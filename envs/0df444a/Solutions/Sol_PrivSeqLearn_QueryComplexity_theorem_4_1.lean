-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:35:48.625869+00:00
-- url     : https://prove2.me/submissions/71c7ccfb-4146-4436-bfd0-24e46865dcb1

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB
import Theorems.Thm_PrivSeqLearn_QueryComplexity_proposition_6_2
import Theorems.Thm_PrivSeqLearn_QueryComplexity_accurate_log_lower
import Theorems.Thm_PrivSeqLearn_QueryComplexity_private_lower_bound

namespace PSLAux
open PrivSeqLearn.QueryComplexity

section General
variable {N : ℕ}

theorem hist_succ (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) (k : ℕ) :
    hist φ x y (k + 1) = hist φ x y k ++ [decide (φ.query (hist φ x y k) y ≤ x)] := rfl

theorem hist_length (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) (k : ℕ) :
    (hist φ x y k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hist_succ]; simp [ih]

theorem hist_getD (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) (k i : ℕ) (d : Bool) (hi : i < k) :
    (hist φ x y k).getD i d = decide (φ.query (hist φ x y i) y ≤ x) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [hist_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hist_length]; exact h), ih h]
    · subst h
      rw [List.getD_append_right _ _ _ _ (by rw [hist_length])]
      simp [hist_length]

theorem hist_drop_succ (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) (n k : ℕ) :
    (hist φ x y (n + k + 1)).drop n =
      (hist φ x y (n + k)).drop n ++ [decide (φ.query (hist φ x y (n + k)) y ≤ x)] := by
  rw [hist_succ, List.drop_append_of_le_length (by rw [hist_length]; omega)]

end General

theorem find?_congr' {α : Type} (p q : α → Bool) (l : List α) (h : ∀ a ∈ l, p a = q a) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

theorem bisect_append (lo hi : ℝ) (l : List Bool) (b : Bool) :
    bisect lo hi (l ++ [b]) =
      if b then (midpt (bisect lo hi l), (bisect lo hi l).2)
      else ((bisect lo hi l).1, midpt (bisect lo hi l)) := by
  induction l generalizing lo hi with
  | nil => cases b <;> simp [bisect, midpt]
  | cons a l ih => cases a <;> simp only [List.cons_append, bisect] <;> exact ih _ _

theorem bisect_props (lo hi : ℝ) (hlh : lo < hi) (l : List Bool) :
    lo ≤ (bisect lo hi l).1 ∧ (bisect lo hi l).1 < (bisect lo hi l).2 ∧ (bisect lo hi l).2 ≤ hi ∧
      (bisect lo hi l).2 - (bisect lo hi l).1 = (hi - lo) / 2 ^ l.length := by
  induction l generalizing lo hi with
  | nil => simp [bisect]; exact hlh
  | cons a l ih =>
    cases a
    · simp only [bisect, Bool.false_eq_true, if_false]
      obtain ⟨h1, h2, h3, h4⟩ := ih lo ((lo + hi) / 2) (by linarith)
      refine ⟨h1, h2, by linarith, ?_⟩
      rw [h4, List.length_cons, pow_succ]; field_simp; ring
    · simp only [bisect, if_true]
      obtain ⟨h1, h2, h3, h4⟩ := ih ((lo + hi) / 2) hi (by linarith)
      refine ⟨by linarith, h2, h3, ?_⟩
      rw [h4, List.length_cons, pow_succ]; field_simp; ring

/-! ## The OB strategy -/

section OB
variable (ϵ : ℝ) (L : ℕ) (hL : 0 < L)

theorem ob_query_phase1 (h : List Bool) (y : Fin (obStrategy ϵ L hL).Ybar) (hh : h.length < L) :
    (obStrategy ϵ L hL).query h y = (h.length : ℝ) / L := by
  simp only [obStrategy, if_pos hh]

theorem ob_query_phase1b (h : List Bool) (y : Fin (obStrategy ϵ L hL).Ybar) (hh1 : L ≤ h.length)
    (hh2 : h.length < 2 * L) :
    (obStrategy ϵ L hL).query h y = ((h.length - L : ℕ) : ℝ) / L + ϵ := by
  simp only [obStrategy, if_neg (show ¬ h.length < L by omega), if_pos hh2]

theorem ob_query_some (h : List Bool) (y : Fin (obStrategy ϵ L hL).Ybar) (hh : 2 * L ≤ h.length)
    (i : ℕ) (hc : caughtGuess L h = some i) :
    (obStrategy ϵ L hL).query h y = midpt (bisect (subLo ϵ L (seedSub y)) (subHi L (seedSub y))
          (seedBits y (h.length - 2 * L))) := by
  simp only [obStrategy, if_neg (show ¬ h.length < L by omega),
    if_neg (show ¬ h.length < 2 * L by omega), hc]

theorem ob_query_none (h : List Bool) (y : Fin (obStrategy ϵ L hL).Ybar) (hh : 2 * L ≤ h.length)
    (hc : caughtGuess L h = none) :
    (obStrategy ϵ L hL).query h y =
      midpt (bisect (subLo ϵ L (jstar L h)) (subHi L (jstar L h)) (h.drop (2 * L))) := by
  simp only [obStrategy, if_neg (show ¬ h.length < L by omega),
    if_neg (show ¬ h.length < 2 * L by omega), hc]

theorem ob_est_some (h : List Bool) (y : Fin (obStrategy ϵ L hL).Ybar) (i : ℕ)
    (hc : caughtGuess L h = some i) :
    (obStrategy ϵ L hL).est h y = (i : ℝ) / L + ϵ / 2 := by
  simp only [obStrategy, hc]

theorem ob_est_none (h : List Bool) (y : Fin (obStrategy ϵ L hL).Ybar)
    (hc : caughtGuess L h = none) :
    (obStrategy ϵ L hL).est h y =
      midpt (bisect (subLo ϵ L (jstar L h)) (subHi L (jstar L h)) (h.drop (2 * L))) := by
  simp only [obStrategy, hc]

/-- Phase 1 responses: entry `i < L` of any history of length `≥ 2L` is `I(x ≥ i/L)`. -/
theorem ob_resp1 (x : ℝ) (y : Fin (obStrategy ϵ L hL).Ybar) (k i : ℕ) (hk : 2 * L ≤ k)
    (hi : i < L) (d : Bool) :
    (hist (obStrategy ϵ L hL) x y k).getD i d = decide ((i : ℝ) / L ≤ x) := by
  rw [hist_getD _ _ _ _ _ _ (by omega), ob_query_phase1 _ _ _ _ _ (by rw [hist_length]; exact hi),
    hist_length]

/-- Phase 1 responses: entry `L + i` (`i < L`) is `I(x ≥ i/L + ϵ)`. -/
theorem ob_resp2 (x : ℝ) (y : Fin (obStrategy ϵ L hL).Ybar) (k i : ℕ) (hk : 2 * L ≤ k)
    (hi : i < L) (d : Bool) :
    (hist (obStrategy ϵ L hL) x y k).getD (L + i) d = decide ((i : ℝ) / L + ϵ ≤ x) := by
  rw [hist_getD _ _ _ _ _ _ (by omega),
    ob_query_phase1b _ _ _ _ _ (by rw [hist_length]; omega) (by rw [hist_length]; omega),
    hist_length, Nat.add_sub_cancel_left]

theorem ob_caught_eq (x : ℝ) (y : Fin (obStrategy ϵ L hL).Ybar) (k : ℕ) (hk : 2 * L ≤ k) :
    caughtGuess L (hist (obStrategy ϵ L hL) x y k) =
      (List.range L).find? (fun i : ℕ => decide ((i : ℝ) / L ≤ x) && !decide ((i : ℝ) / L + ϵ ≤ x)) := by
  unfold caughtGuess
  apply find?_congr'
  intro i hi
  rw [List.mem_range] at hi
  rw [ob_resp1 ϵ L hL x y k i hk hi, ob_resp2 ϵ L hL x y k i hk hi]

theorem ob_jstar_eq (x : ℝ) (y : Fin (obStrategy ϵ L hL).Ybar) (k : ℕ) (hk : 2 * L ≤ k) :
    jstar L (hist (obStrategy ϵ L hL) x y k) =
      ((List.range L).filter (fun i : ℕ => decide ((i : ℝ) / L ≤ x))).length - 1 := by
  unfold jstar
  have : (List.range L).filter (fun i => (hist (obStrategy ϵ L hL) x y k).getD i false) =
      (List.range L).filter (fun i : ℕ => decide ((i : ℝ) / L ≤ x)) :=
    List.filter_congr (fun i hi => by
      rw [List.mem_range] at hi
      exact ob_resp1 ϵ L hL x y k i hk hi false)
  rw [this]

end OB


theorem hist_take {N : ℕ} (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) (k m : ℕ) :
    (hist φ x y (k + m)).take k = hist φ x y k := by
  induction m with
  | zero => rw [Nat.add_zero]; exact List.take_of_length_le (by rw [hist_length])
  | succ m ih =>
    rw [← Nat.add_assoc, hist_succ, List.take_append_of_le_length (by rw [hist_length]; omega), ih]

theorem bisect_append_list (lo hi : ℝ) (l l2 : List Bool) :
    bisect lo hi (l ++ l2) = bisect (bisect lo hi l).1 (bisect lo hi l).2 l2 := by
  induction l generalizing lo hi with
  | nil => rfl
  | cons a l ih => cases a <;> simp only [List.cons_append, bisect] <;> exact ih _ _

theorem midpt_mem (lo hi : ℝ) (hlh : lo < hi) (l : List Bool) :
    lo < midpt (bisect lo hi l) ∧ midpt (bisect lo hi l) < hi := by
  obtain ⟨h1, h2, h3, -⟩ := bisect_props lo hi hlh l
  unfold midpt; constructor <;> linarith

/-- A later bisection midpoint differs from an earlier one. -/
theorem midpt_ne_of_append (lo hi : ℝ) (hlh : lo < hi) (l l2 : List Bool) (hl2 : l2 ≠ []) :
    midpt (bisect lo hi (l ++ l2)) ≠ midpt (bisect lo hi l) := by
  rw [bisect_append_list]
  obtain ⟨-, hJ, -, -⟩ := bisect_props lo hi hlh l
  set J := bisect lo hi l
  obtain ⟨b, l3, rfl⟩ := List.exists_cons_of_ne_nil hl2
  cases b
  · simp only [bisect, Bool.false_eq_true, if_false]
    have := midpt_mem J.1 ((J.1 + J.2) / 2) (by linarith) l3
    unfold midpt at this ⊢; linarith
  · simp only [bisect, if_true]
    have := midpt_mem ((J.1 + J.2) / 2) J.2 (by linarith) l3
    unfold midpt at this ⊢; linarith

theorem midpt_take_ne (lo hi : ℝ) (hlh : lo < hi) (B : List Bool) (t t' : ℕ) (htt : t < t')
    (ht' : t' ≤ B.length) :
    midpt (bisect lo hi (B.take t')) ≠ midpt (bisect lo hi (B.take t)) := by
  have hsplit : B.take t' = B.take t ++ (B.take t').drop t := by
    conv_lhs => rw [← List.take_append_drop t (B.take t')]
    rw [List.take_take, Nat.min_eq_left htt.le]
  rw [hsplit]
  apply midpt_ne_of_append lo hi hlh
  intro h
  have := congrArg List.length h
  simp at this; omega

section OBPhi
variable (ϵ : ℝ) (L : ℕ) (hL : 0 < L)

theorem sub_lt (hϵL : ϵ < 1 / (L : ℝ)) (s : ℕ) : subLo ϵ L s < subHi L s := by
  unfold subLo subHi; rw [add_div]; linarith

theorem sub_unit (hL0 : 0 < L) (hϵ : 0 < ϵ) (s : ℕ) (hs : s < L) : 0 < subLo ϵ L s ∧ subHi L s ≤ 1 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  unfold subLo subHi
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hLr]; exact_mod_cast hs

theorem jstar_lt (hL0 : 0 < L) (h : List Bool) : jstar L h < L := by
  unfold jstar
  have := List.length_filter_le (fun i => h.getD i false) (List.range L)
  simp only [List.length_range] at this; omega

theorem seedSub_lt (y : Fin (L * 2 ^ obM ϵ L)) : seedSub y < L := by
  unfold seedSub; exact (finProdFinEquiv.symm y).1.2

theorem caught_lt (h : List Bool) (i : ℕ) (hc : caughtGuess L h = some i) : i < L := by
  unfold caughtGuess at hc
  exact List.mem_range.1 (List.mem_of_find?_eq_some hc)

/-- Explicit form of the realized queries of the OB strategy: Phase 2 queries are the midpoints of
bisections of a fixed sub-interval `s`, driven by prefixes of a fixed bit list `B` of length `M`. -/
theorem ob_queries_form (x : ℝ) (y : Fin (obStrategy ϵ L hL).Ybar) :
    ∃ s < L, ∃ B : List Bool, B.length = obM ϵ L ∧ ∀ k : ℕ, 2 * L ≤ k → k ≤ 2 * L + obM ϵ L →
      (obStrategy ϵ L hL).query (hist (obStrategy ϵ L hL) x y k) y =
        midpt (bisect (subLo ϵ L s) (subHi L s) (B.take (k - 2 * L))) := by
  have hN : 2 * L ≤ 2 * L + obM ϵ L := by omega
  rcases hc : caughtGuess L (hist (obStrategy ϵ L hL) x y (2 * L + obM ϵ L)) with _ | i
  · refine ⟨jstar L (hist (obStrategy ϵ L hL) x y (2 * L + obM ϵ L)), jstar_lt L hL _,
      (hist (obStrategy ϵ L hL) x y (2 * L + obM ϵ L)).drop (2 * L), by simp [hist_length], ?_⟩
    intro k hk1 hk2
    have hcxk : caughtGuess L (hist (obStrategy ϵ L hL) x y k) = none := by
      rw [ob_caught_eq ϵ L hL x y k hk1, ← ob_caught_eq ϵ L hL x y _ hN]; exact hc
    rw [ob_query_none ϵ L hL _ y (by rw [hist_length]; exact hk1) hcxk,
      ob_jstar_eq ϵ L hL x y k hk1, ← ob_jstar_eq ϵ L hL x y _ hN]
    congr 2
    rw [← List.drop_take]
    have := hist_take (obStrategy ϵ L hL) x y k (2 * L + obM ϵ L - k)
    rw [Nat.add_sub_cancel' hk2] at this
    rw [this]
  · refine ⟨seedSub y, seedSub_lt ϵ L y, seedBits y (obM ϵ L), by simp [seedBits], ?_⟩
    intro k hk1 hk2
    have hcxk : caughtGuess L (hist (obStrategy ϵ L hL) x y k) = some i := by
      rw [ob_caught_eq ϵ L hL x y k hk1, ← ob_caught_eq ϵ L hL x y _ hN]; exact hc
    rw [ob_query_some ϵ L hL _ y (by rw [hist_length]; exact hk1) i hcxk, hist_length]
    congr 2
    unfold seedBits
    rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega)]

theorem ob_inPhi (hϵ : 0 < ϵ) (hϵL : 2 * ϵ < 1 / (L : ℝ)) : InPhi (obStrategy ϵ L hL) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hϵL' : ϵ < 1 / (L : ℝ) := by linarith
  have hϵLm : ϵ * L < 1 / 2 := by
    have := (lt_div_iff₀ hLr).1 hϵL; linarith
  -- values of Phase 1b queries are in [0,1)
  have hp1b : ∀ i : ℕ, i < L → (i : ℝ) / L + ϵ < 1 := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ L := by exact_mod_cast hi
    have : (i : ℝ) / L ≤ 1 - 1 / L := by
      rw [div_le_iff₀ hLr, sub_mul, one_div_mul_cancel hLr.ne']; linarith
    linarith
  have hmid : ∀ s, s < L → ∀ l : List Bool,
      midpt (bisect (subLo ϵ L s) (subHi L s) l) ∈ Set.Ico (0 : ℝ) 1 := by
    intro s hs l
    obtain ⟨h1, h2⟩ := midpt_mem _ _ (sub_lt ϵ L hϵL' s) l
    obtain ⟨h3, h4⟩ := sub_unit ϵ L hL hϵ s hs
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h hh y
    by_cases h1 : h.length < L
    · rw [ob_query_phase1 ϵ L hL h y h1]
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one hLr]; exact_mod_cast h1
    · by_cases h2 : h.length < 2 * L
      · rw [ob_query_phase1b ϵ L hL h y (by omega) h2]
        exact ⟨by positivity, hp1b _ (by omega)⟩
      · rcases hc : caughtGuess L h with _ | i
        · rw [ob_query_none ϵ L hL h y (by omega) hc]; exact hmid _ (jstar_lt L hL h) _
        · rw [ob_query_some ϵ L hL h y (by omega) i hc]; exact hmid _ (seedSub_lt ϵ L y) _
  · intro h hh y
    rcases hc : caughtGuess L h with _ | i
    · rw [ob_est_none ϵ L hL h y hc]; exact hmid _ (jstar_lt L hL h) _
    · rw [ob_est_some ϵ L hL h y i hc]
      have hi := caught_lt L h i hc
      have := hp1b i hi
      exact ⟨by positivity, by linarith⟩
  · intro x hx y
    obtain ⟨s, hs, B, hB, hform⟩ := ob_queries_form ϵ L hL x y
    -- the value of each query
    have hval : ∀ k : ℕ, k < 2 * L + obM ϵ L →
        (k < L ∧ (obStrategy ϵ L hL).query (hist (obStrategy ϵ L hL) x y k) y = (k : ℝ) / L) ∨
        (L ≤ k ∧ k < 2 * L ∧ (obStrategy ϵ L hL).query (hist (obStrategy ϵ L hL) x y k) y =
          ((k - L : ℕ) : ℝ) / L + ϵ) ∨
        (2 * L ≤ k ∧ (obStrategy ϵ L hL).query (hist (obStrategy ϵ L hL) x y k) y =
          midpt (bisect (subLo ϵ L s) (subHi L s) (B.take (k - 2 * L)))) := by
      intro k hk
      by_cases h1 : k < L
      · left; refine ⟨h1, ?_⟩
        rw [ob_query_phase1 ϵ L hL _ y (by rw [hist_length]; exact h1), hist_length]
      · by_cases h2 : k < 2 * L
        · right; left; refine ⟨by omega, h2, ?_⟩
          rw [ob_query_phase1b ϵ L hL _ y (by rw [hist_length]; omega) (by rw [hist_length]; exact h2),
            hist_length]
        · right; right; exact ⟨by omega, hform k (by omega) (by omega)⟩
    -- a Phase 2 value is not a Phase 1 value
    have hP2 : ∀ t : ℕ, ∀ i : ℕ, i < L →
        midpt (bisect (subLo ϵ L s) (subHi L s) (B.take t)) ≠ (i : ℝ) / L ∧
        midpt (bisect (subLo ϵ L s) (subHi L s) (B.take t)) ≠ (i : ℝ) / L + ϵ := by
      intro t i hi
      obtain ⟨h1, h2⟩ := midpt_mem _ _ (sub_lt ϵ L hϵL' s) (B.take t)
      unfold subLo subHi at h1 h2 ⊢
      rcases Nat.lt_or_ge s i with hsi | hsi
      · have : ((s : ℝ) + 1) / L ≤ (i : ℝ) / L := by
          apply div_le_div_of_nonneg_right _ hLr.le; exact_mod_cast hsi
        constructor <;> intro h <;> linarith
      · have : (i : ℝ) / L ≤ (s : ℝ) / L := by
          apply div_le_div_of_nonneg_right _ hLr.le; exact_mod_cast hsi
        constructor <;> intro h <;> linarith
    -- Phase 1a and Phase 1b values differ
    have hAB : ∀ a b : ℕ, (a : ℝ) / L ≠ (b : ℝ) / L + ϵ := by
      intro a b h
      have h' : (a : ℝ) - b = ϵ * L := by
        field_simp at h; linarith
      rcases Nat.lt_or_ge b a with hab | hab
      · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast hab
        nlinarith
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        nlinarith
    intro k k' hkk
    simp only [queries] at hkk
    apply Fin.ext
    rcases hval k k.2 with ⟨hk1, hk⟩ | ⟨hk1, hk2, hk⟩ | ⟨hk1, hk⟩ <;>
    rcases hval k' k'.2 with ⟨hk1', hk'⟩ | ⟨hk1', hk2', hk'⟩ | ⟨hk1', hk'⟩ <;>
    rw [hk, hk'] at hkk
    · rw [div_left_inj' hLr.ne'] at hkk; exact_mod_cast hkk
    · exact absurd hkk (hAB _ _)
    · exact absurd hkk.symm (hP2 _ _ hk1).1
    · exact absurd hkk.symm (hAB _ _)
    · have : ((k - L : ℕ) : ℝ) = ((k' - L : ℕ) : ℝ) := by
        have := add_right_cancel hkk
        rwa [div_left_inj' hLr.ne'] at this
      have : (k : ℕ) - L = (k' : ℕ) - L := by exact_mod_cast this
      omega
    · exact absurd hkk.symm (hP2 _ _ (by omega)).2
    · exact absurd hkk (hP2 _ _ hk1').1
    · exact absurd hkk (hP2 _ _ (by omega)).2
    · by_contra hne
      have hlen : ∀ k'' : Fin (2 * L + obM ϵ L), (k'' : ℕ) - 2 * L ≤ B.length := by
        intro k''; have := k''.2; omega
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact midpt_take_ne _ _ (sub_lt ϵ L hϵL' s) B _ _ (by omega) (hlen k') hkk.symm
      · exact midpt_take_ne _ _ (sub_lt ϵ L hϵL' s) B _ _ (by omega) (hlen k) hkk

end OBPhi

end PSLAux

open PrivSeqLearn.QueryComplexity

theorem solution (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ)) :
    max ⌈Real.logb 2 (1 / ϵ)⌉ (⌈Real.logb 2 (δ / ϵ)⌉ + 2 * (L : ℤ) - 4) ≤ (Nstar ϵ δ L : ℤ) ∧
      (Nstar ϵ δ L : ℤ) ≤ ⌈Real.logb 2 (1 / ((L : ℝ) * ϵ))⌉ + 2 * (L : ℤ) := by
  have hL0 : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hϵL : 2 * ϵ < 1 / (L : ℝ) := lt_of_lt_of_le h2ϵδ hδL
  -- the OB strategy witnesses membership of `2L + M` in the defining set of `N*`
  have hmem : (2 * L + obM ϵ L) ∈ {N : ℕ | ∃ φ : Strategy N, InPhi φ ∧ IsPrivate ϵ δ L φ} :=
    ⟨obStrategy ϵ L hL0, PSLAux.ob_inPhi ϵ L hL0 hϵ hϵL,
      proposition_6_2 ϵ δ L hϵ hδ hL h2ϵδ hδL⟩
  obtain ⟨φ, hφ, hpriv⟩ := Nat.sInf_mem ⟨_, hmem⟩
  have hle : Nstar ϵ δ L ≤ 2 * L + obM ϵ L := Nat.sInf_le hmem
  refine ⟨max_le (accurate_log_lower ϵ φ hϵ hpriv.1)
    (private_lower_bound ϵ δ L hϵ hδ hL h2ϵδ hδL _ φ hφ.1 hpriv), ?_⟩
  -- the upper bound: `M = ⌈log₂ (1/(ϵL))⌉`
  have hϵLm : ϵ * L < 1 := by
    have := (lt_div_iff₀ hLr).1 hϵL; linarith
  have hlog : 0 ≤ Real.logb 2 (1 / (ϵ * L)) := by
    apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ (by positivity)]; linarith
  have hM : ((obM ϵ L : ℕ) : ℤ) = ⌈Real.logb 2 (1 / ((L : ℝ) * ϵ))⌉ := by
    unfold obM; rw [Int.natCast_ceil_eq_ceil hlog, mul_comm]
  have := (Nat.cast_le (α := ℤ)).2 hle
  push_cast at this
  rw [hM] at this
  linarith
