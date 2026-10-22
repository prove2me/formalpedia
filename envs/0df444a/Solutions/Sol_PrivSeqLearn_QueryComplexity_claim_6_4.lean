-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.claim_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:28:59.149227+00:00
-- url     : https://prove2.me/submissions/5e31afd7-c6e0-49c8-8658-519674f37a61

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB

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


theorem exists_bits (M : ℕ) (r : Fin M → Bool) :
    ∃ z : Fin (2 ^ M), ∀ t : Fin M, Nat.testBit z t = r t := by
  have hinj : Function.Injective (fun z : Fin (2 ^ M) => fun t : Fin M => Nat.testBit z t) := by
    intro a b hab
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < M
    · exact congrFun hab ⟨i, hi⟩
    · have hle : 2 ^ M ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le a.2 hle),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.2 hle)]
  have hbij : Function.Bijective (fun z : Fin (2 ^ M) => fun t : Fin M => Nat.testBit z t) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp⟩
  obtain ⟨z, hz⟩ := hbij.2 r
  exact ⟨z, fun t => congrFun hz t⟩

theorem ob_query_phase1_eq (ϵ : ℝ) (L : ℕ) (hL : 0 < L) (h h' : List Bool)
    (y y' : Fin (obStrategy ϵ L hL).Ybar) (hlen : h.length = h'.length) (hlt : h.length < 2 * L) :
    (obStrategy ϵ L hL).query h y = (obStrategy ϵ L hL).query h' y' := by
  by_cases h1 : h.length < L
  · rw [ob_query_phase1 ϵ L hL h y h1, ob_query_phase1 ϵ L hL h' y' (hlen ▸ h1), hlen]
  · rw [ob_query_phase1b ϵ L hL h y (by omega) hlt,
      ob_query_phase1b ϵ L hL h' y' (by omega) (hlen ▸ hlt), hlen]

theorem ob_caught_some (ϵ : ℝ) (L : ℕ) (hL : 0 < L) (x' : ℝ) (y' : Fin (obStrategy ϵ L hL).Ybar)
    (k : ℕ) (hk : 2 * L ≤ k) (i : ℕ) (hi : i < L) (h1 : (i : ℝ) / L ≤ x') (h2 : x' < (i : ℝ) / L + ϵ) :
    ∃ i', caughtGuess L (hist (obStrategy ϵ L hL) x' y' k) = some i' := by
  rw [ob_caught_eq ϵ L hL x' y' k hk]
  cases hf : (List.range L).find?
      (fun i : ℕ => decide ((i : ℝ) / L ≤ x') && !decide ((i : ℝ) / L + ϵ ≤ x')) with
  | some i' => exact ⟨i', rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.1 hf i (List.mem_range.2 hi)
    simp [h1, h2] at this

theorem ob_seedBits_eq (ϵ : ℝ) (L : ℕ) (hL : 0 < L) (x : ℝ) (y y' : Fin (obStrategy ϵ L hL).Ybar)
    (hz : ∀ s, s < obM ϵ L → Nat.testBit (finProdFinEquiv.symm y').2 s =
      decide ((obStrategy ϵ L hL).query (hist (obStrategy ϵ L hL) x y (2 * L + s)) y ≤ x))
    (t : ℕ) (ht : t ≤ obM ϵ L) :
    seedBits y' t = (hist (obStrategy ϵ L hL) x y (2 * L + t)).drop (2 * L) := by
  induction t with
  | zero =>
    rw [Nat.add_zero, List.drop_eq_nil_of_le (by rw [hist_length])]
    rfl
  | succ t ih =>
    rw [← Nat.add_assoc, hist_drop_succ, ← ih (by omega), ← hz t (by omega)]
    unfold seedBits
    rw [List.range_succ, List.map_append]
    rfl

theorem claim_6_4_aux (ϵ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hL : 2 ≤ L) (hϵL : 2 * ϵ < 1 / (L : ℝ)) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ q ∈ Qset (obStrategy ϵ L (by omega)) x,
      guessUnion ϵ L ⊆ infoSet (obStrategy ϵ L (by omega)) q := by
  have hL0 : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  intro x hx q hq x' hx'
  obtain ⟨y, rfl⟩ := hq
  obtain ⟨i', hi'⟩ := Set.mem_iUnion.1 hx'
  have hi'L : ((i' : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast i'.2
  have hx'01 : x' ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨le_trans (by positivity) hi'.1, ?_⟩
    have h1 : ((i' : ℕ) : ℝ) / L ≤ 1 - 1 / L := by
      rw [div_le_iff₀ hLr, sub_mul, one_div_mul_cancel hLr.ne']; linarith
    linarith [hi'.2]
  refine ⟨hx'01, ?_⟩
  have hN : 2 * L ≤ 2 * L + obM ϵ L := by omega
  have hcx' : ∀ k, 2 * L ≤ k → ∀ y' : Fin (obStrategy ϵ L hL0).Ybar,
      ∃ i'', caughtGuess L (hist (obStrategy ϵ L hL0) x' y' k) = some i'' :=
    fun k hk y' => ob_caught_some ϵ L hL0 x' y' k hk i' i'.2 hi'.1 hi'.2
  rcases hc : caughtGuess L (hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)) with _ | i
  · -- x was not caught: the fictitious search of x' imitates the truthful search of x
    set j := jstar L (hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)) with hjdef
    have hjL : j < L := by
      have : ((List.range L).filter
          (fun i => (hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)).getD i false)).length ≤ L := by
        have := List.length_filter_le
          (fun i => (hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)).getD i false) (List.range L)
        simpa using this
      simp only [hjdef, jstar]; omega
    obtain ⟨z, hz⟩ := exists_bits (obM ϵ L)
      (fun t => (hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)).getD (2 * L + t) false)
    let y' : Fin (obStrategy ϵ L hL0).Ybar := finProdFinEquiv (⟨j, hjL⟩, z)
    have hsub : seedSub y' = j := by simp [y', seedSub]
    have hz' : ∀ s, s < obM ϵ L → Nat.testBit (finProdFinEquiv.symm y').2 s =
        decide ((obStrategy ϵ L hL0).query (hist (obStrategy ϵ L hL0) x y (2 * L + s)) y ≤ x) := by
      intro s hs
      have := hz ⟨s, hs⟩
      simp only [y', Equiv.symm_apply_apply] at this ⊢
      rw [this, hist_getD _ _ _ _ _ _ (by omega)]
    refine ⟨y', ?_⟩
    funext k
    unfold queries
    by_cases hk : (k : ℕ) < 2 * L
    · exact ob_query_phase1_eq ϵ L hL0 _ _ y' y (by rw [hist_length, hist_length])
        (by rw [hist_length]; exact hk)
    · rw [not_lt] at hk
      obtain ⟨i'', hi''⟩ := hcx' k hk y'
      have hcxk : caughtGuess L (hist (obStrategy ϵ L hL0) x y k) = none := by
        rw [ob_caught_eq ϵ L hL0 x y k hk, ← ob_caught_eq ϵ L hL0 x y _ hN]; exact hc
      rw [ob_query_some ϵ L hL0 _ y' (by rw [hist_length]; exact hk) i'' hi'',
        ob_query_none ϵ L hL0 _ y (by rw [hist_length]; exact hk) hcxk,
        ob_jstar_eq ϵ L hL0 x y k hk, ← ob_jstar_eq ϵ L hL0 x y _ hN, ← hjdef, hsub, hist_length]
      obtain ⟨t, ht⟩ : ∃ t, (k : ℕ) = 2 * L + t := ⟨k - 2 * L, by omega⟩
      have htM : t ≤ obM ϵ L := by have := k.2; omega
      rw [ht, Nat.add_sub_cancel_left, ob_seedBits_eq ϵ L hL0 x y y' hz' t htM]
  · -- x was caught: the same seed produces the same queries for x'
    refine ⟨y, ?_⟩
    funext k
    unfold queries
    by_cases hk : (k : ℕ) < 2 * L
    · exact ob_query_phase1_eq ϵ L hL0 _ _ y y (by rw [hist_length, hist_length])
        (by rw [hist_length]; exact hk)
    · rw [not_lt] at hk
      obtain ⟨i'', hi''⟩ := hcx' k hk y
      have hcxk : caughtGuess L (hist (obStrategy ϵ L hL0) x y k) = some i := by
        rw [ob_caught_eq ϵ L hL0 x y k hk, ← ob_caught_eq ϵ L hL0 x y _ hN]; exact hc
      rw [ob_query_some ϵ L hL0 _ y (by rw [hist_length]; exact hk) i'' hi'',
        ob_query_some ϵ L hL0 _ y (by rw [hist_length]; exact hk) i hcxk, hist_length, hist_length]

end PSLAux

open PrivSeqLearn.QueryComplexity

theorem solution (ϵ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hL : 2 ≤ L) (hϵL : 2 * ϵ < 1 / (L : ℝ)) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ q ∈ Qset (obStrategy ϵ L (by omega)) x,
      guessUnion ϵ L ⊆ infoSet (obStrategy ϵ L (by omega)) q :=
  PSLAux.claim_6_4_aux ϵ L hϵ hL hϵL
