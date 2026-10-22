-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.ob_accurate
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:26:45.977119+00:00
-- url     : https://prove2.me/submissions/ca4df54f-582d-43f7-8f9c-656ef0850c86

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


theorem filter_range_le_length (p : ℕ → Bool) (j : ℕ) (hp : ∀ i, p i = true ↔ i ≤ j) (n : ℕ) :
    ((List.range n).filter p).length = min n (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases hn : n ≤ j
    · have : p n = true := (hp n).2 hn
      simp [this]; omega
    · have : p n = false := by
        cases h : p n
        · rfl
        · exact absurd ((hp n).1 h) hn
      simp [this]; omega

theorem two_pow_obM (ϵ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hL : 0 < L) :
    1 / (ϵ * L) ≤ (2 : ℝ) ^ obM ϵ L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hpos : 0 < 1 / (ϵ * L) := by positivity
  have h1 : Real.logb 2 (1 / (ϵ * L)) ≤ (obM ϵ L : ℝ) := Nat.le_ceil _
  calc 1 / (ϵ * L) = (2 : ℝ) ^ Real.logb 2 (1 / (ϵ * L)) := (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
    _ ≤ (2 : ℝ) ^ (obM ϵ L : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = (2 : ℝ) ^ obM ϵ L := Real.rpow_natCast _ _

/-- The sub-interval index when nobody caught `x`: `jstar = ⌊x L⌋`. -/
theorem ob_filter_len (L : ℕ) (hL : 0 < L) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ((List.range L).filter (fun i : ℕ => decide ((i : ℝ) / L ≤ x))).length - 1 = ⌊x * L⌋₊ := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hxL : 0 ≤ x * L := mul_nonneg hx.1 hLr.le
  have hlt : ⌊x * L⌋₊ < L := by
    rw [Nat.floor_lt hxL]; nlinarith [hx.2]
  rw [filter_range_le_length _ ⌊x * L⌋₊ (fun i => by
    rw [decide_eq_true_iff, Nat.le_floor_iff hxL, div_le_iff₀ hLr])]
  omega

/-- Truthful bisection invariant: when no guess caught `x`, every Phase 2 interval contains `x`. -/
theorem ob_truthful (ϵ : ℝ) (L : ℕ) (hL : 0 < L) (x : ℝ) (y : Fin (obStrategy ϵ L hL).Ybar)
    (hc : (List.range L).find? (fun i : ℕ => decide ((i : ℝ) / L ≤ x) && !decide ((i : ℝ) / L + ϵ ≤ x)) = none)
    (j : ℕ) (hj : ((List.range L).filter (fun i : ℕ => decide ((i : ℝ) / L ≤ x))).length - 1 = j)
    (hlo : subLo ϵ L j ≤ x) (hhi : x < subHi L j) (k : ℕ) :
    (bisect (subLo ϵ L j) (subHi L j) ((hist (obStrategy ϵ L hL) x y (2 * L + k)).drop (2 * L))).1 ≤ x ∧
    x < (bisect (subLo ϵ L j) (subHi L j) ((hist (obStrategy ϵ L hL) x y (2 * L + k)).drop (2 * L))).2 := by
  induction k with
  | zero =>
    rw [Nat.add_zero, List.drop_eq_nil_of_le (by rw [hist_length])]
    exact ⟨hlo, hhi⟩
  | succ k ih =>
    rw [← Nat.add_assoc, hist_drop_succ]
    have hk : 2 * L ≤ (hist (obStrategy ϵ L hL) x y (2 * L + k)).length := by rw [hist_length]; omega
    rw [ob_query_none ϵ L hL _ y hk (by rw [ob_caught_eq ϵ L hL x y _ (by omega)]; exact hc),
      ob_jstar_eq ϵ L hL x y _ (by omega), hj, bisect_append]
    set J := bisect (subLo ϵ L j) (subHi L j) ((hist (obStrategy ϵ L hL) x y (2 * L + k)).drop (2 * L))
    by_cases hm : midpt J ≤ x
    · simp [hm, ih.2]
    · simp [hm, ih.1, lt_of_not_ge hm]

theorem ob_accurate_aux (ϵ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hL : 2 ≤ L) (_hϵL : 2 * ϵ < 1 / (L : ℝ)) :
    IsAccurate ϵ (obStrategy ϵ L (by omega)) := by
  have hL0 : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  intro x hx y
  unfold estimate
  have hN : 2 * L ≤ 2 * L + obM ϵ L := by omega
  have hceq := ob_caught_eq ϵ L hL0 x y _ hN
  rcases hc : caughtGuess L (hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)) with _ | i
  · -- Case 2: no guess caught `x`
    rw [ob_est_none ϵ L hL0 _ y hc, ob_jstar_eq ϵ L hL0 x y _ hN, ob_filter_len L hL0 x hx]
    rw [hc] at hceq
    have hnone := List.find?_eq_none.1 hceq.symm
    set j := ⌊x * L⌋₊ with hjdef
    have hxL : 0 ≤ x * L := mul_nonneg hx.1 hLr.le
    have hj1 : (j : ℝ) / L ≤ x := by
      rw [div_le_iff₀ hLr]; exact Nat.floor_le hxL
    have hj2 : x < ((j : ℝ) + 1) / L := by
      rw [lt_div_iff₀ hLr]; exact Nat.lt_floor_add_one _
    have hjL : j < L := by
      rw [hjdef, Nat.floor_lt hxL]; nlinarith [hx.2]
    have hlo : subLo ϵ L j ≤ x := by
      have := hnone j (List.mem_range.2 hjL)
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
        not_and, not_not] at this
      exact this hj1
    have hinv := ob_truthful ϵ L hL0 x y hceq.symm j (ob_filter_len L hL0 x hx) hlo hj2 (obM ϵ L)
    have hlh : subLo ϵ L j < subHi L j := lt_of_le_of_lt hlo hj2
    obtain ⟨-, -, -, hlen⟩ := bisect_props _ _ hlh
      ((hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)).drop (2 * L))
    rw [List.length_drop, hist_length, Nat.add_sub_cancel_left] at hlen
    set J := bisect (subLo ϵ L j) (subHi L j) ((hist (obStrategy ϵ L hL0) x y (2 * L + obM ϵ L)).drop (2 * L))
    have hpow := two_pow_obM ϵ L hϵ hL0
    have h2pos : (0 : ℝ) < 2 ^ obM ϵ L := by positivity
    have hwidth : subHi L j - subLo ϵ L j ≤ 1 / L := by
      unfold subHi subLo; rw [add_div]; linarith
    have hsmall : (subHi L j - subLo ϵ L j) / 2 ^ obM ϵ L ≤ ϵ := by
      rw [div_le_iff₀ h2pos]
      have : 1 / (L : ℝ) ≤ ϵ * 2 ^ obM ϵ L := by
        have h' : 1 / (ϵ * L) * (ϵ : ℝ) = 1 / L := by field_simp
        calc 1 / (L : ℝ) = 1 / (ϵ * L) * ϵ := h'.symm
          _ ≤ 2 ^ obM ϵ L * ϵ := mul_le_mul_of_nonneg_right hpow hϵ.le
          _ = ϵ * 2 ^ obM ϵ L := mul_comm _ _
      linarith
    unfold midpt
    rw [abs_le]
    constructor <;> linarith [hinv.1, hinv.2]
  · -- Case 1: guess `i` caught `x`
    rw [ob_est_some ϵ L hL0 _ y i hc]
    rw [hc] at hceq
    have hp := List.find?_some hceq.symm
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      not_le] at hp
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2]

end PSLAux

open PrivSeqLearn.QueryComplexity

theorem solution (ϵ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hL : 2 ≤ L) (hϵL : 2 * ϵ < 1 / (L : ℝ)) :
    IsAccurate ϵ (obStrategy ϵ L (by omega)) :=
  PSLAux.ob_accurate_aux ϵ L hϵ hL hϵL
