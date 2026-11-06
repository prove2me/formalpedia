-- Prove2me | solution 1 for ProductFraming.Nest.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:48:44.335056+00:00
-- url     : https://prove2.me/submissions/a9e7638c-edf3-45da-9abc-2e4d48bd3647

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Nest_Algorithm
import Definitions.Def_ProductFraming_Nest_Program
import Theorems.Thm_ProductFraming_Nest_theorem_2
import Theorems.Thm_ProductFraming_Nest_proposition_1
import Theorems.Thm_ProductFraming_Nest_lemma_2
import Theorems.Thm_ProductFraming_Nest_gamma_ge_six_div_pi_sq

open Finset ProductFraming.Nest

namespace PFNThm3Aux

lemma U_nonneg {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (x : ℕ) :
    0 ≤ U p r P x := by
  unfold U G
  have hmem : (∅ : Finset (Fin n)) ∈ univ.filter (fun S : Finset (Fin n) => S.card ≤ x * p) := by
    simp
  have := Finset.le_sup' (R r P) hmem
  simpa [R] using this

lemma U_mono {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) {x x' : ℕ}
    (h : x ≤ x') : U p r P x ≤ U p r P x' := by
  unfold U G
  apply Finset.sup'_le
  intro S hS
  apply Finset.le_sup'
  simp only [mem_filter, mem_univ, true_and] at hS ⊢
  exact le_trans hS (Nat.mul_le_mul_right p h)

lemma sum_Icc_split (f : ℕ → ℝ) {x m : ℕ} (h : x ≤ m) :
    ∑ y ∈ Icc x m, f y = f x + ∑ y ∈ Icc (x + 1) m, f y := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, sum_insert]
  simp

lemma tail_succ (m : ℕ) (lam : ℕ → ℝ) {x : ℕ} (h : x ≤ m) :
    tail m lam x = lam x + tail m lam (x + 1) := by
  unfold tail; exact sum_Icc_split lam h

lemma tail_nonneg (m : ℕ) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) {z : ℕ} (hz : 1 ≤ z) :
    0 ≤ tail m lam z := by
  unfold tail
  apply sum_nonneg
  intro y hy
  rw [mem_Icc] at hy
  exact hlam.1 y (mem_Icc.mpr ⟨by omega, hy.2⟩)

lemma tail_anti (m : ℕ) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) {z w : ℕ} (hz : 1 ≤ z)
    (hzw : z ≤ w) : tail m lam w ≤ tail m lam z := by
  unfold tail
  apply sum_le_sum_of_subset_of_nonneg
  · intro y hy; rw [mem_Icc] at hy ⊢; omega
  · intro y hy _
    rw [mem_Icc] at hy
    exact hlam.1 y (mem_Icc.mpr ⟨by omega, hy.2⟩)

lemma tail_one (m : ℕ) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) : tail m lam 1 = 1 := hlam.2

lemma lamOf_tail (m : ℕ) (lam : ℕ → ℝ) {x : ℕ} (hx : x ∈ Icc 1 m) :
    lamOf m (tail m lam) x = lam x := by
  rw [mem_Icc] at hx
  unfold lamOf
  split_ifs with h
  · rw [tail_succ m lam hx.2]; ring
  · have : x = m := by omega
    subst this
    unfold tail
    simp

lemma Emin_succ_sub (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) :
    Emin m lam ((x + 1 : ℕ) : ℝ) = Emin m lam (x : ℝ) + tail m lam (x + 1) := by
  unfold Emin tail
  have hfil : (Icc 1 m).filter (fun y => x + 1 ≤ y) = Icc (x + 1) m := by
    ext y; simp only [mem_filter, mem_Icc]; omega
  rw [← hfil, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  split_ifs with h
  · have h1 : ((x + 1 : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h
    have h2 : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : x ≤ y)
    rw [min_eq_right h1, min_eq_right h2]; push_cast; ring
  · have h1 : (y : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : y ≤ x + 1)
    have h2 : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : y ≤ x)
    rw [min_eq_left h1, min_eq_left h2]; ring

lemma EminTail_tail (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) :
    EminTail (tail m lam) x = Emin m lam (x : ℝ) := by
  induction x with
  | zero =>
    unfold EminTail Emin
    simp
  | succ k ih =>
    unfold EminTail at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih, Emin_succ_sub]

lemma A_eq_B (m : ℕ) (lam : ℕ → ℝ) :
    ∀ d x, x + d = m + 1 →
      ∑ y ∈ Icc x m, lam y * ((y : ℝ) - x + 1) = ∑ z ∈ Icc x m, tail m lam z := by
  intro d
  induction d with
  | zero =>
    intro x hx
    have : Icc x m = ∅ := by ext y; simp; omega
    simp [this]
  | succ d ih =>
    intro x hx
    have hxm : x ≤ m := by omega
    have ih' := ih (x + 1) (by omega)
    rw [sum_Icc_split _ hxm, sum_Icc_split _ hxm, ← ih', tail_succ m lam hxm]
    unfold tail
    rw [show lam x * ((x : ℝ) - x + 1) = lam x by ring, add_assoc, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl; intro i _; push_cast; ring

lemma q_eq (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) :
    q m lam x = (∑ z ∈ Icc x m, tail m lam z) / tail m lam x := by
  unfold q
  by_cases hx : x ≤ m + 1
  · rw [A_eq_B m lam (m + 1 - x) x (by omega)]
  · have : Icc x m = ∅ := by ext y; simp; omega
    simp [this]

lemma feasible6_tail (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam)
    (hA3 : IsNBUE m lam) : Feasible6 m (tail m lam) := by
  refine ⟨tail_one m lam hlam, ?_, ?_, ?_⟩
  · intro x hx _
    exact tail_anti m lam hlam hx (by omega)
  · exact tail_nonneg m lam hlam hm
  · intro x hx hxm
    have hq := hA3 (x + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [q_eq, q_eq, tail_one m lam hlam, div_one] at hq
    have hpos := tail_nonneg m lam hlam (z := x + 1) (by omega)
    rcases hpos.lt_or_eq with hlt | heq
    · rw [div_le_iff₀ hlt] at hq
      linarith
    · have hzero : ∑ z ∈ Icc (x + 1) m, tail m lam z = 0 := by
        apply sum_eq_zero
        intro z hz
        rw [mem_Icc] at hz
        have h1 := tail_anti m lam hlam (z := x + 1) (w := z) (by omega) hz.1
        have h2 := tail_nonneg m lam hlam (z := z) (by omega)
        linarith
      rw [hzero, ← heq]; simp

lemma Emin_nonneg (m : ℕ) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Emin m lam x := by
  unfold Emin
  apply sum_nonneg
  intro y hy
  exact mul_nonneg (hlam.1 y hy) (le_min (Nat.cast_nonneg y) hx)

end PFNThm3Aux

open PFNThm3Aux in
theorem solution (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P)
    (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    (runs : ℕ → ℕ → Finset (Fin n)) (hruns : ∀ y ∈ Icc 1 m, IsNestRun p r P y (runs y)) :
    6 / Real.pi ^ 2 * Vopt n m p r P lam ≤ VNEST hm r P lam runs := by
  have hT2 := theorem_2 n m p hm hp r P hP lam hlam
  have hP1 := proposition_1 n m p hm hp r P hP lam hlam
  have hL2 := lemma_2 n m p hm hp r hr P hP hA1
  set c := ∑ x ∈ Icc 1 m, lam x * U p r P x with hc
  have hpi : 0 < 6 / Real.pi ^ 2 := by positivity
  -- each `V^{NEST(y)}` is bounded by `V^{NEST}`
  have hVy : ∀ y ∈ Icc 1 m, U p r P y / (y : ℝ) * Emin m lam (y : ℝ) ≤ VNEST hm r P lam runs := by
    intro y hy
    refine le_trans (hP1 y hy (runs y) (hruns y hy)) ?_
    unfold VNEST
    exact Finset.le_sup' (fun y => VNest m r P lam y (runs y)) hy
  have hc0 : 0 ≤ c := by
    apply sum_nonneg; intro x hx; exact mul_nonneg (hlam.1 x hx) (U_nonneg p r P x)
  rcases hc0.lt_or_eq with hcpos | hczero
  · -- normalise: `U' = U / c` is feasible for (5) with `Λ = tail`
    have hfeas : Feasible5 m (fun x => U p r P x / c) (tail m lam) := by
      refine ⟨feasible6_tail m hm lam hlam hA3, ?_, ?_, ?_, ?_⟩
      · intro x _ _
        exact div_le_div_of_nonneg_right (U_mono p r P (by omega)) hcpos.le
      · intro x hx hxm
        have := hL2 x (mem_Icc.mpr ⟨hx, by omega⟩) (x + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
          (by omega)
        push_cast at this
        rw [div_div, div_div, mul_comm c, mul_comm c, ← div_div, ← div_div]
        exact div_le_div_of_nonneg_right this hcpos.le
      · calc ∑ x ∈ Icc 1 m, lamOf m (tail m lam) x * (fun x => U p r P x / c) x
            = ∑ x ∈ Icc 1 m, lam x * U p r P x / c := by
              apply sum_congr rfl; intro x hx; rw [lamOf_tail m lam hx]; ring
          _ = c / c := by rw [← sum_div]
          _ = 1 := div_self hcpos.ne'
      · intro x _
        exact div_nonneg (U_nonneg p r P x) hcpos.le
    have hg := gamma_ge_six_div_pi_sq m hm _ _ hfeas
    unfold J5 at hg
    obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_sup' ⟨1, mem_Icc.mpr ⟨le_refl 1, hm⟩⟩
      (fun x => (fun x => U p r P x / c) x / (x : ℝ) * EminTail (tail m lam) x)
    rw [hxeq, EminTail_tail] at hg
    have hkey : 6 / Real.pi ^ 2 * c ≤ VNEST hm r P lam runs := by
      have h1 : U p r P x / c / (x : ℝ) * Emin m lam (x : ℝ)
          = (U p r P x / (x : ℝ) * Emin m lam (x : ℝ)) / c := by ring
      rw [h1, le_div_iff₀ hcpos] at hg
      exact le_trans hg (hVy x hx)
    calc 6 / Real.pi ^ 2 * Vopt n m p r P lam ≤ 6 / Real.pi ^ 2 * c :=
          mul_le_mul_of_nonneg_left hT2 hpi.le
      _ ≤ _ := hkey
  · have h1 : 6 / Real.pi ^ 2 * Vopt n m p r P lam ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hpi.le
      rw [hczero]; exact hT2
    have hm1 : 1 ∈ Icc 1 m := mem_Icc.mpr ⟨le_refl 1, hm⟩
    have h2 : 0 ≤ U p r P 1 / ((1 : ℕ) : ℝ) * Emin m lam ((1 : ℕ) : ℝ) :=
      mul_nonneg (div_nonneg (U_nonneg p r P 1) (Nat.cast_nonneg 1))
        (Emin_nonneg m lam hlam (Nat.cast_nonneg 1))
    linarith [hVy 1 hm1]
