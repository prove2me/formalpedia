-- Prove2me | solution 1 for SuttonTD.Convergence.varga_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:52:27.50587+00:00
-- url     : https://prove2.me/submissions/68bda9d1-bc97-49d9-aefd-4804876209cb

import Mathlib
import Definitions.Def_SuttonTD_Convergence_IsPosDefReal
import Definitions.Def_SuttonTD_Convergence_StrictlyDiagDominant

set_option autoImplicit false

open SuttonTD.Convergence Matrix in
theorem varga_aux {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hsymm : A.IsSymm) (y : n → ℝ) :
    ∑ i, y i ^ 2 * (A i i - ∑ j ∈ Finset.univ.erase i, |A i j|) ≤ y ⬝ᵥ (A *ᵥ y) := by
  have hs : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hsymm i) j
    simpa [Matrix.transpose_apply] using this
  -- full-sum forms
  have key : ∀ i, y i * ∑ j, A i j * y j ≥
      A i i * y i ^ 2 - ∑ j ∈ Finset.univ.erase i, |A i j| * (y i ^ 2 + y j ^ 2) / 2 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), mul_add, Finset.mul_sum]
    have : ∀ j ∈ Finset.univ.erase i, -( |A i j| * (y i ^ 2 + y j ^ 2) / 2) ≤ y i * (A i j * y j) := by
      intro j _
      have h1 : -( |A i j| * (y i ^ 2 + y j ^ 2) / 2) ≤ A i j * (y i * y j) := by
        have h2 : |A i j * (y i * y j)| ≤ |A i j| * (y i ^ 2 + y j ^ 2) / 2 := by
          rw [abs_mul]
          have h3 : |y i * y j| ≤ (y i ^ 2 + y j ^ 2) / 2 := by
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y i + y j), sq_nonneg (y i - y j)]
          have := mul_le_mul_of_nonneg_left h3 (abs_nonneg (A i j))
          linarith
        linarith [neg_abs_le (A i j * (y i * y j))]
      linarith [show y i * (A i j * y j) = A i j * (y i * y j) by ring]
    have hsum := Finset.sum_le_sum this
    rw [Finset.sum_neg_distrib] at hsum
    nlinarith [hsum]
  have hdot : y ⬝ᵥ (A *ᵥ y) = ∑ i, y i * ∑ j, A i j * y j := by
    simp [dotProduct, Matrix.mulVec]
  rw [hdot]
  have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  refine le_trans ?_ hle
  -- compare the bounds
  have hS2 : ∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * y j ^ 2
      = ∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * y i ^ 2 := by
    have e1 : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| * y j ^ 2
        = ∑ j, |A i j| * y j ^ 2 - |A i i| * y i ^ 2 :=
      fun i => by rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have e2 : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| * y i ^ 2
        = ∑ j, |A i j| * y i ^ 2 - |A i i| * y i ^ 2 :=
      fun i => by rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [e1, e2, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hs]
  have expand : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| * (y i ^ 2 + y j ^ 2) / 2
      = (∑ j ∈ Finset.univ.erase i, |A i j| * y i ^ 2) / 2
        + (∑ j ∈ Finset.univ.erase i, |A i j| * y j ^ 2) / 2 := by
    intro i
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  simp only [Finset.sum_sub_distrib, expand, Finset.sum_add_distrib, ← Finset.sum_div, hS2]
  have : ∀ i, y i ^ 2 * (A i i - ∑ j ∈ Finset.univ.erase i, |A i j|)
      = A i i * y i ^ 2 - ∑ j ∈ Finset.univ.erase i, |A i j| * y i ^ 2 := by
    intro i; rw [← Finset.sum_mul]; ring
  simp only [this, Finset.sum_sub_distrib]
  linarith

open SuttonTD.Convergence Matrix in
theorem solution {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hsymm : A.IsSymm) (hdom : StrictlyDiagDominant A) (hdiag : ∀ i, 0 < A i i) :
    IsPosDefReal A := by
  intro y hy
  refine lt_of_lt_of_le ?_ (varga_aux A hsymm y)
  obtain ⟨k, hk⟩ : ∃ k, y k ≠ 0 := by
    by_contra h
    exact hy (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have hpos : ∀ i, 0 < A i i - ∑ j ∈ Finset.univ.erase i, |A i j| := by
    intro i
    have := hdom i
    rw [abs_of_pos (hdiag i)] at this
    linarith
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (sq_nonneg _) (hpos i).le
  · exact ⟨k, Finset.mem_univ k, mul_pos (by positivity) (hpos k)⟩
