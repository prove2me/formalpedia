-- Prove2me | solution 1 for VdNSim.Sparse.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:00:27.31999+00:00
-- url     : https://prove2.me/submissions/270a1e41-cbc2-4481-ba0c-f494f0fefdd5

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace Aux_VdNc2
open VdNSim.Sparse
open scoped Matrix.Norms.L2Operator

lemma entry_eq {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (x y : X) (j : Fin s)
    (hj : D.r j x = y) (hα : D.α j x ≠ 0) : A y x = D.α j x := by
  rw [D.eq2]
  apply Finset.sum_eq_single_of_mem j
  · simp [hj]
  · intro i hi hij
    have hri : D.r i x = y := (Finset.mem_filter.mp hi).2
    by_contra h
    exact hij (D.inj x i j h hα (by rw [hri, hj]))

lemma entry_le {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ) (y x : X) :
    ‖A y x‖ ≤ QAlgorithms.specNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single x 1)
  have he : ‖(EuclideanSpace.single x (1 : ℂ) : EuclideanSpace ℂ X)‖ = 1 := by simp
  rw [he, mul_one] at h
  have hc : ((EuclideanSpace.equiv X ℂ).symm (A.mulVec (WithLp.ofLp (EuclideanSpace.single x (1 : ℂ))))) y
      = A y x := by simp
  calc ‖A y x‖ = ‖((EuclideanSpace.equiv X ℂ).symm
        (A.mulVec (WithLp.ofLp (EuclideanSpace.single x (1 : ℂ))))) y‖ := by rw [hc]
    _ ≤ ‖(EuclideanSpace.equiv X ℂ).symm (A.mulVec (WithLp.ofLp (EuclideanSpace.single x (1 : ℂ))))‖ :=
        PiLp.norm_apply_le _ _
    _ ≤ ‖A‖ := h
    _ = QAlgorithms.specNorm A := rfl

end Aux_VdNc2

open VdNSim.Sparse Aux_VdNc2 in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (hsp : IsSparse s A)
    (hA : QAlgorithms.specNorm A ≤ 1)
    (D : ColumnData A s) (ψ ϕ : X → ℂ) (i : Fin s) (y : X) :
    ‖G ψ ϕ D i y‖ ≤ (s : ℝ) := by
  unfold G
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 ?_) ?_
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    obtain ⟨hr, hα0⟩ := hx'
    have hα : ‖D.α i x‖ ≤ 1 := by
      rw [← entry_eq D x y i hr hα0]
      exact (entry_le A _ _).trans hA
    split_ifs with hp
    · unfold prob at hp ⊢
      have hab : ‖ψ x‖ < ‖ϕ y‖ :=
        (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hp
      have hbpos : 0 < ‖ϕ y‖ := lt_of_le_of_lt (norm_nonneg _) hab
      have hn : ‖((‖ϕ y‖ ^ 2 : ℝ) : ℂ)‖ = ‖ϕ y‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [norm_mul, norm_div, norm_mul, norm_star, hn]
      have h1 : ‖ϕ y‖ * ‖ψ x‖ / ‖ϕ y‖ ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [norm_nonneg (ψ x)]
      exact mul_le_one₀ h1 (norm_nonneg _) hα
    · rw [norm_zero]; exact zero_le_one
  · rw [nsmul_eq_mul, mul_one]
    exact_mod_cast le_trans (Finset.card_le_card (fun x hx => by
      obtain ⟨hr, hα0⟩ := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [entry_eq D x y i hr hα0]
      exact hα0)) (hsp.2 y)
