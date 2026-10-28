-- Prove2me | solution 1 for VdNSim.Sparse.F_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:03:10.122649+00:00
-- url     : https://prove2.me/submissions/5b50170d-bd27-46ec-a364-92597a5cef85

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace Aux_VdNF
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

end Aux_VdNF

open VdNSim.Sparse in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (hA : QAlgorithms.specNorm A ≤ 1)
    (D : ColumnData A s) (ψ ϕ : X → ℂ) (i : Fin s) (x : X) :
    ‖F ψ ϕ D i x‖ ≤ 1 := by
  have hα : ‖D.α i x‖ ≤ 1 := by
    by_cases h0 : D.α i x = 0
    · rw [h0, norm_zero]; exact zero_le_one
    · rw [← Aux_VdNF.entry_eq D x (D.r i x) i rfl h0]
      exact (Aux_VdNF.entry_le A _ _).trans hA
  unfold F
  split_ifs with hp
  · unfold prob at hp ⊢
    have hab : ‖ϕ (D.r i x)‖ ≤ ‖ψ x‖ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hp
    have hn : ‖((‖ψ x‖ ^ 2 : ℝ) : ℂ)‖ = ‖ψ x‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [norm_mul, norm_div, norm_mul, norm_star, hn]
    by_cases hb : ‖ψ x‖ = 0
    · rw [hb]; simp
    · have hbpos : 0 < ‖ψ x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb)
      have h1 : ‖ϕ (D.r i x)‖ * ‖ψ x‖ / ‖ψ x‖ ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      exact mul_le_one₀ h1 (norm_nonneg _) hα
  · rw [norm_zero]; exact zero_le_one
