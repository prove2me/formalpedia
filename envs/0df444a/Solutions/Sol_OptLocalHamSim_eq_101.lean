-- Prove2me | solution 1 for OptLocalHamSim.eq_101
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:25:39.440223+00:00
-- url     : https://prove2.me/submissions/1ece6f26-1a8b-4bf9-bb5c-4d0beb9c5e4b

import Mathlib

open scoped Matrix Matrix.Norms.L2Operator
namespace OptLocalHamSim

theorem eq_101 {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : Matrix m m ℂ) (hV : V ∈ Matrix.unitaryGroup m ℂ) (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (ι : Matrix m n ℂ) (η : ℝ) (hη : ‖V * ι - ι * U‖ ≤ η) :
    Vᴴ * ι - ι * Uᴴ = Vᴴ * (ι * U - V * ι) * Uᴴ ∧ ‖Vᴴ * ι - ι * Uᴴ‖ ≤ η := by
  have hV1 : V * Vᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hV; rwa [Matrix.star_eq_conjTranspose] at this
  have hV2 : Vᴴ * V = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hV; rwa [Matrix.star_eq_conjTranspose] at this
  have hU1 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU; rwa [Matrix.star_eq_conjTranspose] at this
  have hU2 : Uᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hU; rwa [Matrix.star_eq_conjTranspose] at this
  have key : Vᴴ * ι - ι * Uᴴ = Vᴴ * (ι * U - V * ι) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hU1,
      ← Matrix.mul_assoc Vᴴ V, hV2, Matrix.mul_one, Matrix.one_mul]
  have one_le : ∀ {k : Type} [Fintype k] [DecidableEq k], ‖(1 : Matrix k k ℂ)‖ ≤ 1 := by
    intro k _ _
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)
  have unit_le : ∀ {k : Type} [Fintype k] [DecidableEq k] (W : Matrix k k ℂ), W * Wᴴ = 1 →
      ‖Wᴴ‖ ≤ 1 := by
    intro k _ _ W hW
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Wᴴ
    rw [Matrix.conjTranspose_conjTranspose, hW] at h
    have h1 := one_le (k := k)
    have h0 : 0 ≤ ‖Wᴴ‖ := norm_nonneg _
    nlinarith
  refine ⟨key, ?_⟩
  rw [key]
  have hVn := unit_le V hV1
  have hUn := unit_le U hU1
  have hm : ‖ι * U - V * ι‖ ≤ η := by rw [norm_sub_rev]; exact hη
  calc ‖Vᴴ * (ι * U - V * ι) * Uᴴ‖ ≤ ‖Vᴴ * (ι * U - V * ι)‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Vᴴ‖ * ‖ι * U - V * ι‖) * ‖Uᴴ‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * η) * 1 := by
        have h0 := norm_nonneg (ι * U - V * ι)
        apply mul_le_mul _ hUn (norm_nonneg _) (by nlinarith)
        exact mul_le_mul hVn hm h0 zero_le_one
    _ = η := by ring

end OptLocalHamSim

theorem solution {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : Matrix m m ℂ) (hV : V ∈ Matrix.unitaryGroup m ℂ) (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (ι : Matrix m n ℂ) (η : ℝ) (hη : ‖V * ι - ι * U‖ ≤ η) :
    Vᴴ * ι - ι * Uᴴ = Vᴴ * (ι * U - V * ι) * Uᴴ ∧ ‖Vᴴ * ι - ι * Uᴴ‖ ≤ η :=
  OptLocalHamSim.eq_101 V hV U hU ι η hη
