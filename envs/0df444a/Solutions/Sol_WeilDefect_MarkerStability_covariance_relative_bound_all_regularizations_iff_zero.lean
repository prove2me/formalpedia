-- Prove2me | solution 1 for WeilDefect.MarkerStability.covariance_relative_bound_all_regularizations_iff_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T21:40:56.223716+00:00
-- url     : https://prove2.me/submissions/655027c7-637a-466d-87c4-bc0a1c46f2d3

import Mathlib
set_option autoImplicit false
open ContinuousLinearMap Filter Set
open scoped Topology
noncomputable section

private theorem norm_le_all_positive_scales_iff_zero
    {E : Type*} [NormedAddCommGroup E] (x : E) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖x‖ ≤ α * ε) ↔ x = 0 := by
  constructor
  · intro h
    have ht : Tendsto (fun ε : ℝ => α * ε) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      simpa using ((tendsto_id : Tendsto (fun ε : ℝ => ε) (nhds (0 : ℝ)) (nhds 0)).mono_left nhdsWithin_le_nhds).const_mul α
    have hz : ‖x‖ ≤ 0 := ge_of_tendsto ht (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact h ε hε)
    exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg x))
  · rintro rfl ε hε
    simpa using mul_nonneg hα hε.le

theorem solution
    {K H : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : K →L[ℂ] H) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖B ∘L B.adjoint‖ ≤ α * ε) ↔ B = 0 := by
  rw [norm_le_all_positive_scales_iff_zero _ α hα]
  constructor
  · intro h
    have hh : B.adjoint.adjoint ∘L B.adjoint = 0 := by simpa using h
    have hz := ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp hh
    have he := congrArg (fun C : H →L[ℂ] K => C.adjoint) hz
    simpa using he
  · rintro rfl
    simp
