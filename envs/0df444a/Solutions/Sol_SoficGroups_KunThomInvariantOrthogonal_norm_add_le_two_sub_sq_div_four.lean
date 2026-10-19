-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.norm_add_le_two_sub_sq_div_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/e0e4a809-23c6-4c56-be6d-40807af85295

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups.KunThomInvariantOrthogonal
theorem _root_.solution
    (x y : H) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδtwo : δ ≤ 2)
    (hnorm : ‖y‖ = ‖x‖)
    (hseparated : δ * ‖x‖ ≤ ‖x - y‖) :
    ‖x + y‖ ≤ (2 - δ ^ 2 / 4) * ‖x‖ := by
  have hpar := parallelogram_law_with_norm ℂ x y
  have hsq : (δ * ‖x‖) ^ 2 ≤ ‖x - y‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg x))
      (norm_nonneg (x - y))).mpr hseparated
  have hδsq : δ ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (2 - δ), sq_nonneg δ]
  have htarget : 0 ≤ (2 - δ ^ 2 / 4) * ‖x‖ :=
    mul_nonneg (by nlinarith) (norm_nonneg x)
  have hadd :
      ‖x + y‖ ^ 2 ≤ ((2 - δ ^ 2 / 4) * ‖x‖) ^ 2 := by
    rw [hnorm] at hpar
    nlinarith [sq_nonneg (δ ^ 2 * ‖x‖)]
  exact (sq_le_sq₀ (norm_nonneg (x + y)) htarget).mp hadd
end SoficGroups.KunThomInvariantOrthogonal
