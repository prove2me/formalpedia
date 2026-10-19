-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_sqrt_div_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/efef239f-cedb-4b13-b102-381d62a6aeb5

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution
    (x : H) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i : Fin 3,
      ‖ejResidualProjection (V i) x‖ ≤ T) :
    Real.sqrt (ejThreeResidualEnergy V x / 3) ≤ T := by
  have h₀ : ‖ejResidualProjection (V 0) x‖ ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hT).mpr (hbound 0)
  have h₁ : ‖ejResidualProjection (V 1) x‖ ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hT).mpr (hbound 1)
  have h₂ : ‖ejResidualProjection (V 2) x‖ ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hT).mpr (hbound 2)
  apply Real.sqrt_le_iff.mpr
  refine ⟨hT, ?_⟩
  unfold ejThreeResidualEnergy
  nlinarith
end SoficGroups
