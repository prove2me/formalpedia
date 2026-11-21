-- Prove2me | solution 1 for RiemannMasullo.hasBoundedLift_iff_image
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:30:30.541968+00:00
-- url     : https://prove2.me/submissions/dce73590-df74-45bc-8459-a2c55271da36

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L709-L716
import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

theorem solution (f : E →L[ℂ] F) (B : Set F) :
    HasBoundedLift f B ↔ ∃ A : Set E, IsVonNBounded ℂ A ∧ f '' A = B := by
  constructor
  · rintro ⟨A, hA, hB⟩
    refine ⟨A ∩ f ⁻¹' B, hA.subset inter_subset_left, ?_⟩
    rw [image_inter_preimage, inter_eq_right.mpr hB]
  · rintro ⟨A, hA, hB⟩
    exact ⟨A, hA, hB.ge⟩
