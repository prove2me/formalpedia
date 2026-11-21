-- Prove2me | solution 1 for RiemannMasullo.liftsBoundedSets_id
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:30:31.127994+00:00
-- url     : https://prove2.me/submissions/db73bf05-e9f9-408c-82bd-60ce13e4633a

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L719-L721
import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

theorem solution : LiftsBoundedSets (ContinuousLinearMap.id ℂ E) := by
  intro B hB
  exact ⟨B, hB, fun x hx ↦ ⟨x, hx, rfl⟩⟩
