-- Prove2me | solution 1 for RiemannMasullo.locallyConvexFinalTopology_id
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:40:53.050743+00:00
-- url     : https://prove2.me/submissions/3a2e8048-a311-40ef-ac3b-99024002509d

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L245-L253
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {ι : Type*} {X : ι → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

theorem solution [t : TopologicalSpace E] [PolynormableSpace ℂ E] :
    locallyConvexFinalTopology (X := fun _ : Unit ↦ E) (fun _ ↦ LinearMap.id) = t := by
  change (SeminormFamily.moduleFilterBasis
    (Subtype.val : {p : Seminorm ℂ E // ∀ _ : Unit, Continuous p} → Seminorm ℂ E)).topology = t
  have h : (fun p : Seminorm ℂ E ↦ ∀ _ : Unit, Continuous p) =
      (fun p : Seminorm ℂ E ↦ Continuous p) := by
    simp only [forall_const]
  rw [h]
  exact (PolynormableSpace.withSeminorms ℂ E).withSeminorms_eq.symm
