-- Prove2me | solution 1 for RiemannMasullo.mappingSeminorm_apply
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:37:03.526858+00:00
-- url     : https://prove2.me/submissions/aaf74964-1f78-47bd-b044-4044bf9bfa6f

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L98-L108
import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]

theorem solution (T : {T : Set E // IsVonNBounded ℂ T})
    (p : {p : Seminorm ℂ F // Continuous p}) (f : E →L[ℂ] F) :
    mappingSeminorm T p f = ⨆ x : T.val, p.val (f x) := by
  unfold mappingSeminorm
  apply Seminorm.iSup_apply
  apply Seminorm.bddAbove_range_iff.mpr
  intro g
  obtain ⟨r, _, hr⟩ :=
    ((PolynormableSpace.withSeminorms ℂ F).image_isVonNBounded_iff_seminorm_bounded g).mp
      (T.2.image g) p
  exact ⟨r, forall_mem_range.mpr fun x ↦ (hr x x.2).le⟩
