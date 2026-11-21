-- Prove2me | solution 1 for RiemannMasullo.isPolarBornology_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:37:07.364875+00:00
-- url     : https://prove2.me/submissions/0548ad5b-9229-43f4-9df8-0618c280d158

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L294-L300
import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]

theorem solution : IsPolarBornology {T : Set E | IsVonNBounded ℂ T} := by
  refine ⟨⟨∅, isVonNBounded_empty ℂ E⟩,
    directedOn_of_sup_mem (fun _ _ ↦ IsVonNBounded.union), ?_, ?_⟩
  · intro T hT
    exact hT.image (toWeakSpaceCLM ℂ E)
  · intro T hT c _
    exact ⟨c • T, hT.image (c • ContinuousLinearMap.id ℂ E), Subset.rfl⟩
