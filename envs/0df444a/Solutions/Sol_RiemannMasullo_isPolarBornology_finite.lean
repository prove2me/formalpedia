-- Prove2me | solution 1 for RiemannMasullo.isPolarBornology_finite
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:37:05.88702+00:00
-- url     : https://prove2.me/submissions/051daeac-40a1-4557-97f2-c9add141fbff

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L268-L273
import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]

theorem solution : IsPolarBornology {T : Set E | T.Finite} := by
  refine ⟨⟨∅, Set.finite_empty⟩, directedOn_of_sup_mem (fun _ _ ↦ Set.Finite.union), ?_, ?_⟩
  · intro T hT
    exact (Set.Finite.image (toWeakSpace ℂ E) hT).isVonNBounded
  · intro T hT c _
    exact ⟨c • T, Set.Finite.smul_set hT, Subset.rfl⟩
