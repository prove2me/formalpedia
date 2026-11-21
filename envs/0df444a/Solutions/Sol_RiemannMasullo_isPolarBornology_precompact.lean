-- Prove2me | solution 1 for RiemannMasullo.isPolarBornology_precompact
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:37:06.740383+00:00
-- url     : https://prove2.me/submissions/c7be5cb8-96a0-41f5-8d74-2057e79d0761

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L276-L291
import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]

theorem solution :
    IsPolarBornology {T : Set E | IsPrecompactInCompletion T} := by
  have hprecompact (T : Set E) : IsPrecompactInCompletion T ↔ TotallyBounded T := by
    have hcoe := (UniformSpace.Completion.isUniformEmbedding_coe E).isUniformInducing
    unfold IsPrecompactInCompletion IsRelativelyCompact
    rw [← totallyBounded_image_iff hcoe, ← totallyBounded_closure]
    exact ⟨IsCompact.totallyBounded, fun h ↦ h.isCompact_of_isClosed isClosed_closure⟩
  simp_rw [hprecompact]
  refine ⟨⟨∅, totallyBounded_empty⟩, directedOn_of_sup_mem (fun _ _ ↦ TotallyBounded.union),
    ?_, ?_⟩
  · intro T hT
    exact (TotallyBounded.isVonNBounded ℂ hT).image (toWeakSpaceCLM ℂ E)
  · intro T hT c _
    have hc :=
      (uniformContinuousConstSMul_of_continuousConstSMul ℂ E).uniformContinuous_const_smul c
    exact ⟨c • T, TotallyBounded.image hT hc, Subset.rfl⟩
