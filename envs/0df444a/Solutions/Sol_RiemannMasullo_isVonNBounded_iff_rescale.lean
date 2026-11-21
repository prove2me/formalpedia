-- Prove2me | solution 1 for RiemannMasullo.isVonNBounded_iff_rescale
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:30:31.760175+00:00
-- url     : https://prove2.me/submissions/51b5a17f-1851-42a7-97ac-8889aadfbae0

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L156-L169
import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo


theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ U ∈ 𝓝 (0 : E), ∃ c : ℂ, c ≠ 0 ∧ c • B ⊆ U := by
  constructor
  · intro hB U hU
    obtain ⟨c, hc, hmaps⟩ :=
      (eventually_mem_nhdsWithin.and (hB hU).eventually_nhdsNE_zero).exists
    exact ⟨c, hc, hmaps.image_subset⟩
  · intro hB
    apply (nhds_basis_balanced ℂ E).isVonNBounded_iff.mpr
    rintro U ⟨hU, hbal⟩
    obtain ⟨c, hc, hsub⟩ := hB U hU
    have hinv : B ⊆ c⁻¹ • U := (smul_set_subset_iff₀ hc).mp hsub
    exact Absorbs.of_norm ⟨‖c⁻¹‖, fun d hd ↦ hinv.trans (hbal.smul_mono hd)⟩
