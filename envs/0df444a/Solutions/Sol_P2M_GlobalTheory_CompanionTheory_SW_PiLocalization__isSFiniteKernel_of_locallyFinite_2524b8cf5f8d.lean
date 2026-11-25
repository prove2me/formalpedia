-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_locallyFinite_2524b8cf5f8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:18.436058+00:00
-- url     : https://prove2.me/submissions/38862b42-97b5-43d3-9397-f860b7e07f75

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFubini
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_forall_univ_lt_top_f4df5b9f1781

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] [SigmaCompactSpace β]
    (κ : Kernel α β) (h : ∀ a, IsLocallyFiniteMeasure (κ a)) : IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed (compactCovering β)
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (isCompact_compactCovering β i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = Set.univ := by
    simp only [C, iUnion_disjointed]
    exact iUnion_compactCovering β
  have hCf : ∀ a k, κ a (C k) < ⊤ := fun a k => by
    haveI := h a
    exact (measure_mono (disjointed_subset _ k)).trans_lt
      (isCompact_compactCovering β k).measure_lt_top
  have hk : ∀ k, IsSFiniteKernel (Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [Kernel.restrict_apply]
      simpa using hCf a k)
  have hsum : κ = Kernel.sum fun k => Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [Kernel.sum_apply]
    simp only [Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu, Measure.restrict_univ]
  rw [hsum]
  infer_instance
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
