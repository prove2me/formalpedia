-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolA.integrable_of_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:16.350032+00:00
-- url     : https://prove2.me/submissions/8459875d-2215-4860-ba22-a4af8864a653

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolA
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
namespace PositivityTheory.Rg.Sw.LVs.HolA
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] {f : Kg → W} (hf : Continuous f) :
    Integrable f μ := by
  have hm : AEStronglyMeasurable f μ := by
    simpa using (hf.continuousOn (s := univ)).aestronglyMeasurable_of_isCompact isCompact_univ
      MeasurableSet.univ (μ := μ)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hf.continuousOn (s := univ))
  exact Integrable.of_bound hm C (Eventually.of_forall fun k => hC k (mem_univ k))
end PositivityTheory.Rg.Sw.LVs.HolA
