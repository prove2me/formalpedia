-- Prove2me | solution 1 for PI.NglqJacSplitW.exists_test_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:11.027534+00:00
-- url     : https://prove2.me/submissions/9710532e-1462-430c-a1de-7b9615c5202d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.NglqJacSplitW
theorem _root_.solution [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (ν : Measure (ι → F))
    [ν.IsAddHaarMeasure] : ∃ K : Set (ι → F), MeasurableSet K ∧ ν K ≠ 0 ∧ ν K ≠ ∞ := by
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : ι → F)
  exact ⟨K, hKc.isClosed.measurableSet, (MeasureTheory.Measure.measure_pos_of_mem_nhds (μ := ν) hK0).ne', hKc.measure_lt_top.ne⟩
end PI.NglqJacSplitW
