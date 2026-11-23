-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.eq_of_isMulLeftInvariant_of_univ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:28.302985+00:00
-- url     : https://prove2.me/submissions/fce3cd7c-ca13-4a84-9d41-caed18ecb083

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfConv
open MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfConv
theorem _root_.solution (μ ν : Measure G) [μ.IsHaarMeasure]
    [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] (h : ν Set.univ = μ Set.univ) :
    ν = μ := by
  have hc : ν = haarScalarFactor ν μ • μ := isMulInvariant_eq_smul_of_compactSpace ν μ
  set C := haarScalarFactor ν μ
  have hμt : μ Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  have : (C : ENNReal) * μ Set.univ = 1 * μ Set.univ := by
    rw [one_mul, ← smul_eq_mul, ← ENNReal.smul_def, ← Measure.smul_apply, ← hc, h]
  have hC : C = 1 := by
    rwa [ENNReal.mul_left_inj (NeZero.ne _) hμt, ENNReal.coe_eq_one] at this
  rw [hc, hC, one_smul]
end PI.UnitaryGroupMassFormula.GelfConv
