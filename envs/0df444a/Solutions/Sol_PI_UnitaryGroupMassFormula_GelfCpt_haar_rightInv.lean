-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.haar_rightInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:29.2193+00:00
-- url     : https://prove2.me/submissions/6358176d-4b51-4239-8e61-f6cd4505e3c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  constructor
  intro g
  have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
  have hu : Measure.map (· * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne μ)).ne'
  have ht : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  have h1 : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) * μ Set.univ =
      1 * μ Set.univ := by
    rw [one_mul]
    conv_rhs => rw [← hu, e]
    simp
  have hc : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 h1
  rw [e, ENNReal.coe_eq_one.mp hc, one_smul]
end PI.UnitaryGroupMassFormula.GelfCpt
