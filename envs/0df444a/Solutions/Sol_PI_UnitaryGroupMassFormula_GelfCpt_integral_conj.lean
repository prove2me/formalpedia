-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.integral_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:35.274903+00:00
-- url     : https://prove2.me/submissions/7802cafc-d34a-41d8-b123-bbe2ea587467

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_haar_rightInv

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
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ) (h : G) :
    ∫ g, F (h * g * h⁻¹) ∂μ = ∫ g, F g ∂μ := by
  have := haar_rightInv μ
  have e1 := integral_mul_left_eq_self (μ := μ) (fun y => F (y * h⁻¹)) h
  have e2 := integral_mul_right_eq_self (μ := μ) F h⁻¹
  exact e1.trans e2
end PI.UnitaryGroupMassFormula.GelfCpt
