-- Prove2me | solution 1 for PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:31.621808+00:00
-- url     : https://prove2.me/submissions/6b790d2a-0ae9-491b-800a-64f5cddf61f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientIntegralBound_QuotientLIntegralLeMultiplicityLIntegral
import Theorems.Thm_PI_PoincareSeriesFinite_UnitaryGroupMassFormula_quotientLIntegral_le_multiplicityLIntegral
import Theorems.Thm_Formalism_L2_SG_FoldBound_foldBound_holds
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_mult_lt_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open PI PI.PoincareSeriesFinite PI.PoincareSeriesFinite.UnitaryGroupMassFormula
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.PoincareSeriesFinite.UnitaryGroupMassFormula
theorem _root_.solution (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesFinite G μ := by
  intro Γ S hΓ hSΓ Ω hΩ h1 a Ph hPh F hF hL D hD x
  haveI := hΓ
  refine lt_of_le_of_lt (foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.isClosed.measurableSet a Ph hPh.1 hPh.2.1
    hPh.2.2 F hF D hD x) ?_
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (PI.FoldMult.UnitaryGroupMassFormula.mult_lt_top Γ Ω hΩ x)) ?_
  exact lt_of_le_of_lt (quotientLIntegral_le_multiplicityLIntegral μ Γ Ω h1 F Ph) hL
end PI.PoincareSeriesFinite.UnitaryGroupMassFormula
