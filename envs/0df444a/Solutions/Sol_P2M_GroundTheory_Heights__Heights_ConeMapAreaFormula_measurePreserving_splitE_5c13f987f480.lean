-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_splitE_5c13f987f480
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:24.310941+00:00
-- url     : https://prove2.me/submissions/81aed4c7-a85a-4f86-bf45-79a5d7dbbe30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_toLp_5a69aa31999e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal ComplexOrder
open GroundTheory.Heights₂.Heights.ConeMapAreaFormula
namespace GroundTheory.Heights₂.Heights.ConeMapAreaFormula
theorem _root_.solution (e : ℕ) : MeasurePreserving (splitE e) volume volume := by
  have h1 := (measurePreserving_toLp (e + 1)).symm (MeasurableEquiv.toLp 2 (Fin (e + 1) → ℂ))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (e + 1) => ℂ) 0
  have h3 := Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
    (ν := (volume : Measure (Fin e → ℂ)))
  exact h3.comp (h2.comp h1)
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
