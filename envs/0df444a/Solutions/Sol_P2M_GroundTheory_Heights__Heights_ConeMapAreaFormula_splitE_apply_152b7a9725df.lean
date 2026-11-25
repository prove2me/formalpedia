-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_splitE_apply_152b7a9725df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:05.012803+00:00
-- url     : https://prove2.me/submissions/f1b0c97a-61e1-4b01-9a92-ef9c4a863ec9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne

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
theorem _root_.solution (e : ℕ) (p : EuclideanSpace ℂ (Fin (e + 1))) :
    splitE e p = (fun j => p j.succ, p 0) := by
  ext j <;> simp [splitE, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm, Fin.tail]
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
