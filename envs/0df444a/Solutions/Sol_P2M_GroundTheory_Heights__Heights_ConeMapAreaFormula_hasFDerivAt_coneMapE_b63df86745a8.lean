-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hasFDerivAt_coneMapE_b63df86745a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:34:11.966682+00:00
-- url     : https://prove2.me/submissions/5aea2968-6895-42d5-b808-5f2152bd73a5

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
theorem _root_.solution {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) :
    HasFDerivAt (coneMapE v)
      (p 0 • ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
          ((fderiv ℂ v (tailL e p)).comp (tailL e))) +
        (EuclideanSpace.proj (0 : Fin (e + 1)) :
          EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] ℂ).smulRight (WithLp.toLp 2 (v (tailL e p)))) p := by
  have hc := (EuclideanSpace.proj (0 : Fin (e + 1)) :
    EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] ℂ).hasFDerivAt (x := p)
  have hf := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.hasFDerivAt.comp p
    (hv.hasFDerivAt.comp p (tailL e).hasFDerivAt)
  exact hc.smul hf
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
