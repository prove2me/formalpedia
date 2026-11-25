-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_fderiv_coneMapE_single_5ae304af17b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:01.914056+00:00
-- url     : https://prove2.me/submissions/36a053da-1bca-4d7d-a26d-08fa0ef13d30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_tailL_apply_e006b4191384
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hasFDerivAt_coneMapE_b63df86745a8

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
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) (a : Fin (e + 1)) :
    fderiv ℂ (coneMapE v) p (EuclideanSpace.single a 1) =
      (Fin.cons 1 (fun _ => p 0) : Fin (e + 1) → ℂ) a • WithLp.toLp 2 (gramVecs v (tailL e p) a) := by
  rw [(hasFDerivAt_coneMapE hv).fderiv]
  refine Fin.cases ?_ (fun j => ?_) a
  · have h0 : tailL e (EuclideanSpace.single 0 1) = 0 := by
      funext j
      simp [tailL_apply, Fin.succ_ne_zero]
    simp [h0, gramVecs]
  · have h1 : tailL e (EuclideanSpace.single j.succ 1) = Pi.single j 1 := by
      funext i
      simp [tailL_apply, Pi.single_apply]
    simp [h1, gramVecs, Fin.succ_ne_zero]
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
