-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_toLp_5a69aa31999e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:06.476267+00:00
-- url     : https://prove2.me/submissions/c387ef10-d0f8-47f2-9357-843a5c272419

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_preserving_uncurry_665ed32e1d59

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
theorem _root_.solution (m : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin m → ℂ) → EuclideanSpace ℂ (Fin m)) volume volume := by
  have h1 : MeasurePreserving
      (fun (x : Fin m → ℂ) (i : Fin m) => Complex.measurableEquivPi (x i)) volume volume :=
    volume_preserving_pi fun _ => Complex.volume_preserving_equiv_pi
  have h2 := volume_preserving_uncurry (Fin m) (Fin 2)
  have h3 := PiLp.volume_preserving_toLp (Fin m × Fin 2)
  have h := (reIm m).symm.measurePreserving.comp (h3.comp (h2.comp h1))
  have hfun : (WithLp.toLp 2 : (Fin m → ℂ) → EuclideanSpace ℂ (Fin m)) =
      ⇑(reIm m).symm ∘ WithLp.toLp 2 ∘ Function.uncurry ∘
        fun x i => Complex.measurableEquivPi (x i) := by
    funext x
    rw [Function.comp_apply, LinearIsometryEquiv.eq_symm_apply]
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> rfl
  rw [hfun]
  exact h
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
