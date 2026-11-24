-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:13.1902+00:00
-- url     : https://prove2.me/submissions/8f70ba0d-538a-4377-84a9-2582c1f69fc8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (a : J → MRing ι R) (p : MRing ι R) :
    aeval (chartSubst a) (liftForm p) = Polynomial.C p := by
  have e : (aeval (chartSubst a)).comp (liftForm : MRing ι R →ₐ[R] MRing (extIdx ι J) R) =
      Polynomial.CAlgHom := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftForm, chartSubst]
  exact DFunLike.congr_fun e p
end GroundTheory.Heights₂.Heights.NumbersDVR
