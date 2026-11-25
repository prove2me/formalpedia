-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_curveNormalisation_le_a06ad3adf3e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:38:57.982077+00:00
-- url     : https://prove2.me/submissions/38b59140-8383-4861-8bd7-200abe9fc259

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdDeterminesPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdDeterminesPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    ringKrullDim (curveNormalisation I q) ≤ ringKrullDim (curveLocalRing I q) :=
  Order.krullDim_le_of_strictMono
    (fun Q ↦ ⟨Q.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)), inferInstance⟩)
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap (R := curveLocalRing I q) h
end GroundTheory.Heights₂.Heights
