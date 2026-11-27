-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConormalGenerationGeneric_D_eq_sum_pderiv_8adc904b72d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:21.570337+00:00
-- url     : https://prove2.me/submissions/dbedc2b8-a802-4c45-8b08-c600ec1f19e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StConormalGenerationGeneric
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GenericGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric

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
noncomputable section
open MvPolynomial KaehlerDifferential TensorProduct IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace ConormalGenerationGeneric
theorem _root_.solution {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    D ℂ (MvPolynomial (Fin n) ℂ) g = ∑ l, pderiv l g • D ℂ (MvPolynomial (Fin n) ℂ) (X l) := by
  conv_lhs => rw [← (mvPolynomialBasis ℂ (Fin n)).sum_repr (D ℂ _ g)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mvPolynomialBasis_repr_apply]
  congr 1
  rw [← (mvPolynomialBasis ℂ (Fin n)).repr_symm_single_one, mvPolynomialBasis_repr_symm_single, one_smul]
end ConormalGenerationGeneric
end GroundTheory.Heights₂.Heights
