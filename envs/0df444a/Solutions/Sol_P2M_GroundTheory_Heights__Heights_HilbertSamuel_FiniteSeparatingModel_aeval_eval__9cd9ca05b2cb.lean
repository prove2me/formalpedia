-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_aeval_eval__9cd9ca05b2cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:36.640798+00:00
-- url     : https://prove2.me/submissions/28c41660-6cb1-47b6-9ec7-bc26365c7696

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiniteSeparatingModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
variable {σ : Type} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
theorem _root_.solution (ℓ : Fin e → MvPolynomial σ ℚ) (Q : Polynomial (MvPolynomial (Fin e) ℚ))
    (g : MvPolynomial σ ℚ) (z : σ → ℂ) :
    aeval z (Q.eval₂ (aeval ℓ).toRingHom g) =
      Q.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z g) := by
  have hc : (aeval (R := ℚ) z).toRingHom.comp (aeval (R := ℚ) ℓ).toRingHom =
      (aeval fun j => aeval z (ℓ j)).toRingHom := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  have := Polynomial.hom_eval₂ Q (aeval (R := ℚ) ℓ).toRingHom (aeval (R := ℚ) z).toRingHom g
  rw [hc] at this
  exact this
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
