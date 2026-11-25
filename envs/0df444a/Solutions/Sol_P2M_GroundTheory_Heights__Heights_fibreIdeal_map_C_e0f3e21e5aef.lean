-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreIdeal_map_C_e0f3e21e5aef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:58.411077+00:00
-- url     : https://prove2.me/submissions/977f3faf-17ae-4de5-b782-9edb734ea19a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {σ : Type*} {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (t : σ → ℂ) :
    fibreIdeal (J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ))) t = J := by
  have h : (MvPolynomial.map (eval t)).comp (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ)) =
      RingHom.id (MvPolynomial (Fin n) ℂ) := by
    ext p <;> simp
  rw [fibreIdeal, Ideal.map_map, h, Ideal.map_id]
end GroundTheory.Heights₂.Heights
