-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_continuous_eval__b98193422951
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:41.254248+00:00
-- url     : https://prove2.me/submissions/b3e8627c-7fed-45cb-927d-dc8c903a647a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsNear

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
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootsNear
theorem _root_.solution {e : ℕ} (G : Polynomial (MvPolynomial (Fin e) ℚ)) (t : ℂ) :
    Continuous fun y : Fin e → ℂ => G.eval₂ (aeval y).toRingHom t := by
  simp only [Polynomial.eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  have : (fun y : Fin e → ℂ => (aeval y).toRingHom (G.coeff i)) =
      fun y => eval y (MvPolynomial.map (algebraMap ℚ ℂ) (G.coeff i)) := by
    funext y
    simp [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  rw [this]
  exact MvPolynomial.continuous_eval _
end RootsNear
end GroundTheory.Heights₂.Heights.HilbertSamuel
