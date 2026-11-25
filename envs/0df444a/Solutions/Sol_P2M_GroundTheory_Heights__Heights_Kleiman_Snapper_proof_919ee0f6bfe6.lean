-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Snapper_proof_919ee0f6bfe6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:29.994916+00:00
-- url     : https://prove2.me/submissions/13ed7e54-5473-4cd0-b583-64a80246bb64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isNumPolyLT_sum_9991b4d10672
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_isNumPolyLT_1596cbf394e9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace Snapper
theorem _root_.solution (hD : SnapperDevissage.Statement.{u, v, w}) (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) (hP : SnapperDiffPoly.Statement) : Snapper.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x e hZ E _ _ _ _ F hF t L
  obtain ⟨r, pp, a, hpp, heq⟩ := hD k Ω N x E F hF
  have hdim : ∀ m, ringKrullDim (Poly k N ⧸ pp m) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := fun m =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective (hpp m).2.2)).trans hZ.dim.le
  obtain ⟨Q, hQ, hev⟩ := isNumPolyLT_sum (fun m n c => (pieceChar k (pp m) (a m) L n c : ℚ))
    fun m => pieceChar_isNumPolyLT hH hS hP L (e + 1) (pp m) (hpp m).1 (hpp m).2.1 (hpp m).2.2 (hdim m) (a m)
  refine ⟨Q, ?_, fun n c => ?_⟩
  · rcases hQ with h0 | h0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · omega
  · rw [heq t L n c, ← hev n c]
    push_cast
    rfl
end Snapper
end GroundTheory.Heights₂.Heights.Kleiman
