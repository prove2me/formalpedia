-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:48:46.122748+00:00
-- url     : https://prove2.me/submissions/d14ee701-ffce-4bf1-81df-30d685ae01ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_weight_groupWeight_apply_bef25cb93b13

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
variable {k n : ℕ}
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (δ : ℕ) (f : MvPolynomial (Fin k × Fin n) R) :
    IsMultiHomog δ f ↔ ∀ i : Fin k, IsWeightedHomogeneous (inGroup i) f δ := by
  constructor
  · intro h i d hd
    rw [← weight_groupWeight_apply, h hd]
  · intro h d hd
    funext i
    rw [weight_groupWeight_apply, h i hd]
end GroundTheory.Heights₂.Heights
