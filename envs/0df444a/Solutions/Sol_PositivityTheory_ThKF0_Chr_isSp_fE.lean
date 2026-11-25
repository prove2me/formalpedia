-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.isSp_fE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:48.665511+00:00
-- url     : https://prove2.me/submissions/3585479c-33ab-4a7b-997a-1a43e36dd8bb

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution : IsSp (fE R κ) := fun w w' => by
  show w.2 ⬝ᵥ (-w'.1) - w'.2 ⬝ᵥ (-w.1) = _
  rw [dotProduct_neg, dotProduct_neg, dotProduct_comm w.2, dotProduct_comm w'.2]; ring
end PositivityTheory.ThKF0.Chr
