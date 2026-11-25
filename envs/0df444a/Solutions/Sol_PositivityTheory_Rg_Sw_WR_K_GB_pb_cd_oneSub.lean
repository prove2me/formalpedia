-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_oneSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:04.42401+00:00
-- url     : https://prove2.me/submissions/235b2440-c5a6-4b69-8111-7fea5bcdd20a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (c : ℂ) (i j : Fin n) : ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 - c • b) i j) := by
  have h : (fun b : Mc n => (1 - c • b) i j) = fun b => (1 + ((-1) * c) • b) i j := by
    funext b; simp [sub_eq_add_neg, neg_smul]
  rw [h]; exact pb_cd_affine c (-1) i j
end PositivityTheory.Rg.Sw.WR.K.GB
