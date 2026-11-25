-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:21.256952+00:00
-- url     : https://prove2.me/submissions/f2544cc5-a65f-4315-834a-af1d94b0f4da

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_entry

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
theorem _root_.solution (a : ℂ) (e : ℂ) (i j : Fin n) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 + (e * a) • b) i j) := by
  have h : (fun b : Mc n => (1 + (e * a) • b) i j) = fun b => (1 : Mc n) i j + (e * a) * b i j := by
    funext b; simp [Matrix.add_apply, Matrix.smul_apply]
  rw [h]; exact contDiff_const.add (contDiff_const.mul (pb_cd_entry i j))
end PositivityTheory.Rg.Sw.WR.K.GB
