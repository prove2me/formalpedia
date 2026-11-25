-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:11.715784+00:00
-- url     : https://prove2.me/submissions/a35cf566-b3eb-418d-822f-8d191cf83ead

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_det

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
theorem _root_.solution {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (i j : Fin n) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b => (f b).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply pb_cd_det
  intro r c
  by_cases h : r = j
  · subst h; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne h]; exact hf r c
end PositivityTheory.Rg.Sw.WR.K.GB
