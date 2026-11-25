-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_cdOn_detInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:07.630187+00:00
-- url     : https://prove2.me/submissions/30e6afac-c81b-497d-b86f-f509d1aa8f45

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
theorem _root_.solution {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (s : Set (Mc n))
    (hs : ∀ b ∈ s, (f b).det ≠ 0) : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => (f b)⁻¹.det) s := by
  have e : (fun b => (f b)⁻¹.det) = fun b => ((f b).det)⁻¹ := by
    funext b; rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [e]; exact (pb_cd_det hf).contDiffOn.inv hs
end PositivityTheory.Rg.Sw.WR.K.GB
