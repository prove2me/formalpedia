-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_cdOn_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:30.186095+00:00
-- url     : https://prove2.me/submissions/cde58699-3107-4dbc-a543-58c6f74e0918

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_det
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_adj

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
    (hs : ∀ b ∈ s, (f b).det ≠ 0) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => (f b)⁻¹ i j) s := by
  have e : (fun b => (f b)⁻¹ i j) = fun b => ((f b).det)⁻¹ * (f b).adjugate i j := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv]; simp [Matrix.smul_apply]
  rw [e]
  exact ((pb_cd_det hf).contDiffOn.inv hs).mul (pb_cd_adj hf i j).contDiffOn
end PositivityTheory.Rg.Sw.WR.K.GB
