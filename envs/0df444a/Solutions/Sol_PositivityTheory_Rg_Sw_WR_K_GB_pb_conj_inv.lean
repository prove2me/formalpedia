-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_conj_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:57.753833+00:00
-- url     : https://prove2.me/submissions/0bd16347-20b0-4951-9174-b91f1c8918cb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_kk

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
theorem _root_.solution (Y k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : IsUnit Y.det) :
    (k * Y * kᴴ)⁻¹ = k * Y⁻¹ * kᴴ := by
  apply Matrix.inv_eq_right_inv
  calc k * Y * kᴴ * (k * Y⁻¹ * kᴴ) = k * (Y * (kᴴ * k) * Y⁻¹) * kᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [(pb_kk k hk).2, Matrix.mul_one, Matrix.mul_nonsing_inv _ hY, Matrix.mul_one, (pb_kk k hk).1]
end PositivityTheory.Rg.Sw.WR.K.GB
