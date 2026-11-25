-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:57.846634+00:00
-- url     : https://prove2.me/submissions/aae80f46-5884-4d9e-9a76-3cb654b46db0

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
theorem _root_.solution (c : ℂ) (k b : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    1 - c • (k * b * kᴴ) = k * (1 - c • b) * kᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (pb_kk k hk).1, Matrix.mul_smul, Matrix.smul_mul]
end PositivityTheory.Rg.Sw.WR.K.GB
