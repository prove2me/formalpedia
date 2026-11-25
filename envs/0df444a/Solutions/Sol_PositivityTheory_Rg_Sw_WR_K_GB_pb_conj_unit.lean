-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_conj_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:01.583099+00:00
-- url     : https://prove2.me/submissions/43c0b28e-0182-49e2-a306-44eab9af7d54

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_norm_det_unitary

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
    IsUnit (k * Y * kᴴ).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_mul, Matrix.det_mul]
  have h1 : k.det ≠ 0 := fun h => by simpa [h] using pb_norm_det_unitary k hk
  have h2 : kᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact fun h => h1 (by simpa using h)
  exact mul_ne_zero (mul_ne_zero h1 (isUnit_iff_ne_zero.1 hY)) h2
end PositivityTheory.Rg.Sw.WR.K.GB
