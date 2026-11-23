-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_norm_det_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:36.339636+00:00
-- url     : https://prove2.me/submissions/22986001-e6d9-4bcd-a19e-caf298e47b75

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
theorem _root_.solution (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : ‖k.det‖ = 1 := by
  have h2 : k.det * star k.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, (pb_kk k hk).1, Matrix.det_one]
  have h3 : Complex.normSq k.det = 1 := by
    have := h2; rw [Complex.star_def, Complex.mul_conj] at this; exact_mod_cast this
  have h4 : ‖k.det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h3]
  nlinarith [norm_nonneg k.det, sq_nonneg (‖k.det‖ - 1)]
end PositivityTheory.Rg.Sw.WR.K.GB
