-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_norm_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:13.993941+00:00
-- url     : https://prove2.me/submissions/f86019e3-ab68-4b14-a1cb-8d608afa510c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound

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
theorem _root_.solution (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (l : ℝ) :
    (1 + |l|) / Real.sqrt 2 ≤ ‖1 - a * (l : ℂ)‖ := by
  have hsq : ‖1 - a * (l : ℂ)‖ ^ 2 = 1 + l ^ 2 := by
    rw [Complex.sq_norm]
    rcases ha with rfl | rfl <;> simp [Complex.normSq_apply] <;> ring
  have h2 : ((1 + |l|) / Real.sqrt 2) ^ 2 ≤ ‖1 - a * (l : ℂ)‖ ^ 2 := by
    rw [hsq, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [sq_abs l, sq_nonneg (1 - |l|), abs_nonneg l]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2
end PositivityTheory.Rg.Sw.WR.K.GB
