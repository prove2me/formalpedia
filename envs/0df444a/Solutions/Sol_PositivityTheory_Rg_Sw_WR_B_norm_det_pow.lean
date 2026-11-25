-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_det_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:03.936845+00:00
-- url     : https://prove2.me/submissions/1b1fa95b-c420-41e1-84bc-660e66d22524

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {x : ℂ} {d : ℝ} (hd : 0 < d) (h : ‖x‖ ^ 2 = d⁻¹) (p : ℕ) : ‖x ^ p‖ = d ^ (-(p : ℝ) / 2) := by
  have h1 : (d ^ (-(1 : ℝ) / 2)) ^ 2 = d⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
    exact Real.rpow_neg_one d
  have h2 : 0 ≤ d ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hd.le _
  have hx : ‖x‖ = d ^ (-(1 : ℝ) / 2) := (pow_left_inj₀ (norm_nonneg _) h2 two_ne_zero).mp (h.trans h1.symm)
  rw [norm_pow, hx, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  congr 1
  ring
end PositivityTheory.Rg.Sw.WR.B
