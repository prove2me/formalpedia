-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GI.abs_pow_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:27.991806+00:00
-- url     : https://prove2.me/submissions/b188e116-1ab4-41e4-886c-c10d920b20c4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G.GI
theorem _root_.solution (b : ℝ) (hb : 0 < b) (k : ℕ) :
    Integrable fun x : ℝ => |x| ^ k * Real.exp (-b * x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  simp_rw [Real.rpow_natCast] at h
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
end PositivityTheory.Rg.Sw.WR.G.GI
