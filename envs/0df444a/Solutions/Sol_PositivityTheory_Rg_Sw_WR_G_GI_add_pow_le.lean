-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GI.add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:30.615455+00:00
-- url     : https://prove2.me/submissions/2687ed58-fe85-4520-b22c-d8a74824e3aa

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
theorem _root_.solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) : (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ k ≤ (2 * b) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * b ^ k := mul_pow 2 b k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg ha k
          gcongr; linarith
  · calc (a + b) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow 2 a k
      _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
          have := pow_nonneg hb k
          gcongr; linarith
end PositivityTheory.Rg.Sw.WR.G.GI
