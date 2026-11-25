-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:24.683143+00:00
-- url     : https://prove2.me/submissions/7f987846-a6f3-4de0-9503-fdc68fca3ac2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisMore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (c : ℝ) (hc : 0 < c) (k : ℕ) : ∃ K : ℝ, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ (2 * k) * Real.exp (-(c * s ^ 2)) ≤ K := by
  refine ⟨4 ^ k * (1 + (k.factorial : ℝ) / c ^ k), fun s hs => ?_⟩
  have hpow : (1 + s) ^ (2 * k) ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ (2 * k) ≤ 2 ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 4 ^ k := by rw [pow_mul]; norm_num
        _ ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
          have : 0 ≤ s ^ (2 * k) := by positivity
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) k]
    · calc (1 + s) ^ (2 * k) ≤ (2 * s) ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 4 ^ k * s ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
        _ ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
          have : 0 ≤ (4:ℝ) ^ k := by positivity
          nlinarith
  have hexp : s ^ (2 * k) ≤ (k.factorial : ℝ) / c ^ k * Real.exp (c * s ^ 2) := by
    have h1 := Real.pow_div_factorial_le_exp (c * s ^ 2) (by positivity) k
    have hck : 0 < c ^ k := pow_pos hc k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hf] at h1
    rw [pow_mul, div_mul_eq_mul_div, le_div_iff₀ hck]
    calc (s ^ 2) ^ k * c ^ k = (c * s ^ 2) ^ k := by ring
      _ ≤ Real.exp (c * s ^ 2) * k.factorial := h1
      _ = k.factorial * Real.exp (c * s ^ 2) := by ring
  have he : 0 < Real.exp (-(c * s ^ 2)) := Real.exp_pos _
  have hee : Real.exp (c * s ^ 2) * Real.exp (-(c * s ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h1le : 1 ≤ Real.exp (c * s ^ 2) := Real.one_le_exp (by positivity)
  calc (1 + s) ^ (2 * k) * Real.exp (-(c * s ^ 2))
      ≤ 4 ^ k * (1 + s ^ (2 * k)) * Real.exp (-(c * s ^ 2)) := mul_le_mul_of_nonneg_right hpow he.le
    _ ≤ 4 ^ k * (Real.exp (c * s ^ 2) + (k.factorial : ℝ) / c ^ k * Real.exp (c * s ^ 2)) *
          Real.exp (-(c * s ^ 2)) := by gcongr
    _ = 4 ^ k * (1 + (k.factorial : ℝ) / c ^ k) * (Real.exp (c * s ^ 2) * Real.exp (-(c * s ^ 2))) := by ring
    _ = 4 ^ k * (1 + (k.factorial : ℝ) / c ^ k) := by rw [hee, mul_one]
end PositivityTheory.Rg.Sw.WR.D
