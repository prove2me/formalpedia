-- Prove2me | solution 1 for P2M_Formalism_IncomingBounds_weight_identities__d3acf4a5cb10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:34.323898+00:00
-- url     : https://prove2.me/submissions/7e11aad2-6c1a-4149-b044-aad3e777a43e

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
private theorem one_add_mul_le_one_add_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : 1 + k * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg hx hx),
      mul_le_mul_of_nonneg_right ih (by linarith : (0:ℝ) ≤ 1 + x)]
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : WeightIdentities := by
  intro l hl i hi
  unfold rho gam
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hB : 0 < (l : ℝ) - 1 := by linarith
  have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
  have hr : ((l : ℝ) - 1) * (1 / ((l : ℝ) - 1)) = 1 := mul_one_div_cancel hB.ne'
  have hP : (l : ℝ) ^ i * ((l : ℝ) ^ i)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero i hl0)
  have hPL : (l : ℝ) ≤ (l : ℝ) ^ i := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ]
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le j
    rw [show (1 : ℝ) + ((l : ℝ) - 1) = l by ring] at hb
    have hj : (1 : ℝ) ≤ (l : ℝ) ^ j := by
      nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hB.le]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℝ) * hP - ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr +
      (1 / ((l : ℝ) - 1)) * hq
  · intro B
    linear_combination (B / 2) * hP - B * ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr +
      B * (1 / ((l : ℝ) - 1)) * hq
  · linear_combination (l : ℝ) ^ i * ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr -
      (l : ℝ) ^ i * (1 / ((l : ℝ) - 1)) * hq
  · have e : ((l : ℝ) ^ i + 1) * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)) - 1 =
        (((l : ℝ) ^ i + 1) * l - ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1)) := by
      linear_combination hq
    rw [e]
    refine mul_nonneg ?_ (one_div_pos.2 hA).le
    nlinarith [mul_le_mul_of_nonneg_right hPL (by linarith : (0 : ℝ) ≤ l)]
end Formalism.IncomingBounds
