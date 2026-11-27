-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r22b.PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:51.243248+00:00
-- url     : https://prove2.me/submissions/2cd63d79-a73b-483e-93a4-f54639327010

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_OneAddPowMulExpLe
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r22b_one_add_pow_mul_exp_neg_le_of_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r22b
namespace UpperTheory.Reformulated.B.P6.r22b
namespace PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates
theorem _root_.solution :
    ∀ (K : ℕ) {β : ℝ}, OfNat.ofNat (nat_lit 0) < β → ∃ (M : ℝ), ∀ (s : ℝ), OfNat.ofNat (nat_lit 0) ≤ s → (OfNat.ofNat (nat_lit 1) + s) ^ K * Real.exp (-β * s) ≤ M := by
  intro K β hβ
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have ha : 0 < β / ((K : ℝ) + 1) := div_pos hβ hK
  have hKa : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ β := by
    have e : ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) = β := by field_simp
    have : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) ha.le
    linarith
  exact ⟨_, fun s hs => one_add_pow_mul_exp_neg_le_of_mul_le K ha hKa hs⟩
end PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates
end UpperTheory.Reformulated.B.P6.r22b
