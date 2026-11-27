-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r23b.PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:57.832225+00:00
-- url     : https://prove2.me/submissions/54508032-6a85-4480-9708-ca4575bc4b39

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowMulExpLeHalfExp
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r23b_pow_mul_exp_le_half_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r23b
namespace UpperTheory.Reformulated.B.P6.r23b
namespace PositivityTheory.Rg.Sw.Glob.DCalcDH
theorem _root_.solution :
    ∀ (N : ℕ) (a : ℝ), OfNat.ofNat (nat_lit 0) < a → ∃ (C : ℝ), OfNat.ofNat (nat_lit 0) ≤ C ∧ ∀ (x : ℝ), OfNat.ofNat (nat_lit 0) ≤ x → (OfNat.ofNat (nat_lit 1) + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / OfNat.ofNat (nat_lit 2) * x)) := by
  intro N a ha
  exact pow_mul_exp_le_half_exp N a ha
end PositivityTheory.Rg.Sw.Glob.DCalcDH
end UpperTheory.Reformulated.B.P6.r23b
