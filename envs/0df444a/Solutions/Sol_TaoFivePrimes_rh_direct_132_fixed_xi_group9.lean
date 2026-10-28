-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_fixed_xi_group9
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:53:48.43309+00:00
-- url     : https://prove2.me/submissions/670ef8eb-fd95-4f68-8a40-19d30266c00d

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (45+j.val) = (RHDirect132FixedXi.xiQ (45+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (45+j.val) := by
  intro j
  fin_cases j
  all_goals
    constructor
    · norm_num [RHDirect132FixedXi.xiC,RHDirect132FixedXi.xiQ,
        RHDirect132FixedXi.lambdaC,RHDirect132FixedXi.lambdaQ,
        RHDirect132FastNumerator.fixed,TaoFivePrimes_RHDirect132FixedComponents,
        Complex.I_sq,Complex.I_pow_three] <;> ring_nf <;>
        norm_num [Complex.I_pow_eq_pow_mod,Complex.I_sq,Complex.I_pow_three] <;>
        norm_num only [Nat.reduceMod,Complex.I_sq,Complex.I_pow_three]
    · unfold RHDirect132FixedXi.roundingHolds
      decide +kernel
