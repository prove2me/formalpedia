-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.rpow_le_balancingLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:31:09.637645+00:00
-- url     : https://prove2.me/submissions/6182de7b-d4ea-4919-a3e2-ff77a88373db

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution (alpha : ℝ) (q : Nat) :
    (q : ℝ) ^ balancingExponent alpha ≤ balancingLift alpha q := by
  calc
    (q : ℝ) ^ balancingExponent alpha ≤
        (Nat.ceil ((q : ℝ) ^ balancingExponent alpha) : Nat) :=
      Nat.le_ceil _
    _ ≤ balancingLift alpha q := by
      exact_mod_cast Nat.le_max_right 2
        (Nat.ceil ((q : ℝ) ^ balancingExponent alpha))
end QEC.Coding.ExpanderCodes.PK20
