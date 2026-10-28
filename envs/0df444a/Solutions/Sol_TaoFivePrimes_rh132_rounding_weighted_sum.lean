-- Prove2me | solution 1 for TaoFivePrimes.rh132_rounding_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:23:20.356186+00:00
-- url     : https://prove2.me/submissions/9dbda066-8f69-4293-bee7-2ea748678752

import Definitions.Def_TaoFivePrimes_RH132RoundingSpec
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset

namespace Direct132RoundedSum

noncomputable def rationalBound (n : ℕ) : ℚ :=
  if n<23 then 1/10^14 else if n<26 then 1/10^15
  else if n<30 then 1/10^19 else if n<35 then 1/10^23
  else if n<40 then 1/10^30 else 1/10^37

lemma rationalBound_cast (n : ℕ) :
    (rationalBound n:ℝ)=RH132RoundingSpec.bound n := by
  unfold rationalBound RH132RoundingSpec.bound
  split_ifs <;> norm_num

end Direct132RoundedSum

theorem solution :
    (∑ n ∈ range 60, ((2/10^34:ℝ)+RH132RoundingSpec.bound n)*(31/10:ℝ)^n) ≤ 4/1000 := by
  have hq : (∑ n ∈ range 60,
      ((2/10^34:ℚ)+Direct132RoundedSum.rationalBound n)*(31/10:ℚ)^n) ≤ 4/1000 := by
    decide +kernel
  have hr : ((∑ n ∈ range 60,
      ((2/10^34:ℚ)+Direct132RoundedSum.rationalBound n)*(31/10:ℚ)^n : ℚ):ℝ) ≤
      ((4/1000:ℚ):ℝ) := by exact_mod_cast hq
  simp only [Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_add,
    Rat.cast_div,Rat.cast_ofNat,Direct132RoundedSum.rationalBound_cast] at hr
  exact hr
