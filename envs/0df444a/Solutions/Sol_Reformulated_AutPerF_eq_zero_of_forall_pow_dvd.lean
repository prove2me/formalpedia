-- Prove2me | solution 1 for Reformulated.AutPerF.eq_zero_of_forall_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:16.204356+00:00
-- url     : https://prove2.me/submissions/9f4a6aa8-b760-4e60-9953-229bbd34dac9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
namespace Reformulated.AutPerF
theorem _root_.solution {A : Type*} [CommRing A] (q : A) [IsHausdorff (span {q}) A]
    {x : A} (h : ∀ n : ℕ, q ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := span {q}) (M := A) inferInstance _ fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  exact h n
end Reformulated.AutPerF
