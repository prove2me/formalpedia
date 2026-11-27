-- Prove2me | solution 1 for Reformulated.AlgebraicInfinityType.InfinityType.isAlgebraic_iff_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:46.520668+00:00
-- url     : https://prove2.me/submissions/9eacf487-591c-4287-8405-f50c11ab5c85

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_AlgebraicInfinityType_InfinityType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Reformulated Reformulated.AlgebraicInfinityType
open NumberField
open Reformulated.AlgebraicInfinityType.InfinityType
variable {F : Type*} [Field F] {n : ℕ}
namespace Reformulated.AlgebraicInfinityType.InfinityType
theorem _root_.solution (t : InfinityType F n) :
    t.IsAlgebraic ↔ (t.twist ((1 - (n : ℂ)) / 2)).IsLAlgebraic := by
  simp only [IsAlgebraic, IsLAlgebraic, exponents, twist, Multiset.map_map,
    Multiset.forall_mem_map_iff, Function.comp]
  refine forall_congr' fun σ => forall₂_congr fun p _ => exists_congr fun m => ?_
  constructor <;> intro h <;> linear_combination h
end Reformulated.AlgebraicInfinityType.InfinityType
