-- Prove2me | solution 1 for QEC.Coding.FiberBundle.sum_cycleFiberCoboundary_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:23:44.221953+00:00
-- url     : https://prove2.me/submissions/83b04cf4-8a4b-4c8c-89ec-132a92720380

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n)) :
    (∑ j : ZMod n, cycleFiberCoboundary n f j) = 0 := by
  simp_rw [cycleFiberCoboundary_apply n hn]
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ j : ZMod n, f (j + 1)) = ∑ j : ZMod n, f j := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
      (fun j => f (j + 1)) f (by intro j; rfl)
  rw [hshift]
  let s := ∑ j : ZMod n, f j
  change s + s = 0
  calc
    s + s = s + (-s) := by rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel s
end QEC.Coding.FiberBundle
