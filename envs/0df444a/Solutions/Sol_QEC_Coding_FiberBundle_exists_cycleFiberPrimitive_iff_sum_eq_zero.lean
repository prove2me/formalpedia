-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_cycleFiberPrimitive_iff_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:38.221184+00:00
-- url     : https://prove2.me/submissions/0edbb84a-a2fe-4000-842f-213aca8899bb

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_cycleFiberPrimitive
import Theorems.Thm_QEC_Coding_FiberBundle_sum_cycleFiberCoboundary_eq_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n)) :
    (∃ f, cycleFiberCoboundary n f = g) ↔
      (∑ j : ZMod n, g j) = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact sum_cycleFiberCoboundary_eq_zero n hn f
  · intro hg
    exact ⟨cycleFiberPrimitive n g,
      cycleFiberCoboundary_cycleFiberPrimitive n hn g hg⟩
end QEC.Coding.FiberBundle
