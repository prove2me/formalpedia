-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_cycleFiberChainBoundary_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:06:40.464327+00:00
-- url     : https://prove2.me/submissions/9b7e658b-d452-45ed-8714-342833f9f5b3

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_apply
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_reindexWord
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (n : Nat) [NeZero n] [NeZero (n - 1)]
    (v : Word (ZMod 2) (ZMod n)) :
    HammingWeight (cycleFiberChainBoundary n v) ≤
      2 * HammingWeight v := by
  have hTwo : 2 ≤ n := by
    have hne : n - 1 ≠ 0 := NeZero.ne (n - 1)
    omega
  let shifted : Word (ZMod 2) (ZMod n) := fun i => v (i - 1)
  have hBoundary :
      cycleFiberChainBoundary n v = v + shifted := by
    funext i
    rw [cycleFiberChainBoundary_apply n hTwo]
    rfl
  have hShifted : HammingWeight shifted = HammingWeight v := by
    let e : ZMod n ≃ ZMod n := Equiv.addRight (1 : ZMod n)
    have hreindex := hammingWeight_reindexWord e v
    change HammingWeight shifted = HammingWeight v
    have hwords : shifted = reindexWord e v := by
      funext i
      change v (i - 1) = v (i + -1)
      rw [sub_eq_add_neg]
    rw [hwords]
    exact hreindex
  rw [hBoundary]
  calc
    HammingWeight (v + shifted) ≤
        HammingWeight v + HammingWeight shifted :=
      HammingWeight_add_le v shifted
    _ = 2 * HammingWeight v := by omega
end QEC.Coding.FiberBundle
