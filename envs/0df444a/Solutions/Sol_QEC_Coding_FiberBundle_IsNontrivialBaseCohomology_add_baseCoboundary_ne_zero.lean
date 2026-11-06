-- Prove2me | solution 1 for QEC.Coding.FiberBundle.IsNontrivialBaseCohomology.add_baseCoboundary_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:53:18.078284+00:00
-- url     : https://prove2.me/submissions/f2dafa8d-a8d3-48ac-99cf-b9e7d703bfbe

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
namespace IsNontrivialBaseCohomology
theorem _root_.solution
    {r : Nat}
    (baseSample : RandomBase.Sample r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    x + baseCoboundary baseSample t ≠ 0 := by
  intro hzero
  apply hx t
  funext b
  have hb :
      x b + baseCoboundary baseSample t b = 0 :=
    congrFun hzero b
  calc
    x b = -(baseCoboundary baseSample t b) :=
      eq_neg_of_add_eq_zero_left hb
    _ = baseCoboundary baseSample t b :=
      ZMod.neg_eq_self_mod_two _
end IsNontrivialBaseCohomology
end QEC.Coding.FiberBundle
