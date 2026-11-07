-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_multipleRotation_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:48:57.224778+00:00
-- url     : https://prove2.me/submissions/0edebc29-b7ae-49db-90d4-279045cb640c

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (ell : Nat) [NeZero ell] (k : Fin ell) :
    fiberResidue ell (multipleRotation ell k) = 0 := by
  rw [fiberResidue, multipleRotation]
  change ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)
    (((k.val * ell : Nat) : ZMod (ell * ell))) = 0
  rw [ZMod.castHom_apply,
    ZMod.cast_natCast (R := ZMod ell) (dvd_mul_right ell ell)]
  rw [Nat.cast_mul]
  rw [ZMod.natCast_self, mul_zero]
end QEC.Coding.FiberBundle
