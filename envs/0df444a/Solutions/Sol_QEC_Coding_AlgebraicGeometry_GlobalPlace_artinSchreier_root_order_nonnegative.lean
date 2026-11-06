-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:31:05.23472+00:00
-- url     : https://prove2.me/submissions/c16c0f44-28b2-47b6-9faa-b516ef613ec3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_sq_add_of_neg

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (Q : GlobalPlace k L)
    (y : L) (ha : 0 ≤ Q.order (y ^ 2 + y)) : 0 ≤ Q.order y := by
  by_contra hn
  have hneg : Q.order y < 0 := by omega
  rw [Q.order_sq_add_of_neg y hneg] at ha
  omega
end QEC.Coding.AlgebraicGeometry.GlobalPlace
