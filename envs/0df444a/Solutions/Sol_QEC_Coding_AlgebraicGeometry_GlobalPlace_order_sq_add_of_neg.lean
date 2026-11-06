-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.order_sq_add_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:12:02.058228+00:00
-- url     : https://prove2.me/submissions/8c03d87b-20b4-4758-9b6f-286d0de45be8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (Q : GlobalPlace k L) (y : L)
    (hy : Q.order y < 0) : Q.order (y ^ 2 + y) = 2 * Q.order y := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    simp [order] at hy
  have hv : Q.valuation y = WithZero.exp (-Q.order y) := by
    simp only [order, neg_neg]
    exact (WithZero.exp_log (Q.valuation.ne_zero_iff.mpr hy0)).symm
  have hv2 : Q.valuation (y ^ 2) = WithZero.exp (-2 * Q.order y) := by
    rw [map_pow, hv, ← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hlt : Q.valuation y < Q.valuation (y ^ 2) := by
    rw [hv, hv2]
    exact WithZero.exp_lt_exp.mpr (by omega)
  change -WithZero.log (Q.valuation (y ^ 2 + y)) = _
  rw [Q.valuation.map_add_eq_of_lt_left hlt, hv2, WithZero.log_exp]
  ring
end QEC.Coding.AlgebraicGeometry.GlobalPlace
