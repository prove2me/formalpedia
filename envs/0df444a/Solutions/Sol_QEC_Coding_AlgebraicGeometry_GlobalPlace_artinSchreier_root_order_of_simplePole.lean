-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_of_simplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:35:45.405537+00:00
-- url     : https://prove2.me/submissions/f4dba82a-1fea-4cfc-b423-cfac32cfc69b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_sq_add_of_neg
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution [Algebra K L]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (a : K) (y : L)
    (e : ℕ) (he0 : 0 < e) (he2 : e ≤ 2)
    (hy : y ^ 2 + y = algebraMap K L a)
    (horder : Q.order (algebraMap K L a) = (e : ℤ) * P.order a)
    (ha : P.order a = -1) : e = 2 ∧ Q.order y = -1 := by
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp [order] at ha
  have hmap0 : algebraMap K L a ≠ 0 :=
    by simpa only [map_zero] using (algebraMap K L).injective.ne ha0
  have hrhs : Q.order (y ^ 2 + y) = -(e : ℤ) := by
    rw [hy, horder, ha]
    ring
  have hneg : Q.order y < 0 := by
    by_contra hn
    have hregular : Q.RegularAt y := by
      by_cases hzero : y = 0
      · simp [hzero, RegularAt]
      · exact (Q.regularAt_iff_order_nonnegative hzero).mpr (by omega)
    have hmem := (Q.regularAt_iff_mem_valuationRing y).mp hregular
    have hsum := Q.valuationRing.add_mem
      (y ^ 2) y (Q.valuationRing.pow_mem hmem 2) hmem
    rw [hy] at hsum
    have hnonneg := (Q.regularAt_iff_order_nonnegative hmap0).mp
      ((Q.regularAt_iff_mem_valuationRing _).mpr hsum)
    rw [horder, ha] at hnonneg
    omega
  rw [Q.order_sq_add_of_neg y hneg] at hrhs
  omega
end QEC.Coding.AlgebraicGeometry.GlobalPlace
