-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.artinSchreier_root_order_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:52.758288+00:00
-- url     : https://prove2.me/submissions/534a5687-6783-4d19-b0b6-f34ef74c2979

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_of_simplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_nonnegative

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
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    Q.order y = -1 ∨ 0 ≤ Q.order y := by
  rcases ha with hpole | hregular
  · exact Or.inl (P.artinSchreier_root_order_of_simplePole Q a y e
      he0 he2 hy horder hpole).2
  · apply Or.inr
    apply Q.artinSchreier_root_order_nonnegative
    rw [hy, horder]
    exact mul_nonneg (Nat.cast_nonneg e) hregular
end QEC.Coding.AlgebraicGeometry.GlobalPlace
