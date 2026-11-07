-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.mapRows_eq_zero_on_rows_of_vanish_on_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:29.258413+00:00
-- url     : https://prove2.me/submissions/d31ba3f3-4eea-4a72-904c-f0520ec39475

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (T : Word F W →ₗ[F] Word F W) (A B : Finset W)
    (hVanish : ∀ y : Word F W, (∀ j ∈ A, y j = 0) → T y = 0)
    (x : Matrix W W F) (hx : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    ∀ i ∈ B, mapRows T x i = 0 := by
  intro i hi
  exact hVanish (x i) (hx i hi)
end QEC.Coding.ProductExpansion
