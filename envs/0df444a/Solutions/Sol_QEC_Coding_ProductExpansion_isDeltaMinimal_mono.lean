-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.isDeltaMinimal_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:54.524362+00:00
-- url     : https://prove2.me/submissions/5530526a-6dda-4c80-830c-8a9cf8024167

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
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) {delta delta' : ℝ}
    (hdelta : delta ≤ delta')
    (hMinimal : IsDeltaMinimal h h' delta x) :
    IsDeltaMinimal h h' delta' x := by
  rcases hMinimal with ⟨hRows, hCols⟩
  constructor
  · intro i c hc
    exact (hRows i c hc).trans (add_le_add_right hdelta _)
  · intro j c hc
    exact (hCols j c hc).trans (add_le_add_right hdelta _)
end QEC.Coding.ProductExpansion
