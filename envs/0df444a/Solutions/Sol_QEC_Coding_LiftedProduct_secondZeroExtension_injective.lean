-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.secondZeroExtension_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:47:07.564905+00:00
-- url     : https://prove2.me/submissions/e9a5a49c-4e33-4a15-b8ce-4da4faba804c

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    Function.Injective (secondZeroExtension D) := by
  intro x y hxy
  funext i
  exact congrFun hxy (Sum.inr i)
end QEC.Coding.LiftedProduct
