-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.firstZeroExtension_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:47:06.605445+00:00
-- url     : https://prove2.me/submissions/d1ca86a9-eac9-4202-bc6e-8f3e36d8e67d

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
    Function.Injective (firstZeroExtension D) := by
  intro x y hxy
  funext i
  exact congrFun hxy (Sum.inl i)
end QEC.Coding.LiftedProduct
