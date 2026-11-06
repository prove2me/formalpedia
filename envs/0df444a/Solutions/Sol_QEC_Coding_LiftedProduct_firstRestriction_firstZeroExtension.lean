-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:53:22.730178+00:00
-- url     : https://prove2.me/submissions/53520a11-3e14-4b65-b399-e66018f1e416

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
    (firstRestriction D).comp (firstZeroExtension D) = LinearMap.id := by
  ext x i
  rfl
end QEC.Coding.LiftedProduct
