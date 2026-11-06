-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.binaryCSSCode_stabilizer_isSourceValidBinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:46:43.554206+00:00
-- url     : https://prove2.me/submissions/c77af86c-51d9-4407-a276-5c78b2955e06

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by
  exact (chainComplex D).binaryCSSCode_stabilizer_isSourceValidBinary
end QEC.Coding.LiftedProduct
