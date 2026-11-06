-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.binaryCSSCode_finrank_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:46:51.079316+00:00
-- url     : https://prove2.me/submissions/81169fac-0d44-4e5e-a51d-1f43d1d78f08

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Theorems.Thm_QEC_Coding_ChainComplexData_binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology


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
    Module.finrank Complex (binaryCSSCode D).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) (chainComplex D).middleHomology := by
  exact
    QEC.Coding.ChainComplexData.binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
      (chainComplex D)
end QEC.Coding.LiftedProduct
