-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.binaryAlgebraicCSSMinimumDistance_of_sector_minima
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:46:52.163614+00:00
-- url     : https://prove2.me/submissions/82f33bb3-b8c8-4ad2-a4b4-12f434cac172

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Theorems.Thm_QEC_Coding_algebraicCSSMinimumDistance_of_sector_minima


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
    (D : Data (ZMod 2) G aRow aCol bRow bCol)
    {dX dZ : Nat}
    (hX : BinaryPureXMinimumDistance D dX)
    (hZ : BinaryPureZMinimumDistance D dZ) :
    BinaryAlgebraicCSSMinimumDistance D (min dX dZ) := by
  exact algebraicCSSMinimumDistance_of_sector_minima hX hZ
end QEC.Coding.LiftedProduct
