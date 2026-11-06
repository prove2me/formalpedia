-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.second_dimension_add_rows_eq_cols_add_transpose_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:42.391614+00:00
-- url     : https://prove2.me/submissions/5f6228f0-bd8d-49e7-9ee1-8df003cb58c5

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Theorems.Thm_QEC_Coding_HypergraphProduct_dimension_kernelCode_add_rank

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Dimension (secondCode D) + Fintype.card rowTwo =
      Fintype.card colTwo + Dimension (secondTransposeCode D) := by
  have hSecond := dimension_kernelCode_add_rank D.second
  have hTranspose := dimension_kernelCode_add_rank D.second.transpose
  rw [Matrix.rank_transpose] at hTranspose
  change
    Dimension (parityCheckKernelCode (Matrix.toLin' D.second)) +
        Fintype.card rowTwo =
      Fintype.card colTwo +
        Dimension (parityCheckKernelCode (Matrix.toLin' D.second.transpose))
  omega
end QEC.Coding.HypergraphProduct
