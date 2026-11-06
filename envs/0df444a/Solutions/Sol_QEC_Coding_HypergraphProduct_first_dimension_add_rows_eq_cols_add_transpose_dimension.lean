-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.first_dimension_add_rows_eq_cols_add_transpose_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:41.478484+00:00
-- url     : https://prove2.me/submissions/df8c89ab-f9db-4bc3-9da6-ff52dd9f1e97

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
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Dimension (firstCode D) + Fintype.card rowOne =
      Fintype.card colOne + Dimension (firstTransposeCode D) := by
  have hFirst := dimension_kernelCode_add_rank D.first
  have hTranspose := dimension_kernelCode_add_rank D.first.transpose
  rw [Matrix.rank_transpose] at hTranspose
  change
    Dimension (parityCheckKernelCode (Matrix.toLin' D.first)) +
        Fintype.card rowOne =
      Fintype.card colOne +
        Dimension (parityCheckKernelCode (Matrix.toLin' D.first.transpose))
  omega
end QEC.Coding.HypergraphProduct
