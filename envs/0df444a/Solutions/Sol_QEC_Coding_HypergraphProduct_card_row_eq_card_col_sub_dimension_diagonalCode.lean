-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.card_row_eq_card_col_sub_dimension_diagonalCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:47:46.677806+00:00
-- url     : https://prove2.me/submissions/3b006e83-578e-4ac8-9e27-22ca73c60084

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Theorems.Thm_QEC_Coding_HypergraphProduct_diagonalTransposeCode_dimensions_eq_zero
import Theorems.Thm_QEC_Coding_HypergraphProduct_first_dimension_add_rows_eq_cols_add_transpose_dimension


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card Row =
      Fintype.card Col - Dimension (firstCode (diagonalData H)) := by
  have hRelation :=
    first_dimension_add_rows_eq_cols_add_transpose_dimension (diagonalData H)
  have hTranspose := (diagonalTransposeCode_dimensions_eq_zero H hFull).1
  rw [hTranspose, add_zero] at hRelation
  omega
end QEC.Coding.HypergraphProduct
