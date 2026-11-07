-- Prove2me | solution 1 for P2M_QEC_Coding_HypergraphProduct_finrank_range_wordLinearMapTranspose_toLin__eq_b35987ba4f3b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:44:18.834214+00:00
-- url     : https://prove2.me/submissions/504a0a54-5d5d-42e2-aa88-44cd562b2d56

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_wordLinearMapTranspose_toLin__eq_8ae563e58468
import Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_finrank_range_toLin__eq_rank_581f87e1a42a

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {row col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype row] [DecidableEq row]
    [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    Module.finrank F
        (LinearMap.range (wordLinearMapTranspose (Matrix.toLin' M))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [wordLinearMapTranspose_toLin'_eq,
    finrank_range_toLin'_eq_rank, finrank_range_toLin'_eq_rank,
    Matrix.rank_transpose]
end QEC.Coding.HypergraphProduct
