-- Prove2me | solution 1 for P2M_QEC_Coding_HypergraphProduct_finrank_range_toLin__eq_rank_581f87e1a42a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:39:56.392505+00:00
-- url     : https://prove2.me/submissions/bd0a4c77-f303-45a1-8cd4-5cea939996f2

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {row col : Type u}
    [Field F]
    [Fintype row] [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    Module.finrank F (LinearMap.range (Matrix.toLin' M)) = M.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_toLin']
end QEC.Coding.HypergraphProduct
