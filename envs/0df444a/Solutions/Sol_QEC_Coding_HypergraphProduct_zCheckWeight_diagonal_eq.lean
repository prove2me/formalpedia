-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.zCheckWeight_diagonal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:39:22.685658+00:00
-- url     : https://prove2.me/submissions/eb8058c8-60d8-469c-beb0-a02a7c8f3748

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Theorems.Thm_QEC_Coding_HypergraphProduct_zCheckWeight_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2)) (c : Col) (r : Row) :
    HammingWeight (boundary2 (diagonalData H) (Pi.single (c, r) 1)) =
      rowWeight H r + columnWeight H c := by
  exact zCheckWeight_eq (diagonalData H) c r
end QEC.Coding.HypergraphProduct
