-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.xCheckWeight_diagonal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:38:54.829212+00:00
-- url     : https://prove2.me/submissions/6818c4ab-3524-4c96-85d2-293a7f7f20e5

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Theorems.Thm_QEC_Coding_HypergraphProduct_xCheckWeight_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2)) (r : Row) (c : Col) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 (diagonalData H))
          (Pi.single (r, c) 1)) =
      rowWeight H r + columnWeight H c := by
  exact xCheckWeight_eq (diagonalData H) r c
end QEC.Coding.HypergraphProduct
