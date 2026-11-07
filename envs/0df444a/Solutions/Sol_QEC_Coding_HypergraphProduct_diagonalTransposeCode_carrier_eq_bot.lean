-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.diagonalTransposeCode_carrier_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:42:32.138812+00:00
-- url     : https://prove2.me/submissions/d8f82f56-9a47-4c9c-9545-8c7e1f02901b

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Theorems.Thm_QEC_Coding_HypergraphProduct_transposeKernelCode_carrier_eq_bot_of_surjective

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
    (firstTransposeCode (diagonalData H)).carrier = ⊥ ∧
      (secondTransposeCode (diagonalData H)).carrier = ⊥ := by
  constructor <;>
    exact transposeKernelCode_carrier_eq_bot_of_surjective H hFull
end QEC.Coding.HypergraphProduct
