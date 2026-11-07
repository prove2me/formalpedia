-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.transposeKernelCode_carrier_eq_bot_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:40:08.829204+00:00
-- url     : https://prove2.me/submissions/e7fe2590-2940-41a9-a2c6-07cbe97a0f1b

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Theorems.Thm_QEC_Coding_HypergraphProduct_ker_wordLinearMapTranspose_eq_bot_of_surjective
import Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_wordLinearMapTranspose_toLin__eq_8ae563e58468


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {Row Col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col F) (hFull : Function.Surjective (Matrix.toLin' H)) :
    (parityCheckKernelCode (Matrix.toLin' H.transpose)).carrier = ⊥ := by
  change LinearMap.ker (Matrix.toLin' H.transpose) = ⊥
  rw [← wordLinearMapTranspose_toLin'_eq]
  exact ker_wordLinearMapTranspose_eq_bot_of_surjective
    (Matrix.toLin' H) hFull
end QEC.Coding.HypergraphProduct
