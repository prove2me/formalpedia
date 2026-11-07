-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_partition_link
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:55:47.597917+00:00
-- url     : https://prove2.me/submissions/8a5355d8-018c-439b-9e4b-9ed79b391907

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_support_inter_link

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) :
    HammingWeight x = HammingWeight (X.localRestriction vertex x) +
      (hammingSupport x \ Finset.univ.image (X.link vertex)).card := by
  have h := Finset.card_inter_add_card_sdiff
    (hammingSupport x) (Finset.univ.image (X.link vertex))
  rw [X.support_inter_link vertex x,
    Finset.card_image_of_injective _ (X.link_injective vertex)] at h
  exact h.symm
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
