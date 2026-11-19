-- Prove2me | solution 1 for QEC.Distillation.BK15.l2LogicalCoset_weight_enumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:11:27.407201+00:00
-- url     : https://prove2.me/submissions/4fed97fb-8343-416d-8f86-a43104eaa1f7

import Definitions.Def_QECert_FifteenWeights_WeightAggregation
import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (weight : Fin 16) :
    weightCount l2LogicalCosetWords weight.1 =
      if weight = 3 then 35 else if weight = 5 then 168 else
      if weight = 7 then 435 else if weight = 9 then 280 else
      if weight = 11 then 105 else if weight = 15 then 1 else 0 := by
  have hshift : Function.Injective (fun w : Word => w + allOnes) :=
    fun _ _ h => add_right_cancel h
  rw [weightCount, l2LogicalCosetWords, l2Words, Finset.image_image,
    Finset.filter_image, Finset.card_image_of_injective _
      (hshift.comp l2CoefficientMap_injective)]
  exact QEC.Distillation.BK15.CertifiedWeights.coset_coefficient_enumerator weight
end QEC.Distillation.BK15