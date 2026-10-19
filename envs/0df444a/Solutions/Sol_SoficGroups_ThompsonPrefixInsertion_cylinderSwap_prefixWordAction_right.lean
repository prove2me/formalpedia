-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.cylinderSwap_prefixWordAction_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/f55caea5-5b32-48b1-926e-3ed8c12b254e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_cylinderSwap_mul_wordS_right

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
open SoficGroups.ThompsonPrefixInsertion
open scoped commutatorElement
namespace SoficGroups.ThompsonPrefixInsertion
theorem _root_.solution
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    PrefixWordAction (cylinderSwap a b hab hba) b a := by
  constructor
  · exact cylinderSwap_mul_wordS_right a b hab hba
  · change
      leavittWordT b *
        PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) = leavittWordT a
    have hbb : leavittWordT b * leavittWordS b = 1 :=
      leavittWordT_mul_wordS_self b
    have hba' : leavittWordT b * leavittWordS a = 0 :=
      leavittWordT_mul_wordS_of_incomparable b a hba hab
    have hbb' (z : BinaryLeavitt) :
        leavittWordT b * (leavittWordS b * z) = z := by
      rw [← mul_assoc, hbb, one_mul]
    have hba'' (z : BinaryLeavitt) :
        leavittWordT b * (leavittWordS a * z) = 0 := by
      rw [← mul_assoc, hba', zero_mul]
    unfold PrefixCompression.transpositionValue
    noncomm_ring [hbb, hba', hbb', hba'']
end SoficGroups.ThompsonPrefixInsertion
