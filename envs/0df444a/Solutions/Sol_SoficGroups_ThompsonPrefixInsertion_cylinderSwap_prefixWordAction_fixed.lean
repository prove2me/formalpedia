-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.cylinderSwap_prefixWordAction_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/31ab3024-92bc-49e8-9ac3-ceae5382a32a

import Mathlib
import Definitions.Def_NonSoficGroup

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
    (a b w : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a)
    (haw : ¬ a <+: w) (hwa : ¬ w <+: a)
    (hbw : ¬ b <+: w) (hwb : ¬ w <+: b) :
    PrefixWordAction (cylinderSwap a b hab hba) w w := by
  constructor
  · change
      PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) *
        leavittWordS w = leavittWordS w
    simp [PrefixCompression.transpositionValue,
      sub_mul, add_mul, mul_assoc,
      leavittWordT_mul_wordS_of_incomparable a w haw hwa,
      leavittWordT_mul_wordS_of_incomparable b w hbw hwb]
  · change
      leavittWordT w *
        PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) = leavittWordT w
    have hwa' : leavittWordT w * leavittWordS a = 0 :=
      leavittWordT_mul_wordS_of_incomparable w a hwa haw
    have hwb' : leavittWordT w * leavittWordS b = 0 :=
      leavittWordT_mul_wordS_of_incomparable w b hwb hbw
    have hwa'' (z : BinaryLeavitt) :
        leavittWordT w * (leavittWordS a * z) = 0 := by
      rw [← mul_assoc, hwa', zero_mul]
    have hwb'' (z : BinaryLeavitt) :
        leavittWordT w * (leavittWordS b * z) = 0 := by
      rw [← mul_assoc, hwb', zero_mul]
    unfold PrefixCompression.transpositionValue
    noncomm_ring [hwa', hwb', hwa'', hwb'']
end SoficGroups.ThompsonPrefixInsertion
