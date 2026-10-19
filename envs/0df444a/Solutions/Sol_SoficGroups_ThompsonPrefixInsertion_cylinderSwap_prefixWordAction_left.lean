-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.cylinderSwap_prefixWordAction_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/5b1e4ef5-43f2-48fc-b0cc-2b5b1e34d626

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
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    PrefixWordAction (cylinderSwap a b hab hba) a b := by
  constructor
  · change
      PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) *
        leavittWordS a = leavittWordS b
    simp [PrefixCompression.transpositionValue,
      sub_mul, add_mul, mul_assoc,
      leavittWordT_mul_wordS_self,
      leavittWordT_mul_wordS_of_incomparable b a hba hab]
  · change
      leavittWordT a *
        PrefixCompression.transpositionValue
          (leavittWordS a) (leavittWordT a)
          (leavittWordS b) (leavittWordT b) = leavittWordT b
    have haa : leavittWordT a * leavittWordS a = 1 :=
      leavittWordT_mul_wordS_self a
    have hab' : leavittWordT a * leavittWordS b = 0 :=
      leavittWordT_mul_wordS_of_incomparable a b hab hba
    have haa' (z : BinaryLeavitt) :
        leavittWordT a * (leavittWordS a * z) = z := by
      rw [← mul_assoc, haa, one_mul]
    have hab'' (z : BinaryLeavitt) :
        leavittWordT a * (leavittWordS b * z) = 0 := by
      rw [← mul_assoc, hab', zero_mul]
    unfold PrefixCompression.transpositionValue
    noncomm_ring [haa, hab', haa', hab'']
end SoficGroups.ThompsonPrefixInsertion
