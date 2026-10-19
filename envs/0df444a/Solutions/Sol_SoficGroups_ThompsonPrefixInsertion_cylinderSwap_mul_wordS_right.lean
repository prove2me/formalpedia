-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.cylinderSwap_mul_wordS_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/75480b47-15ec-4fd9-bf64-c1f67a417f25

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ThompsonPrefixInsertion
namespace SoficGroups.ThompsonPrefixInsertion
theorem _root_.solution
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    (↑(cylinderSwap a b hab hba) : BinaryLeavitt) *
        leavittWordS b = leavittWordS a := by
  change
    PrefixCompression.transpositionValue
        (leavittWordS a) (leavittWordT a)
        (leavittWordS b) (leavittWordT b) *
      leavittWordS b = leavittWordS a
  simp [PrefixCompression.transpositionValue, sub_mul, add_mul, mul_assoc,
    leavittWordT_mul_wordS_self,
    leavittWordT_mul_wordS_of_incomparable a b hab hba]
end SoficGroups.ThompsonPrefixInsertion
