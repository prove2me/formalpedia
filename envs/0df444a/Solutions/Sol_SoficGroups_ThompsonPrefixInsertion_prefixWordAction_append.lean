-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.prefixWordAction_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/f0efd7e4-7e5a-498d-a85d-9532721cbb99

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
    {g : BinaryLeavittˣ} {a b : List (Fin 2)}
    (h : PrefixWordAction g a b) (r : List (Fin 2)) :
    PrefixWordAction g (a ++ r) (b ++ r) := by
  constructor
  · rw [leavittWordS_append, leavittWordS_append, ← mul_assoc, h.prefixing]
  · rw [leavittWordT_append, leavittWordT_append, mul_assoc, h.deletion]
end SoficGroups.ThompsonPrefixInsertion
