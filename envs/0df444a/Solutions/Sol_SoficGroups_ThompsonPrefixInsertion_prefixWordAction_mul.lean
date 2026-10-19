-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.prefixWordAction_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/ddf98ec6-bc97-45fc-aab5-2fc0959d825d

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
    {g h : BinaryLeavittˣ} {a b c : List (Fin 2)}
    (hg : PrefixWordAction g b c)
    (hh : PrefixWordAction h a b) :
    PrefixWordAction (g * h) a c := by
  constructor
  · change
      ((g : BinaryLeavitt) * (h : BinaryLeavitt)) *
        leavittWordS a = leavittWordS c
    rw [mul_assoc, hh.prefixing, hg.prefixing]
  · change
      leavittWordT a *
        ((↑(h⁻¹) : BinaryLeavitt) *
          (↑(g⁻¹) : BinaryLeavitt)) = leavittWordT c
    rw [← mul_assoc, hh.deletion, hg.deletion]
end SoficGroups.ThompsonPrefixInsertion
