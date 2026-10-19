-- Prove2me | solution 1 for SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_conjugate_of_prefixWordAction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/01471042-7801-4948-8306-a05cf1349e3b

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
    (g : BinaryLeavittˣ) (a b : List (Fin 2))
    (h : PrefixWordAction g a b) (u : BinaryLeavittˣ) :
    g * prefixInsertionHom a u * g⁻¹ = prefixInsertionHom b u := by
  apply Units.ext
  change
    (g : BinaryLeavitt) *
        (↑(prefixInsertionHom a u) : BinaryLeavitt) *
          (↑(g⁻¹) : BinaryLeavitt) =
      (↑(prefixInsertionHom b u) : BinaryLeavitt)
  rw [prefixInsertionHom_val, prefixInsertionHom_val]
  change
    (g : BinaryLeavitt) *
        (leavittWordS a * (u : BinaryLeavitt) * leavittWordT a +
          (1 - leavittWordS a * leavittWordT a)) *
          (↑(g⁻¹) : BinaryLeavitt) =
      leavittWordS b * (u : BinaryLeavitt) * leavittWordT b +
        (1 - leavittWordS b * leavittWordT b)
  have hunit :
      (g : BinaryLeavitt) * (↑(g⁻¹) : BinaryLeavitt) = 1 :=
    g.val_inv
  calc
    (g : BinaryLeavitt) *
        (leavittWordS a * (u : BinaryLeavitt) * leavittWordT a +
          (1 - leavittWordS a * leavittWordT a)) *
          (↑(g⁻¹) : BinaryLeavitt) =
        ((g : BinaryLeavitt) * leavittWordS a) *
            (u : BinaryLeavitt) *
            (leavittWordT a * (↑(g⁻¹) : BinaryLeavitt)) +
          ((g : BinaryLeavitt) * (↑(g⁻¹) : BinaryLeavitt) -
            ((g : BinaryLeavitt) * leavittWordS a) *
              (leavittWordT a * (↑(g⁻¹) : BinaryLeavitt))) := by
          simp only [CharTwo.sub_eq_add]
          noncomm_ring
    _ = leavittWordS b * (u : BinaryLeavitt) * leavittWordT b +
          (1 - leavittWordS b * leavittWordT b) := by
          rw [h.prefixing, h.deletion, hunit]
end SoficGroups.ThompsonPrefixInsertion
