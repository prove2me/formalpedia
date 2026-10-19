-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.prefixWordAction_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/00c8ffea-4d22-4bad-ae08-90ac4d5a7991

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution {g : BinaryLeavittˣ}
    {a b : List (Fin 2)} (h : PrefixWordAction g a b) :
    PrefixWordAction g⁻¹ b a := by
  have hunit : (↑g⁻¹ : BinaryLeavitt) * (g : BinaryLeavitt) = 1 := by
    simp
  constructor
  · calc
      (↑g⁻¹ : BinaryLeavitt) * leavittWordS b =
          (↑g⁻¹ : BinaryLeavitt) *
            ((g : BinaryLeavitt) * leavittWordS a) := by
              rw [h.prefixing]
      _ = ((↑g⁻¹ : BinaryLeavitt) * (g : BinaryLeavitt)) *
          leavittWordS a := by rw [mul_assoc]
      _ = leavittWordS a := by rw [hunit, one_mul]
  · change leavittWordT b * (g : BinaryLeavitt) = leavittWordT a
    calc
      leavittWordT b * (g : BinaryLeavitt) =
          (leavittWordT a * (↑g⁻¹ : BinaryLeavitt)) *
            (g : BinaryLeavitt) := by rw [h.deletion]
      _ = leavittWordT a *
          ((↑g⁻¹ : BinaryLeavitt) * (g : BinaryLeavitt)) := by
            rw [mul_assoc]
      _ = leavittWordT a := by rw [hunit, mul_one]
end SoficGroups.ThompsonFLocalWitness
