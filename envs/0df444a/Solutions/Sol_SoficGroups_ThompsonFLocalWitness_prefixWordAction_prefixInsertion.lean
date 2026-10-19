-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.prefixWordAction_prefixInsertion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/2c50090f-2e10-46b1-b02c-3ee4b46d7c26

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution {g : BinaryLeavittˣ}
    {a b : List (Fin 2)} (l : List (Fin 2))
    (h : PrefixWordAction g a b) :
    PrefixWordAction (prefixInsertionHom l g) (l ++ a) (l ++ b) := by
  have hl := leavittWordT_mul_wordS_self l
  have hl' (x : BinaryLeavitt) :
      leavittWordT l * (leavittWordS l * x) = x := by
    rw [← mul_assoc, hl, one_mul]
  constructor
  · rw [prefixInsertionHom_val, leavittWordS_append,
      leavittWordS_append]
    simp only [leavittCylinder]
    noncomm_ring [hl, hl', h.prefixing]
  · have hinv :
        (prefixInsertionHom l g)⁻¹ = prefixInsertionHom l g⁻¹ :=
      ((prefixInsertionHom l).map_inv g).symm
    rw [hinv, prefixInsertionHom_val, leavittWordT_append,
      leavittWordT_append]
    simp only [leavittCylinder]
    noncomm_ring [hl, hl', h.deletion]
    rw [← mul_assoc, h.deletion]
end SoficGroups.ThompsonFLocalWitness
