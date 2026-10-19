-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.commute_prefixInsertion_of_prefixWordAction_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/0818db25-e434-4b62-86bd-61064abbc668

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixInsertionHom_conjugate_of_prefixWordAction

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution
    (g : BinaryLeavittˣ) (w : List (Fin 2))
    (h : PrefixWordAction g w w) (u : BinaryLeavittˣ) :
    Commute g (prefixInsertionHom w u) := by
  have hconjugate :=
    prefixInsertionHom_conjugate_of_prefixWordAction g w w h u
  apply (commute_iff_eq _ _).2
  calc
    g * prefixInsertionHom w u =
        (g * prefixInsertionHom w u * g⁻¹) * g := by group
    _ = prefixInsertionHom w u * g := by rw [hconjugate]
end SoficGroups.ThompsonFLocalWitness
