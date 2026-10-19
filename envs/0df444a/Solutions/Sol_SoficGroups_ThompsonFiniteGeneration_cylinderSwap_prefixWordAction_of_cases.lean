-- Prove2me | solution 1 for SoficGroups.ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/fab8a4f8-9254-4b8f-a397-3e5d70646921

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_append
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_cylinderSwap_prefixWordAction_left
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_cylinderSwap_prefixWordAction_right
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_cylinderSwap_prefixWordAction_fixed

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
open SoficGroups.ThompsonFiniteGeneration
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFiniteGeneration
theorem _root_.solution
    {a b w v : List (Fin 2)}
    (hab : ¬ a <+: b) (hba : ¬ b <+: a)
    (hcase :
      (a <+: w ∧ v = b ++ w.drop a.length) ∨
      (b <+: w ∧ v = a ++ w.drop b.length) ∨
      (v = w ∧ ¬ a <+: w ∧ ¬ w <+: a ∧
        ¬ b <+: w ∧ ¬ w <+: b)) :
    PrefixWordAction (cylinderSwap a b hab hba) w v := by
  rcases hcase with h | h | h
  · obtain ⟨haw, rfl⟩ := h
    simpa only [(List.prefix_append_drop haw).symm] using
      prefixWordAction_append
        (cylinderSwap_prefixWordAction_left a b hab hba)
        (w.drop a.length)
  · obtain ⟨hbw, rfl⟩ := h
    simpa only [(List.prefix_append_drop hbw).symm] using
      prefixWordAction_append
        (cylinderSwap_prefixWordAction_right a b hab hba)
        (w.drop b.length)
  · obtain ⟨hv, haw, hwa, hbw, hwb⟩ := h
    subst v
    exact cylinderSwap_prefixWordAction_fixed
      a b w hab hba haw hwa hbw hwb
end SoficGroups.ThompsonFiniteGeneration
