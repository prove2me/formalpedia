-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_choice_totalChoiceTerm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:40.388116+00:00
-- url     : https://prove2.me/submissions/15822fc7-ef03-4dda-b65d-918bf6723ed5

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_eq_zero_of_source_leaf
import Theorems.Thm_Sabidussi_OddBalance_sum_coveredChoice_totalChoiceTerm_eq_zero

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ f : Choice S, totalChoiceTerm b S f) = 0 := by
  classical
  let covers : Choice S → Prop := fun f =>
    ∀ w : {w // w ∈ S}, ∃ v, (f v : V) = w
  have hgood :
      (∑ f ∈ Finset.univ.filter covers, totalChoiceTerm b S f) = 0 := by
    calc
      (∑ f ∈ Finset.univ.filter covers, totalChoiceTerm b S f) =
          ∑ c : CoveredChoice S, totalChoiceTerm b S c.1 := by
            exact Finset.sum_subtype (Finset.univ.filter covers) (by
              intro f
              simp [covers, CoveredChoice]) (fun f => totalChoiceTerm b S f)
      _ = 0 := sum_coveredChoice_totalChoiceTerm_eq_zero b hsymm hrow S hS
  have hbad :
      (∑ f ∈ Finset.univ.filter (fun f => ¬covers f), totalChoiceTerm b S f) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    have hn : ¬covers f := (Finset.mem_filter.mp hf).2
    simp only [covers, not_forall, not_exists] at hn
    obtain ⟨w, hw⟩ := hn
    exact totalChoiceTerm_eq_zero_of_source_leaf b hsymm hrow S f w w rfl hw
  calc
    (∑ f : Choice S, totalChoiceTerm b S f) =
        (∑ f ∈ Finset.univ.filter covers, totalChoiceTerm b S f) +
          ∑ f ∈ Finset.univ.filter (fun f => ¬covers f), totalChoiceTerm b S f := by
            exact (Finset.sum_filter_add_sum_filter_not Finset.univ covers
              (fun f => totalChoiceTerm b S f)).symm
    _ = 0 := by rw [hgood, hbad, add_zero]
end Sabidussi.OddBalance
