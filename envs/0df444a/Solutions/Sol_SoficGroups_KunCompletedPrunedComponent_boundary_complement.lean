-- Prove2me | solution 1 for SoficGroups.KunCompletedPrunedComponent.boundary_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/cd40c378-3b1c-4ed8-9f2f-e4f2ece5194f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_entering_eq_card_exiting

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators
namespace SoficGroups.KunCompletedPrunedComponent
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    SoficGroups.boundary σ (Finset.univ \ A) =
      SoficGroups.boundary σ A := by
  classical
  unfold SoficGroups.boundary
  apply Finset.sum_congr rfl
  intro i _
  calc
    ((Finset.univ \ A).filter
        (fun x => σ i x ∉ Finset.univ \ A)).card =
        (Finset.univ.filter
          (fun x => x ∉ A ∧ σ i x ∈ A)).card := by
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      grind
    _ = (A.filter fun x => σ i x ∉ A).card :=
      SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting
        (σ i) A
end SoficGroups.KunCompletedPrunedComponent
