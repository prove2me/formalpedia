-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/bef11f33-9245-4024-8013-36249a88b71b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (A : Finset V) :
    (Finset.univ.filter fun x => x ∉ A ∧ p x ∈ A).card =
      (A.filter fun x => p x ∉ A).card := by
  classical
  let P : Finset V := Finset.univ.filter fun x => p x ∈ A
  have hP : P.card = A.card := by
    apply Finset.card_bij (fun x _ => p x)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x _ y _ hxy
      exact p.injective hxy
    · intro y hy
      refine ⟨p.symm y, ?_, by simp⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa using hy⟩
  have hsplitA :=
    Finset.card_filter_add_card_filter_not (s := A)
      (fun x => p x ∈ A)
  have hsplitP :=
    Finset.card_filter_add_card_filter_not (s := P)
      (fun x => x ∈ A)
  have hinternal :
      (P.filter fun x => x ∈ A).card =
        (A.filter fun x => p x ∈ A).card := by
    congr 1
    ext x
    simp [P, and_comm]
  have henter :
      (P.filter fun x => x ∉ A).card =
        (Finset.univ.filter fun x => x ∉ A ∧ p x ∈ A).card := by
    congr 1
    ext x
    simp [P, and_comm]
  omega
end SoficGroups.KunThomFiberCoarea
