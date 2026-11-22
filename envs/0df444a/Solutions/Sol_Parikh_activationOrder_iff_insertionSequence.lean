-- Prove2me | solution 1 for Parikh.activationOrder_iff_insertionSequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:51.214128+00:00
-- url     : https://prove2.me/submissions/ab27784e-d317-4cd2-ad85-3a84af3cc9a1

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_insertion_accounting
public import Theorems.Thm_Parikh_insertion_enabled


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} {g : ContextFreeGrammar T}
    (roots : ParseTree T g.NT → g.NT) (B : ParseTree T g.NT)
    (Cs : List (ParseTree T g.NT)) (hB : Complete g B)
    (hCs : ∀ C ∈ Cs, Cycle g C (roots C)) :
    ActivationOrder roots ParseTree.support B.support Cs ↔
      ∃ t, InsertionSequence g B Cs t := by
  classical
  induction Cs generalizing B with
  | nil => exact ⟨fun _ => ⟨B, .nil B⟩, fun _ => True.intro⟩
  | cons C Cs ih =>
    have hC := hCs C (by simp)
    have htail : ∀ D ∈ Cs, Cycle g D (roots D) :=
      fun D hD => hCs D (List.mem_cons_of_mem C hD)
    constructor
    · intro horder
      obtain ⟨next, hstep⟩ := (insertion_enabled g B C (roots C) hB hC).mpr horder.1
      have hsupport := (insertion_accounting g B C next hstep).2.2.2
      have hnext : ActivationOrder roots ParseTree.support next.support Cs := by
        simpa only [hsupport] using horder.2
      obtain ⟨t, hseq⟩ := (ih next hstep.2.1 htail).mp hnext
      exact ⟨t, .cons hstep hseq⟩
    · rintro ⟨t, hseq⟩
      cases hseq with
      | @cons _ _ next _ _ hstep hrest =>
        refine ⟨(insertion_enabled g B C (roots C) hB hC).mp ⟨next, hstep⟩, ?_⟩
        have hsupport := (insertion_accounting g B C next hstep).2.2.2
        rw [← hsupport]
        exact (ih next hstep.2.1 htail).mpr ⟨t, hrest⟩
end Parikh
