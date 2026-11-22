-- Prove2me | solution 1 for Parikh.first_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:57.578178+00:00
-- url     : https://prove2.me/submissions/39633e99-6e1f-4bcc-a164-fddc52cdacfa

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_ActivationOrder_filter_of_covered

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (cs : List C)
    (h : ActivationOrder required added U cs) :
    Activatable required added U cs.toFinset := by
  induction cs generalizing U with
  | nil => exact ⟨[], by simp, by simp, by simp [ActivationOrder]⟩
  | cons c cs ih =>
    obtain ⟨order, hnd, hmem, horder⟩ := ih (U ∪ added c) h.2
    have hfiltered := horder.filter_of_covered (fun d => decide (d ≠ c)) (by
      intro d hd hp
      have heq : d = c := by simpa using hp
      subst d
      exact Set.subset_union_right)
    refine ⟨c :: order.filter (fun d => decide (d ≠ c)), ?_, ?_, h.1, hfiltered⟩
    · exact List.nodup_cons.mpr ⟨by simp, List.Nodup.filter _ hnd⟩
    · intro d
      simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq, hmem,
        List.mem_toFinset]
      tauto
end Parikh
