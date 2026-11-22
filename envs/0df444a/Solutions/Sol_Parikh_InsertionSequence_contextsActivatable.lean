-- Prove2me | solution 1 for Parikh.InsertionSequence.contextsActivatable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:46.4768+00:00
-- url     : https://prove2.me/submissions/ad017c6c-ff56-460b-9839-fcba46a55686

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_first_occurrences
public import Theorems.Thm_Parikh_activationOrder_iff_insertionSequence

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
namespace InsertionSequence
theorem _root_.solution {T : Type*} {g : ContextFreeGrammar T}
    {B t : ParseTree T g.NT} {Cs : List (ParseTree T g.NT)}
    [DecidableEq (ParseTree T g.NT)]
    (h : InsertionSequence g B Cs t) (hB : Complete g B) :
    ContextsActivatable g B Cs.toFinset := by
  classical
  have hcycles : ∀ C ∈ Cs, ∃ A, Cycle g C A := by
    clear hB
    induction h with
    | nil _ => simp
    | cons step _ ih =>
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · obtain ⟨_, _, A, hcycle, _⟩ := step
        exact ⟨A, hcycle⟩
      · exact ih C hC
  let roots : ParseTree T g.NT → g.NT := fun C =>
    if hC : C ∈ Cs then Classical.choose (hcycles C hC) else g.initial
  have hrootcycles : ∀ C ∈ Cs, Cycle g C (roots C) := by
    intro C hC
    simpa only [roots, dif_pos hC] using Classical.choose_spec (hcycles C hC)
  have horder := (activationOrder_iff_insertionSequence roots B Cs hB hrootcycles).mpr ⟨t, h⟩
  obtain ⟨order, hnodup, hmem, hfirst⟩ :=
    first_occurrences roots ParseTree.support B.support Cs horder
  exact ⟨order, hnodup, hmem, roots,
    fun C hC => hrootcycles C (List.mem_toFinset.mp hC), hfirst⟩
end InsertionSequence
end Parikh
