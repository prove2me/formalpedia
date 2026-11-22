-- Prove2me | solution 1 for Parikh.bounded_cycles_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:25.042887+00:00
-- url     : https://prove2.me/submissions/30e87976-49e8-4311-bd37-bbce8329035c

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
public import Theorems.Thm_Parikh_Cycle_root_mem_support
public import Theorems.Thm_Parikh_Valid_support_active
public import Theorems.Thm_Parikh_bounded_open_finite


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] (g : ContextFreeGrammar T) :
    {C : ParseTree T g.NT | IsBoundedCycle g C}.Finite := by
  apply (bounded_open_finite g ((activeNonterminals g).card + 1)).subset
  rintro C ⟨⟨A, hcycle⟩, hheight⟩
  refine ⟨⟨hcycle.1.1, ?_⟩, hheight⟩
  intro B hB
  have hBA : B = A := by
    simpa only [hcycle.1.2, List.mem_singleton] using hB
  subst B
  exact hcycle.1.1.support_active hcycle.root_mem_support
end Parikh
