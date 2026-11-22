-- Prove2me | solution 1 for Parikh.bases_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:36.47779+00:00
-- url     : https://prove2.me/submissions/63ba2d5b-da30-4fe2-925a-a644b42a30f3

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
public import Theorems.Thm_Parikh_bounded_open_finite
public import Theorems.Thm_Parikh_simple_height


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] (g : ContextFreeGrammar T) :
    {B : ParseTree T g.NT | IsBase g B}.Finite := by
  apply (bounded_open_finite g (activeNonterminals g).card).subset
  rintro B ⟨hB, _, hsimple⟩
  exact ⟨⟨hB.1, by simp [hB.2]⟩, simple_height g B hB hsimple⟩
end Parikh
