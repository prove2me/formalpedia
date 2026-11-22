-- Prove2me | solution 1 for Parikh.ActivationOrder.append_of_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:54.950799+00:00
-- url     : https://prove2.me/submissions/e6ac86ea-8b36-4fe3-ad30-0bdaf20ee8d6

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_ActivationOrder_of_forall_mem

set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.ActivationOrder
variable {N C : Type*} {required : C → N} {added : C → Set N}
namespace Parikh.ActivationOrder
theorem _root_.solution {U : Set N} {cs ds : List C}
    (h : ActivationOrder required added U cs)
    (hcovered : ∀ d ∈ ds, required d ∈ U ∨ ∃ c ∈ cs, required d ∈ added c) :
    ActivationOrder required added U (cs ++ ds) := by
  induction cs generalizing U with
  | nil =>
    apply of_forall_mem
    intro d hd
    simpa using hcovered d hd
  | cons c cs ih =>
    refine ⟨h.1, ih h.2 ?_⟩
    intro d hd
    rcases hcovered d hd with hU | ⟨b, hb, hadded⟩
    · exact Or.inl (Or.inl hU)
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl (Or.inr hadded)
      · exact Or.inr ⟨b, hb, hadded⟩
end Parikh.ActivationOrder
