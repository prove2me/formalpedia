-- Prove2me | solution 1 for Parikh.ActivationOrder.of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:04.296305+00:00
-- url     : https://prove2.me/submissions/2d3d0090-6c38-4e0f-b5a1-34cc92b2dca7

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation

set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.ActivationOrder
variable {N C : Type*} {required : C → N} {added : C → Set N}
namespace Parikh.ActivationOrder
theorem _root_.solution {U : Set N} {cs : List C}
    (h : ∀ c ∈ cs, required c ∈ U) : ActivationOrder required added U cs := by
  induction cs generalizing U with
  | nil => simp [ActivationOrder]
  | cons c cs ih =>
    refine ⟨h c (by simp), ih ?_⟩
    intro d hd
    exact Or.inl (h d (List.mem_cons_of_mem c hd))
end Parikh.ActivationOrder
