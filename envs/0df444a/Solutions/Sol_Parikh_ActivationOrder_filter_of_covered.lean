-- Prove2me | solution 1 for Parikh.ActivationOrder.filter_of_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:55.425445+00:00
-- url     : https://prove2.me/submissions/e119d2b9-e0e6-4fc5-aa61-51ecf62d97ad

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
    (h : ActivationOrder required added U cs) (p : C → Bool)
    (hcovered : ∀ c ∈ cs, p c = false → added c ⊆ U) :
    ActivationOrder required added U (cs.filter p) := by
  induction cs generalizing U with
  | nil => simp [ActivationOrder]
  | cons c cs ih =>
    cases hp : p c with
    | false =>
      have hU : U ∪ added c = U :=
        Set.union_eq_left.mpr (hcovered c (by simp) hp)
      have htail : ActivationOrder required added U cs := by
        simpa only [hU] using h.2
      simpa only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte] using
        ih htail (fun d hd hpd => hcovered d (List.mem_cons_of_mem c hd) hpd)
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, ActivationOrder]
      refine ⟨h.1, ih h.2 ?_⟩
      intro d hd hpd x hx
      exact Or.inl (hcovered d (List.mem_cons_of_mem c hd) hpd hx)
end Parikh.ActivationOrder
