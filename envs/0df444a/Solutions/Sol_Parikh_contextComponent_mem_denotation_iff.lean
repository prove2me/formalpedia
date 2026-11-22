-- Prove2me | solution 1 for Parikh.contextComponent.mem_denotation_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:09.549051+00:00
-- url     : https://prove2.me/submissions/ec189bcb-8a7a-4a2d-b814-e329fca6c737

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_Component_denotation_eq_vadd_closure


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
namespace contextComponent
theorem _root_.solution {T N : Type*} [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) (v : Vector T) :
    v ∈ (contextComponent B D).denotation ↔
      ∃ k : ParseTree T N → ℕ,
        v = (B.weight + ∑ C ∈ D, C.weight) + ∑ C ∈ D, k C • C.weight := by
  classical
  have hrange : Set.range (contextComponent B D).periods.get =
      Set.range (fun C : D => C.val.weight) := by
    ext w
    simp [contextComponent]
  rw [Component.denotation_eq_vadd_closure, hrange]
  simp only [Set.mem_vadd_set, SetLike.mem_coe, vadd_eq_add,
    AddSubmonoid.mem_closure_range_iff_of_fintype]
  constructor
  · rintro ⟨w, ⟨k, rfl⟩, rfl⟩
    let coeff : ParseTree T N → ℕ := fun C => if hC : C ∈ D then k ⟨C, hC⟩ else 0
    refine ⟨coeff, ?_⟩
    change (B.weight + ∑ C ∈ D, C.weight) + (∑ C : D, k C • C.val.weight) = _
    congr 1
    rw [← Finset.sum_coe_sort D]
    apply Finset.sum_congr rfl
    intro C _
    simp [coeff, C.property]
  · rintro ⟨k, rfl⟩
    refine ⟨∑ C : D, k C.val • C.val.weight, ⟨fun C => k C.val, rfl⟩, ?_⟩
    change (B.weight + ∑ C ∈ D, C.weight) + (∑ C : D, k C.val • C.val.weight) = _
    rw [Finset.sum_coe_sort D (fun C => k C • C.weight)]
end contextComponent
end Parikh
