-- Prove2me | solution 1 for Parikh.contextComponent_size_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:52.484812+00:00
-- url     : https://prove2.me/submissions/94a6af09-fcba-4e75-9ca2-f63ef1b1d24c

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T N : Type*} [Fintype T] [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) (M : ℕ)
    (hB : norm B.weight ≤ M) (hD : ∀ C ∈ D, norm C.weight ≤ M) :
    (contextComponent B D).periods.length = D.card ∧
      norm (contextComponent B D).base ≤ (D.card + 1) * M ∧
      ∀ p ∈ (contextComponent B D).periods, norm p ≤ M := by
  classical
  refine ⟨by simp [contextComponent], ?_, ?_⟩
  · have hsum : norm (contextComponent B D).base =
        norm B.weight + ∑ C ∈ D, norm C.weight := by
      change (∑ a, (B.weight + ∑ C ∈ D, C.weight) a) = _
      simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib, norm]
      rw [Finset.sum_comm]
    rw [hsum]
    calc
      norm B.weight + ∑ C ∈ D, norm C.weight ≤ M + D.card * M :=
        Nat.add_le_add hB (by simpa using Finset.sum_le_sum hD)
      _ = (D.card + 1) * M := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  · intro p hp
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hp
    exact hD C (Finset.mem_toList.mp hC)
end Parikh
