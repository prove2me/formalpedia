-- Prove2me | solution 1 for Reduce.push_node_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:13:19.323675+00:00
-- url     : https://prove2.me/submissions/5436aeed-f80b-4bc9-b704-b7b08b9b547e

import Definitions.Def_Bdd_Reduce_Populate
import Definitions.Def_Bdd_Reduce_Process

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {n m : Nat} {i : Nat}
    (O : OBdd n m)
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (entry : (RawPointer × RawPointer) × Fin m)
    (hec : EntryCorrect O ps i entry)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    (hnonred : entry.1.1 ≠ entry.1.2)
    (hallabove : AllAbove ps i)
    (hheapinj : HeapInjective ps) :
    let hN  : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded
                ps.state.size := ⟨hbound.1, hbound.2⟩
    let ps₁ := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
    let ptr := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
    let ps₂ := set_id ps₁ entry.2 ptr
    ∃ hj  : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
    ∃ hp  : ptr.Bounded ps₂.state.size,
    ∃ ho  : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩,
      OBdd.Reduced ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ ∧
      ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ I =
           OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I :=
  push_node_correct' O ps inv entry hec hbound hnonred ps.state.size (le_refl _) hbound
    (fun k _ => hallabove k) hheapinj
    (fun k heq => by
      have h : i < O.1.heap[entry.2].var.1 := by
        have hh := hallabove k; rw [heq] at hh; exact hh
      have hvar : O.1.heap[entry.2].var.1 = i := hec.2.1
      omega)
end Reduce
