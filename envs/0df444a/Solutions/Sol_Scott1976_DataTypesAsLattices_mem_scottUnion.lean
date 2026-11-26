-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_scottUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:16.112668+00:00
-- url     : https://prove2.me/submissions/d8bfb115-155e-4d72-b1b0-4b6e2729538a

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} {x : Pomega} {k : ℕ} :
    k ∈ scottUnion f x ↔ ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by
  constructor
  · intro hk
    obtain ⟨n, hn, hfk⟩ := Set.mem_iUnion.mp hk
    exact ⟨n, hn, hfk⟩
  · intro ⟨n, hn, hk⟩
    exact Set.mem_iUnion.mpr ⟨n, hn, hk⟩
end Scott1976.DataTypesAsLattices
