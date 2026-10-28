-- Prove2me | solution 1 for WilliamsonShmoys.connected_induced_face_data
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:42:19.53828+00:00
-- url     : https://prove2.me/submissions/72e57d86-e80b-4209-a7e8-01a4c8b8d6ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset V)
    (hC : C.Nonempty)
    (hconn : (G.induce (fun v => v ∈ C)).Connected)
    (hlarge : 3 ≤ C.card)
    (hbound : (G.induce (fun v => v ∈ C)).edgeSet.ncard + 6 ≤ 3 * C.card) :
    ∃ f : ℕ,
      C.card + f = (G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * (G.induce (fun v => v ∈ C)).edgeSet.ncard := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  have h' : C.card ≤ (G.induce (fun v => v ∈ C)).edgeSet.ncard + 1 := by
    rw [← Nat.card_coe_set_eq]
    convert h using 2
    exact (Nat.card_eq_finsetCard C).symm
  refine ⟨(G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 - C.card, by omega, by omega⟩
