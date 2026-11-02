-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:03:41.47821+00:00
-- url     : https://prove2.me/submissions/ebe44c54-4175-43c7-af3a-44064d7fb59a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : Nat.le 3 (Fintype.card V)) :
    Exists (fun lengths : List Nat =>
      And (forall l : Nat, List.Mem l lengths -> Nat.le 3 l)
        (And (lengths.sum = 2 * M.edgeFinset.card)
          (Fintype.card V + lengths.length = M.edgeFinset.card + 2))) := by
  rcases WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
      M hM hcard hconn with ⟨f, lengths, heuler, hlen, hsum, hbound⟩
  have hedge : M.edgeSet.ncard = M.edgeFinset.card := by
    classical
    simpa [SimpleGraph.edgeFinset] using
      (Set.ncard_eq_toFinset_card M.edgeSet)
  refine ⟨lengths, hbound, ?_, ?_⟩
  · calc
      lengths.sum = 2 * M.edgeSet.ncard := hsum
      _ = 2 * M.edgeFinset.card := by rw [hedge]
  · calc
      Fintype.card V + lengths.length = Fintype.card V + f := by rw [hlen]
      _ = f + Fintype.card V := by omega
      _ = M.edgeSet.ncard + 2 := heuler
      _ = M.edgeFinset.card + 2 := by rw [hedge]
