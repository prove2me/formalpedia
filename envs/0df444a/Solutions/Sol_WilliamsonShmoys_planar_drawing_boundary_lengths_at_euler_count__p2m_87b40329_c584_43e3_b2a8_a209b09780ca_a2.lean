-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:38:06.55511+00:00
-- url     : https://prove2.me/submissions/c9640c3f-3595-478e-8c97-3270b158d04c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (faceCount : Nat)
    (hEuler : Fintype.card V + faceCount = K.edgeFinset.card + 2) :
    ∃ boundaryLength : Fin faceCount → Nat,
      (∑ f : Fin faceCount, boundaryLength f) = 2 * K.edgeFinset.card ∧
      (∀ f : Fin faceCount, 3 ≤ boundaryLength f) := by
  classical
  obtain ⟨f, lengths, heuler, hlength, hsum, hmin⟩ :=
    WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4 K hK hcard hconn
  have hedge : K.edgeSet.ncard = K.edgeFinset.card := by
    rw [← K.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hedge] at heuler hsum
  have hlength' : lengths.length = faceCount := by omega
  subst faceCount
  refine ⟨lengths.get, ?_, ?_⟩
  · calc
      (∑ i : Fin lengths.length, lengths.get i) = lengths.sum := by
        simpa only [List.sum_ofFn] using congrArg List.sum (List.ofFn_get lengths)
      _ = 2 * K.edgeFinset.card := hsum
  · intro i
    exact hmin _ (List.get_mem lengths i)

