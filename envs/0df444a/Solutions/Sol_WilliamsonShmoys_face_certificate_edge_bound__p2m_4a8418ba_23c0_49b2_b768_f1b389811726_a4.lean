-- Prove2me | solution 1 for WilliamsonShmoys.face_certificate_edge_bound__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:43:43.603982+00:00
-- url     : https://prove2.me/submissions/a75e6d05-8ba9-4c37-8c76-45ee38e6652b

import Mathlib
import Definitions.Def_PlanarFaceCertificate__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hfaces : WilliamsonShmoys.PlanarFaceCertificate__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4 G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  classical
  have hsum : 3 * hfaces.faceCount ≤
      (∑ i : Fin hfaces.faceCount, hfaces.faceLength i) := by
    calc
      3 * hfaces.faceCount = ∑ i : Fin hfaces.faceCount, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin hfaces.faceCount, hfaces.faceLength i :=
        Finset.sum_le_sum (fun i _ => hfaces.everyFaceHasThreeSides i)
  have heuler : Fintype.card V + hfaces.faceCount = G.edgeSet.ncard + 2 := hfaces.euler
  have hinc : (∑ i : Fin hfaces.faceCount, hfaces.faceLength i) =
      2 * G.edgeSet.ncard := by
    simpa using hfaces.edgeIncidences
  have hmain : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by omega
  omega
