-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_face_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:35:07.912608+00:00
-- url     : https://prove2.me/submissions/99b85ad2-13d2-4f63-8b9f-8af100d6e5d5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (d : WilliamsonShmoys.PlanarFaceCountData G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hsum : Finset.univ.sum (fun f : Fin d.faceCount => d.faceLength f) = d.faceCount * 3 := by
    simp [d.triangular]
  have hfaces0 : d.faceCount * 3 = 2 * G.edgeSet.ncard :=
    hsum.symm.trans d.totalLength
  have hfaces : 3 * d.faceCount = 2 * G.edgeSet.ncard := by
    simpa [Nat.mul_comm] using hfaces0
  have hscaled : 3 * (Fintype.card V + d.faceCount) =
      3 * (G.edgeSet.ncard + 2) :=
    congrArg (fun n : Nat => 3 * n) d.euler
  have hlin : 3 * Fintype.card V + 2 * G.edgeSet.ncard =
      3 * G.edgeSet.ncard + 6 := by
    calc
      3 * Fintype.card V + 2 * G.edgeSet.ncard =
          3 * Fintype.card V + 3 * d.faceCount := by rw [hfaces]
      _ = 3 * (Fintype.card V + d.faceCount) := by simp [Nat.mul_add]
      _ = 3 * (G.edgeSet.ncard + 2) := hscaled
      _ = 3 * G.edgeSet.ncard + 6 := by omega
  omega