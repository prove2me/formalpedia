-- Prove2me | solution 1 for WilliamsonShmoys.has_euler_face_count_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:26:09.714997+00:00
-- url     : https://prove2.me/submissions/088b60fe-a4cf-443c-a2bb-d707a3acdaf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.


import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_euler_face_count
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.euler_face_count K hK hconn hV
  have hE :=
    WilliamsonShmoys.simple_planar_edge_bound K hK hconn hV
  refine ⟨f, hf, ?_⟩
  omega
