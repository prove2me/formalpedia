-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:28:13.820254+00:00
-- url     : https://prove2.me/submissions/c65bb5cf-6fc1-4ee7-8981-8d90eb5ebca3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_e3fcbf10_6f41_4741_b7a4_cf721019c4f7_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    (letI : DecidableRel T.Adj := Classical.decRel T.Adj
     T.edgeFinset.card < 3 * Fintype.card V - 6 →
       ∃ U : SimpleGraph V, T ≤ U ∧ U ≠ T ∧ HasPlanarDrawingOn U) := by
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  intro hlt
  obtain ⟨U, hTU, hUdraw, hUcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_e3fcbf10_6f41_4741_b7a4_cf721019c4f7_a1
      T hV hT
  refine ⟨U, hTU, ?_, hUdraw⟩
  intro hEq
  subst U
  omega