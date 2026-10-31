-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_extension__p2m_4d39bfdd_3b15_4c53_aa35_0f292c6309dd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:47:54.407843+00:00
-- url     : https://prove2.me/submissions/46ca9ae0-9bbd-4ede-a4bf-96f8448e124f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_embedding_joining_arc__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_clean_edge__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hdis : ¬ K.Connected) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      K.edgeFinset ⊂ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  rcases hK with ⟨p, arc, hp, hdrawing, hcross⟩
  obtain ⟨u, v, gamma, huv, hnonadj, hcont, hinj, hzero, hone,
      hvertices, harcs⟩ :=
    WilliamsonShmoys.disconnected_embedding_joining_arc__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a2
      K p arc hp hdrawing hcross hcard hdis
  exact WilliamsonShmoys.planar_drawing_add_clean_edge__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
    K p arc hp hdrawing hcross u v gamma huv hnonadj hcont hinj hzero hone hvertices harcs