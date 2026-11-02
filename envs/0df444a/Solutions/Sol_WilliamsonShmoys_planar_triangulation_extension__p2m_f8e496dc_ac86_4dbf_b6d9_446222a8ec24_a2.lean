-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_f8e496dc_ac86_4dbf_b6d9_446222a8ec24_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:12:36.628743+00:00
-- url     : https://prove2.me/submissions/39b87655-5464-448f-8fc2-3638e235c6ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hNdraw : HasPlanarDrawingOn N) :
    Exists (fun K : SimpleGraph V =>
      And (LE.le N K)
        (And (HasPlanarDrawingOn K)
          (letI : DecidableRel K.Adj := Classical.decRel K.Adj
           3 * Fintype.card V = K.edgeFinset.card + 6))) := by
  have hext :=
    WilliamsonShmoys.maximal_drawable_extension__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
      N hcard hNdraw
  let K := Classical.choose hext
  have hprops := Classical.choose_spec hext
  have hNK := hprops.1
  have hKdraw := hprops.2.1
  have hmax := hprops.2.2
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hcount :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
      K hcard hKdraw hmax
  exact Exists.intro K (And.intro hNK (And.intro hKdraw hcount))