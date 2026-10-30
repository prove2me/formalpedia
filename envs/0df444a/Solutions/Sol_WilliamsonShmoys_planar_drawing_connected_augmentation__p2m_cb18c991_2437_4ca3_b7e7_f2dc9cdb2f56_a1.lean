-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:43.661957+00:00
-- url     : https://prove2.me/submissions/fb3c82a9-833e-4a70-952c-1ff175aca09e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_extension__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 0 < Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      And (K.edgeSet.ncard <= H.edgeSet.ncard)
        (And H.Connected (WilliamsonShmoys.HasPlanarDrawingOn H)) := by
  let hExt :=
    WilliamsonShmoys.maximal_planar_supergraph_extension__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2
      K hDraw
  let H := Classical.choose hExt
  have hExtSpec := Classical.choose_spec hExt
  have hKH : K <= H := hExtSpec.1
  have hDrawH : WilliamsonShmoys.HasPlanarDrawingOn H := hExtSpec.2.1
  have hmax : forall G : SimpleGraph V, H <= G ->
      WilliamsonShmoys.HasPlanarDrawingOn G -> G = H := hExtSpec.2.2
  have hconn :=
    WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2
      H hmax hDrawH hV
  refine Exists.intro H (And.intro ?_ (And.intro hconn hDrawH))
  apply Set.ncard_mono
  exact SimpleGraph.edgeSet_mono hKH