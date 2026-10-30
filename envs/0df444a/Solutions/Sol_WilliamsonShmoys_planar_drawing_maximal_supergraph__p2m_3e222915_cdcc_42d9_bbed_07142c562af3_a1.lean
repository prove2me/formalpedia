-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:05.889453+00:00
-- url     : https://prove2.me/submissions/df557c05-f87f-49e9-9d99-660024fac2e7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    Exists fun X : SimpleGraph V => LE.le W X /\ WilliamsonShmoys.HasPlanarDrawingOn X /\
      forall Y : SimpleGraph V, LE.le X Y -> WilliamsonShmoys.HasPlanarDrawingOn Y -> Y = X := by
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
  have hmax_exists :=
    WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
      (fun G : SimpleGraph V => LE.le W G /\ WilliamsonShmoys.HasPlanarDrawingOn G)
      (Exists.intro W (And.intro le_rfl hW))
  cases hmax_exists with
  | intro X hx =>
    cases hx with
    | intro hX hmax =>
      refine Exists.intro X (And.intro hX.1 (And.intro hX.2 ?_))
      intro Y hXY hY
      exact hmax Y (And.intro (le_trans hX.1 hXY) hY) hXY