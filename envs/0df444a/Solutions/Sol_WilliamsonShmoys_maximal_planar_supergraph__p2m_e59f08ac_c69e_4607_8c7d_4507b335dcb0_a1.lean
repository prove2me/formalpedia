-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_e59f08ac_c69e_4607_8c7d_4507b335dcb0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:23:13.968343+00:00
-- url     : https://prove2.me/submissions/91f0136a-aa06-4825-957c-c780b14cce3d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (LE.le H K)
        (And (HasPlanarDrawingOn K)
          (forall (L : SimpleGraph V), LE.le K L ->
            HasPlanarDrawingOn L -> L = K)) := by
  classical
  let P : SimpleGraph V -> Prop := fun G =>
    And (LE.le H G) (HasPlanarDrawingOn G)
  have hP : Exists fun G : SimpleGraph V => P G :=
    Exists.intro H (And.intro le_rfl hH)
  have hEx : Exists fun G : SimpleGraph V =>
      Exists fun d : DecidableRel G.Adj => SimpleGraph.IsExtremal G P :=
    (SimpleGraph.exists_isExtremal_iff_exists P).2 hP
  let K : SimpleGraph V := Classical.choose hEx
  have hExK : Exists fun d : DecidableRel K.Adj => SimpleGraph.IsExtremal K P :=
    Classical.choose_spec hEx
  let dK : DecidableRel K.Adj := Classical.choose hExK
  have hmax : SimpleGraph.IsExtremal K P := Classical.choose_spec hExK
  letI : DecidableRel K.Adj := dK
  refine Exists.intro K (And.intro hmax.prop.1 (And.intro hmax.prop.2 ?_))
  intro L hKL hL
  have hPL : P L := And.intro (le_trans hmax.prop.1 hKL) hL
  exact ((hmax.le_iff_eq hPL).mp hKL).symm