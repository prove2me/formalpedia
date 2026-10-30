-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:15:31.429273+00:00
-- url     : https://prove2.me/submissions/3eca83d4-1ce1-4ac6-af90-12e5d80b5b86

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    (Q.edgeSet.ncard : Int) =
      (3 : Int) * (Fintype.card V : Int) - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
  | (apply _root_.WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5 <;> assumption)
