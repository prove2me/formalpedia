-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:03:15.22235+00:00
-- url     : https://prove2.me/submissions/027e0a2a-bee4-48e2-8bce-6894b2dd358d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T) :
    (letI : DecidableRel T.Adj := Classical.decRel T.Adj
     T.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  have hupper :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
      T hV hT
  have hnotlt : ¬ T.edgeFinset.card < 3 * Fintype.card V - 6 := by
    intro hlt
    obtain ⟨U, hTU, hneq, hU⟩ :=
      WilliamsonShmoys.planar_edge_augmentation__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
        T hV hT hlt
    exact hneq (hmax U hTU hU)
  exact Nat.le_antisymm hupper (Nat.le_of_not_gt hnotlt)