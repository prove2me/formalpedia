-- Prove2me | solution 1 for WilliamsonShmoys.planar_complete_card_le_four__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:04.186536+00:00
-- url     : https://prove2.me/submissions/341f3940-6917-4595-89db-2f6ea96f2418
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
import Theorems.Thm_WilliamsonShmoys_choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    Fintype.card V ≤ 4 := by
  classical
  letI : DecidableRel (⊤ : SimpleGraph V).Adj := SimpleGraph.Top.adjDecidable V
  by_cases hsmall : Fintype.card V < 3
  · omega
  · have hcard : 3 ≤ Fintype.card V := by omega
    have hedges :=
      WilliamsonShmoys.planar_edge_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
        H hH hcard
    have htop : H = ⊤ := SimpleGraph.eq_top_iff_forall_ne_adj.mpr hcomplete
    have hedges' : (Fintype.card V).choose 2 ≤ 3 * Fintype.card V - 6 := by
      calc
        (Fintype.card V).choose 2 = (⊤ : SimpleGraph V).edgeFinset.card := by
          symm
          exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two
        _ = H.edgeFinset.card := by
          have hfin : (⊤ : SimpleGraph V).edgeFinset = H.edgeFinset := by
            ext e
            simp [htop]
          rw [hfin]
        _ ≤ 3 * Fintype.card V - 6 := hedges
    exact
      WilliamsonShmoys.choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
        (Fintype.card V) hcard hedges'