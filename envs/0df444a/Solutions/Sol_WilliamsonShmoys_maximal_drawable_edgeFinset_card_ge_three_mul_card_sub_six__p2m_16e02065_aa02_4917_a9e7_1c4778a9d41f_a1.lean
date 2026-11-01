-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edgeFinset_card_ge_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:48:47.065053+00:00
-- url     : https://prove2.me/submissions/92ecd46b-1ea7-46c5-b84b-6889286e116d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_triangulated__p2m_b8ffaa04_868a_495a_ab39_10d09a3d9b95_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by
  obtain ⟨K, hKdec, hMK, hKdraw, hKcard⟩ :=
    WilliamsonShmoys.maximal_drawable_extension_triangulated__p2m_b8ffaa04_868a_495a_ab39_10d09a3d9b95_a1
      M hM hcard
  letI : DecidableRel K.Adj := hKdec
  have hKM : K ≤ M := hmax K hMK hKdraw
  have hEq : K = M := le_antisymm hKM hMK
  have hEdges : M.edgeFinset = K.edgeFinset :=
    SimpleGraph.edgeFinset_inj.mpr hEq.symm
  have hCard : M.edgeFinset.card = 3 * Fintype.card V - 6 :=
    (congrArg Finset.card hEdges).trans hKcard
  exact hCard.ge
