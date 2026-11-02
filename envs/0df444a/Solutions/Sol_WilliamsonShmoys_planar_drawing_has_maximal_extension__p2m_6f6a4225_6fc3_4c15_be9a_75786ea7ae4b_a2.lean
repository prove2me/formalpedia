-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:55:25.603167+00:00
-- url     : https://prove2.me/submissions/3f4ce2aa-5c17-416e-b71c-f9dced1ecc52

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2__p2m_af83aa0e_dfa3_4817_a80f_86472a8bb5ad_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      L.edgeFinset.card ≤ H.edgeFinset.card := by
  classical
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2__p2m_af83aa0e_dfa3_4817_a80f_86472a8bb5ad_a1 L hL
  refine ⟨H, hLH, hH, ?_, hmax L le_rfl hL⟩
  intro K hHK hK
  by_contra hne
  have hlt : H < K := lt_of_le_of_ne hHK (Ne.symm hne)
  have hedge : H.edgeFinset.card < K.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
  exact (not_lt_of_ge (hmax K (hLH.trans hHK) hK)) hedge