-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:57:21.411711+00:00
-- url     : https://prove2.me/submissions/ae027bee-506e-4e2f-a59d-9caf55248a18

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_card_maximum__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
import Theorems.Thm_WilliamsonShmoys_edge_card_strict_of_le__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      And (G <= H)
        (And (HasPlanarDrawingOn H)
          (And (forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H)
            (G.edgeSet.ncard <= H.edgeSet.ncard))) := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_card_maximum__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
      G hG
  refine Exists.intro H ?_
  apply And.intro hGH
  apply And.intro hH
  apply And.intro
  · intro K hHK hK
    have hKG : G <= K := le_trans hGH hHK
    by_contra hne
    have hstrict :=
      WilliamsonShmoys.edge_card_strict_of_le__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
        H K hHK (Ne.symm hne)
    have hbound := hMax K hKG hK
    omega
  · exact hMax G le_rfl hG