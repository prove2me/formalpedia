-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_has_edge_maximal_supergraph__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:47:28.507757+00:00
-- url     : https://prove2.me/submissions/80c3a836-148c-4d11-a0c5-3050eb880144

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel G.Adj := dG; letI : DecidableRel H.Adj := dH; G.edgeFinset ⊆ H.edgeFinset) ∧
      HasPlanarDrawingOn H ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; H.edgeFinset ⊆ K.edgeFinset) →
        HasPlanarDrawingOn K →
        (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; K.edgeFinset = H.edgeFinset)) := by
  classical
  letI : DecidableRel G.Adj := dG
  let P : SimpleGraph V → Prop := fun A => G ≤ A ∧ HasPlanarDrawingOn A
  have hPG : P G := ⟨le_rfl, hG⟩
  obtain ⟨H, dH, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists P).2 ⟨G, hPG⟩
  have hPH : P H := hExt.1
  refine ⟨H, dH, ?_, hPH.2, ?_⟩
  · letI : DecidableRel H.Adj := dH
    exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr hPH.1
  · intro K dK hHK hK
    letI : DecidableRel H.Adj := dH
    letI : DecidableRel K.Adj := dK
    have hHKle : H ≤ K := SimpleGraph.edgeFinset_subset_edgeFinset.mp hHK
    have hPK : P K := ⟨le_trans hPH.1 hHKle, hK⟩
    have hcard : K.edgeFinset.card ≤ H.edgeFinset.card := by
      exact hExt.2 hPK
    exact (Finset.eq_of_subset_of_card_le hHK hcard).symm
