-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:20.824208+00:00
-- url     : https://prove2.me/submissions/87990358-e817-4b0e-bc73-6ad5fc18b199

import Theorems.Thm_WilliamsonShmoys_exists_edge_card_maximal_planar_extension__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
import Theorems.Thm_WilliamsonShmoys_eq_of_le_of_edgeFinset_card_le__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      H.edgeFinset.card ≤ M.edgeFinset.card ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨M, hHM, hM, hHcard, hmax⟩ :=
    WilliamsonShmoys.exists_edge_card_maximal_planar_extension__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1 H hH
  refine ⟨M, hHM, hHcard, hM, ?_⟩
  intro N hMN hN
  have hHN : H ≤ N := le_trans hHM hMN
  have hNcard : N.edgeFinset.card ≤ M.edgeFinset.card := hmax N hHN hN
  exact WilliamsonShmoys.eq_of_le_of_edgeFinset_card_le__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1 M N hMN hNcard