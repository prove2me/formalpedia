-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_edge_card_ge__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:59:36.070018+00:00
-- url     : https://prove2.me/submissions/49860d2c-8c9a-44b4-b193-779ac2bd28a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximizer_of_bounded_nat__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
import Theorems.Thm_WilliamsonShmoys_SimpleGraph_edge_card_mono_and_eq_of_le__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  let P : SimpleGraph V → Prop :=
    fun K => H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hne : ∃ K, P K := ⟨H, le_rfl, hdraw⟩
  have hbdd : ∃ N, ∀ K, P K → K.edgeFinset.card ≤ N := by
    refine ⟨Fintype.card (Sym2 V), ?_⟩
    intro K _
    exact Finset.card_le_univ _
  obtain ⟨K, hPK, hmax⟩ :=
    WilliamsonShmoys.exists_maximizer_of_bounded_nat__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
      P (fun K => K.edgeFinset.card) hne hbdd
  have hcardMono :=
    WilliamsonShmoys.SimpleGraph.edge_card_mono_and_eq_of_le__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
      H K hPK.1
  refine ⟨K, hPK.1, hPK.2, ?_, hcardMono.1⟩
  intro L hL hKL
  have hPL : P L := ⟨le_trans hPK.1 hKL, hL⟩
  have hLKcard : L.edgeFinset.card ≤ K.edgeFinset.card :=
    hmax L hPL
  have hmonoKL :=
    WilliamsonShmoys.SimpleGraph.edge_card_mono_and_eq_of_le__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
      K L hKL
  exact (hmonoKL.2 hLKcard).symm