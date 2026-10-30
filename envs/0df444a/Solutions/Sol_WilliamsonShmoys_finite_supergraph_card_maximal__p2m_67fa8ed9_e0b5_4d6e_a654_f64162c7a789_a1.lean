-- Prove2me | solution 1 for WilliamsonShmoys.finite_supergraph_card_maximal__p2m_67fa8ed9_e0b5_4d6e_a654_f64162c7a789_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:33:54.308657+00:00
-- url     : https://prove2.me/submissions/11fe4789-ddca-4416-9ba1-47cac28ae52d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       H.edgeFinset.card ≤ K.edgeFinset.card) ∧
      (∀ L : SimpleGraph V, K ≤ L → P L →
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
         letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         L.edgeFinset.card ≤ K.edgeFinset.card)) := by
  classical
  let Q : SimpleGraph V → Prop := fun G => H ≤ G ∧ P G
  obtain ⟨K, _hdecK, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := Q)).2
      ⟨H, le_rfl, hP⟩
  have hQK : Q K := hK.1
  refine ⟨K, hQK.1, hQK.2, ?_, ?_⟩
  · convert! hK.2 (show Q H from ⟨le_rfl, hP⟩)
  · intro L hKL hPL
    convert! hK.2 (show Q L from ⟨hQK.1.trans hKL, hPL⟩)