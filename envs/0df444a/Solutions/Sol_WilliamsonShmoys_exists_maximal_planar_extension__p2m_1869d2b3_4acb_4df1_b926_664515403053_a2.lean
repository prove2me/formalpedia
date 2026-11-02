-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:09:26.033234+00:00
-- url     : https://prove2.me/submissions/4b8f9e1a-e854-45a1-b071-a4d1a5eda847

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_FiniteMaximizer__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
import Theorems.Thm_SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  let r : SimpleGraph V → SimpleGraph V → Prop := fun G K => ∀ u v, G.Adj u v → K.Adj u v
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  let w : SimpleGraph V → Nat := fun G => G.edgeFinset.card
  have htrans : ∀ G K L, r G K → r K L → r G L := by
    intro G K L hGK hKL u v huv
    exact hKL u v (hGK u v huv)
  have hrefl : ∀ G, r G G := by
    intro G u v huv
    exact huv
  have hmono : ∀ G K, r G K → w G ≤ w K := by
    intro G K h
    exact (SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3 G K h).1
  have hstrict : ∀ G K, r G K → ¬ r K G → w G < w K := by
    intro G K h hk
    exact (SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3 G K h).2 hk
  obtain ⟨K, hHK, hPK, hmax, hcard⟩ :=
    FiniteMaximizer__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
      r P w hrefl htrans hmono hstrict H hdraw
  refine ⟨K, ?_, hPK, ?_, ?_⟩
  · exact hHK
  · intro L hKL hPL u v huv
    exact hmax L hKL hPL u v huv
  · exact hcard