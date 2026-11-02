-- Prove2me | solution 1 for WilliamsonShmoys.finite_edge_maximal_extension__p2m_89ca6453_1971_4f8a_b52b_11a113611db9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:21.48641+00:00
-- url     : https://prove2.me/submissions/72588574-08ec-4c97-8749-c7c50d3a0e68

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_mem_of_finite__p2m_d662b61a_1996_4a06_ab90_0abefab2bcb6_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ L : SimpleGraph V, G.edgeSet ⊆ L.edgeSet ∧ P L ∧
      ∀ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet → P K →
        K.edgeSet = L.edgeSet := by
  classical
  let S : Set (SimpleGraph V) := {K | G ≤ K ∧ P K}
  have hS : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨L, hL, hmax⟩ :=
    exists_maximal_mem_of_finite__p2m_d662b61a_1996_4a06_ab90_0abefab2bcb6_a1 S hS
  refine ⟨L, SimpleGraph.edgeSet_mono hL.1, hL.2, ?_⟩
  intro K hLK hPK
  have hLK' : L ≤ K := by
    intro u v huv
    have hu : s(u, v) ∈ L.edgeSet := by simpa using huv
    have hv : s(u, v) ∈ K.edgeSet := hLK hu
    simpa using hv
  have hKL : K ≤ L := le_of_eq (hmax K ⟨le_trans hL.1 hLK', hPK⟩ hLK')
  have hsubset : K.edgeSet ⊆ L.edgeSet := SimpleGraph.edgeSet_mono hKL
  exact Set.Subset.antisymm hsubset hLK