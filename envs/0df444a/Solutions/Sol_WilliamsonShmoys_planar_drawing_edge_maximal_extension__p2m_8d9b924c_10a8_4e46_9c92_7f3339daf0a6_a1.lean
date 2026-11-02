-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T21:06:32.982071+00:00
-- url     : https://prove2.me/submissions/a58fadd2-ae56-4464-9c5b-fe1b9dc63b59

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by
  classical
  let S : Set (SimpleGraph V) := fun G => M ≤ G ∧ HasPlanarDrawingOn G
  have hS : S.Nonempty := ⟨M, le_rfl, hM⟩
  have hfin : S.Finite := Set.Finite.subset Set.finite_univ (by
    intro G hG
    trivial)
  let hex := hfin.exists_maximal hS
  let N : SimpleGraph V := Classical.choose hex
  have hN : S N := (Classical.choose_spec hex).1
  have hmax := (Classical.choose_spec hex).2
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro K hNK hK
  have hKmem : S K := ⟨le_trans hN.1 hNK, hK⟩
  exact le_antisymm (hmax hKmem hNK) hNK