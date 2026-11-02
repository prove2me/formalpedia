-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:10:30.598698+00:00
-- url     : https://prove2.me/submissions/be798267-918d-4431-8f2a-d95cbc562aa9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hH : HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
          K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) := {G | H ≤ G ∧ HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨H, by simp [S, hH]⟩
  obtain ⟨K, hK, hKmax⟩ := hSfinite.exists_maximal hSne
  rcases hK with ⟨hHK, hKdrawing⟩
  refine ⟨K, inferInstance, hHK, hKdrawing, ?_⟩
  intro L dL hKL hLdrawing
  have hL : L ∈ S := ⟨hHK.trans hKL, hLdrawing⟩
  have hLK : L ≤ K := hKmax hL hKL
  exact le_antisymm hLK hKL