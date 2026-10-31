-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:15:06.712509+00:00
-- url     : https://prove2.me/submissions/98d2ce5a-503e-440a-8f2d-bf1bed362e09

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_above_of_finite__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
import Theorems.Thm_finite_simpleGraph_of_fintype__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, M ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by
  letI : Finite (SimpleGraph V) := finite_simpleGraph_of_fintype__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  obtain ⟨S, hMS, hS, hmax⟩ :=
    exists_maximal_above_of_finite__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
      WilliamsonShmoys.HasPlanarDrawingOn M hM
  refine ⟨S, hMS, hS, ?_⟩
  intro T hST hT
  exact hmax T hST hT