-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_euler_extension_exists_maximal_extension__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:30:07.215198+00:00
-- url     : https://prove2.me/submissions/e3ce3801-0cc2-4099-9629-2154303b0c32

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_max_ncard_extension__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
import Theorems.Thm_WilliamsonShmoys_graph_eq_of_le_and_ncard__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let P : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hPK : P K := ⟨le_rfl, hK⟩
  obtain ⟨L, hPL, hmax⟩ :=
    WilliamsonShmoys.max_ncard_extension__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
      P ⟨K, hPK⟩
  refine ⟨L, hPL.1, hPL.2, ?_⟩
  intro M hLM hM
  have hPM : P M := ⟨le_trans hPL.1 hLM, hM⟩
  have hcard := hmax M hPM
  exact WilliamsonShmoys.graph_eq_of_le_and_ncard__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
    hLM hcard
