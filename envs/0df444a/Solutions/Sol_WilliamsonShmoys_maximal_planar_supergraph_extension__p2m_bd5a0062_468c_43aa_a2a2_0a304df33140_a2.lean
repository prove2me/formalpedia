-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_extension__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:19.133829+00:00
-- url     : https://prove2.me/submissions/43bab7ba-fd65-48a5-8600-4f0c661a87f6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H) := by
  classical
  let p : SimpleGraph V → Prop := fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨K, le_rfl, hDraw⟩
  obtain ⟨H, _hDecidable, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  refine ⟨H, hExt.1.1, hExt.1.2, ?_⟩
  intro G hHG hDrawG
  exact ((SimpleGraph.IsExtremal.le_iff_eq hExt ⟨hExt.1.1.trans hHG, hDrawG⟩).mp hHG).symm