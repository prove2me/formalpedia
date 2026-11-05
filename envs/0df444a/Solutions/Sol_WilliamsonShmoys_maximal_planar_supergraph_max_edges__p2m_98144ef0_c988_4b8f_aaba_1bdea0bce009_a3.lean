-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_max_edges__p2m_98144ef0_c988_4b8f_aaba_1bdea0bce009_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:22:20.894414+00:00
-- url     : https://prove2.me/submissions/7772833b-3ca1-405c-bb7f-586b13f68b0d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M →
        Set.ncard M.edgeSet ≤ Set.ncard L.edgeSet) := by
  classical
  let s : Set (SimpleGraph V) := {N | K ≤ N ∧ HasPlanarDrawingOn N}
  have hsne : s.Nonempty := ⟨K, by simp [s, hDraw]⟩
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨L, hLs, hmax⟩ :=
    Set.exists_max_image s (fun N : SimpleGraph V => Set.ncard N.edgeSet) hsfinite hsne
  have hLs' : K ≤ L ∧ HasPlanarDrawingOn L := by simpa [s] using hLs
  refine ⟨L, hLs'.1, hLs'.2, ?_⟩
  intro M hKM hM
  exact hmax M (by simpa [s] using (show K ≤ M ∧ HasPlanarDrawingOn M from ⟨hKM, hM⟩))
