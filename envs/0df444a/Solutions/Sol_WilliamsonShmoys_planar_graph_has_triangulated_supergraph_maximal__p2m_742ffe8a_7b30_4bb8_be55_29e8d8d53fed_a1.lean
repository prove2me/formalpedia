-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph_maximal__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:32.27149+00:00
-- url     : https://prove2.me/submissions/5db17f43-aae7-4023-bc87-99e0aa5e56cd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

open WilliamsonShmoys

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      (∀ Q : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        (∀ u v, P.Adj u v → Q.Adj u v) →
        ∀ u v, Q.Adj u v → P.Adj u v) := by
  classical
  let p : SimpleGraph V → Prop := fun G =>
    WilliamsonShmoys.HasPlanarDrawingOn G ∧ ∀ u v, N.Adj u v → G.Adj u v
  have hex : ∃ G : SimpleGraph V, p G := by
    exact ⟨N, hN, fun _ _ h => h⟩
  obtain ⟨P, hdec, hP, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2 hex
  letI : DecidableRel P.Adj := hdec
  refine ⟨P, hP.1, hP.2, ?_⟩
  intro Q hQ hPQ u v huv
  have hq : p Q := ⟨hQ, fun x y hxy => hPQ x y (hP.2 x y hxy)⟩
  have heq : P = Q := (SimpleGraph.IsExtremal.le_iff_eq (show P.IsExtremal p from ⟨hP, hmax⟩) hq).1 hPQ
  rw [heq]
  exact huv