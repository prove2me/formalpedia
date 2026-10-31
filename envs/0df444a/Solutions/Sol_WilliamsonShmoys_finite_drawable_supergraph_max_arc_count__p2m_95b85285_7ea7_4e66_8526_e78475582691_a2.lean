-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_supergraph_max_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:15:50.783989+00:00
-- url     : https://prove2.me/submissions/e2069d53-d09f-4bb4-9e7d-665cfbefab81

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H →
        Nat.card {p : V × V // H.Adj p.1 p.2} ≤
          Nat.card {p : V × V // K.Adj p.1 p.2} := by
  classical
  let candidates : Set (SimpleGraph V) :=
    {H | G ≤ H ∧ HasPlanarDrawingOn H}
  have hfinite : candidates.Finite := Set.toFinite candidates
  have hnonempty : candidates.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hK, hmax⟩ :=
    Set.exists_max_image candidates
      (fun H => Nat.card {p : V × V // H.Adj p.1 p.2}) hfinite hnonempty
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro H hGH hH
  exact hmax H ⟨hGH, hH⟩