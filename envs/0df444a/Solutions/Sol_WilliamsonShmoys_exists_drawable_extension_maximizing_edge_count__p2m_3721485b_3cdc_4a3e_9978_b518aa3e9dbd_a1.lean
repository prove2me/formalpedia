-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_extension_maximizing_edge_count__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:56:27.037225+00:00
-- url     : https://prove2.me/submissions/46da9a52-8636-47be-88fa-8a4baadb8d08

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, L ≤ U → HasPlanarDrawingOn U →
        Nat.card U.edgeSet ≤ Nat.card T.edgeSet := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun T => L ≤ T ∧ HasPlanarDrawingOn T
  have hLmem : L ∈ candidates := by
    simp [candidates, hL]
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image candidates (fun T => Nat.card T.edgeSet) ⟨L, hLmem⟩
  refine ⟨T, (Finset.mem_filter.mp hTmem).2.1,
    (Finset.mem_filter.mp hTmem).2.2, ?_⟩
  intro U hLU hU
  apply hTmax U
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ U, ⟨hLU, hU⟩⟩