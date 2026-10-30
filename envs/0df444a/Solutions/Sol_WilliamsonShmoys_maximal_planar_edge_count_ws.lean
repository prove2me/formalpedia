-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_ws
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:10:34.701997+00:00
-- url     : https://prove2.me/submissions/e25d7875-5d4b-4317-8835-fe8eaf525b4d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_tight_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V), H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.exists_planar_tight_supergraph H hH hcard
  have hKH : K ≤ H := hmax K hHK hKplanar
  have hEq : H = K := le_antisymm hHK hKH
  rw [hEq]
  exact hKcount