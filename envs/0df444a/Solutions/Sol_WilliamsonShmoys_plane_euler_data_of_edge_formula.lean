-- Prove2me | solution 1 for WilliamsonShmoys.plane_euler_data_of_edge_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:18:01.641603+00:00
-- url     : https://prove2.me/submissions/0d98d62c-f442-4a60-8aa1-24a28c24a36f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlaneEulerData

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    WilliamsonShmoys.HasPlaneEulerData K := by
  let n := Fintype.card V
  let e := K.edgeSet.ncard
  have hn : 3 ≤ n := hV
  have he : e + 6 = 3 * n := hE
  refine ⟨Fin (2 * n - 4), inferInstance, ?_, ?_⟩
  · simp only [Fintype.card_fin]
    omega
  · simp only [Fintype.card_fin]
    omega