-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:35:00.783126+00:00
-- url     : https://prove2.me/submissions/2967e938-b7a2-4190-b159-b917a0d5c407

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hMax : forall X : SimpleGraph V, HasPlanarDrawingOn X ->
      (forall u v, W.Adj u v -> X.Adj u v) -> X = W)
    (hCard : 3 <= Fintype.card V) :
    (W.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hex :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion W hW hCard
  cases hex with
  | intro K h =>
    cases h with
    | intro hWK h =>
      cases h with
      | intro hK hcount =>
        have hKW : K = W := hMax K hK (fun u v huv => hWK huv)
        simpa [hKW] using hcount