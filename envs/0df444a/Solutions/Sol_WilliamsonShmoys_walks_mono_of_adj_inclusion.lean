-- Prove2me | solution 1 for WilliamsonShmoys.walks_mono_of_adj_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:29:54.628481+00:00
-- url     : https://prove2.me/submissions/21287fbe-8131-4e80-9e5a-b46225551b8c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} {G H : SimpleGraph V}
    (hGH : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v)
    {u v : V} (hwalk : Nonempty (G.Walk u v)) :
    Nonempty (H.Walk u v) := by
  rcases hwalk with ⟨p⟩
  induction p with
  | nil =>
      exact ⟨SimpleGraph.Walk.nil⟩
  | @cons a b c hadj p ih =>
      rcases ih with ⟨q⟩
      exact ⟨SimpleGraph.Walk.cons (hGH hadj) q⟩