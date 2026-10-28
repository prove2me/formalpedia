-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:25:58.861068+00:00
-- url     : https://prove2.me/submissions/6c66f51f-66ed-4c4b-ab81-c1a6afce50f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_of_downward_closed_property

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ P := by
  apply WilliamsonShmoys.exists_maximal_simpleGraph_of_downward_closed_property
    (Good := WilliamsonShmoys.HasPlanarDrawingOn) (G := G)
  · intro H K hHK hK
    rcases hK with ⟨p, arc, hp, hedge, hcross⟩
    exact ⟨p, arc, hp,
      (fun u v huv hadj => hedge u v huv (hHK hadj)),
      (fun u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq =>
        hcross u v x y huv hxy (hHK hadj₁) (hHK hadj₂) hne t ht s hs heq)⟩
  · exact hG