-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:28.688011+00:00
-- url     : https://prove2.me/submissions/14942e1f-8a02-4b3a-be17-d416719af1d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_property_maximal_supergraph__p2m_b1eaa68f_d3bc_482e_8876_be28beef9c21_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists (fun T : SimpleGraph V =>
      And (LE.le G T)
        (And (WilliamsonShmoys.HasPlanarDrawingOn T)
          (forall U : SimpleGraph V, LE.le T U ->
            WilliamsonShmoys.HasPlanarDrawingOn U -> LE.le U T))) := by
  have hhered : forall A B : SimpleGraph V, LE.le A B ->
      WilliamsonShmoys.HasPlanarDrawingOn B -> WilliamsonShmoys.HasPlanarDrawingOn A := by
    intro A B hAB hB
    apply Exists.elim hB
    intro p hp
    apply Exists.elim hp
    intro arc hprops
    have hinj := And.left hprops
    have hdraw := And.left (And.right hprops)
    have hcross := And.right (And.right hprops)
    exact Exists.intro p (Exists.intro arc (And.intro hinj
      (And.intro
        (by intro u v huv hadj; exact hdraw u v huv (hAB hadj))
        (by intro u v x y huv hxy hadjA hadjB hne t ht s hs heq;
            exact hcross u v x y huv hxy (hAB hadjA) (hAB hadjB) hne t ht s hs heq))))
  exact WilliamsonShmoys.finite_hereditary_property_maximal_supergraph__p2m_b1eaa68f_d3bc_482e_8876_be28beef9c21_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) hhered G hG