-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_pair_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:31:10.461063+00:00
-- url     : https://prove2.me/submissions/0e0acbcb-3d28-4b6f-8ead-7ab55df51e70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_augmentation_from_connector_witnesses
import Theorems.Thm_WilliamsonShmoys_planar_connector_witnesses

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v) :
    ∃ K : SimpleGraph V,
      (∀ ⦃x y⦄, H.Adj x y → K.Adj x y) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  have hgeom :=
    WilliamsonShmoys.planar_connector_witnesses H hH u v hdisconnected
  exact WilliamsonShmoys.planar_augmentation_from_connector_witnesses
    H hH u v hdisconnected hgeom