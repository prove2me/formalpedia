-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_single_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:17:31.783018+00:00
-- url     : https://prove2.me/submissions/61f35dbf-ca92-478d-a995-39ed8cd039a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_pair_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ ∀ u v, Relation.ReflTransGen H.Adj u v) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by
  have hp : ∃ u v : V, ¬ Relation.ReflTransGen H.Adj u v := by
    rcases not_forall.mp hdisconnected with ⟨u, hu⟩
    rcases not_forall.mp hu with ⟨v, huv⟩
    exact ⟨u, v, huv⟩
  obtain ⟨u, v, huv⟩ := hp
  obtain ⟨K, hold, hnew, huvK, hplanar⟩ :=
    WilliamsonShmoys.planar_disconnected_pair_augmentation H hH u v huv
  exact ⟨K, hold, hnew, hplanar⟩