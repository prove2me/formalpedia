-- Prove2me | solution 1 for WilliamsonShmoys.planar_separated_bridge_extension__p2m_cb139db2_73c1_451e_b6a9_3cccdec58a46_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:02:56.795387+00:00
-- url     : https://prove2.me/submissions/cfd286fd-02a0-4fa2-a8ac-f1c2d45df898
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_unreachable_pair_of_disconnected__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4
import Theorems.Thm_WilliamsonShmoys_planar_bridge_for_unreachable_pair__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hdisc : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Adj u v ∧ ∃ G : SimpleGraph V,
      H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v ∧
        ¬ Relation.ReflTransGen H.Adj u v := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.unreachable_pair_of_disconnected__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4
      H hV hdisc
  obtain ⟨G, hsub, hG, hadj⟩ :=
    WilliamsonShmoys.planar_bridge_for_unreachable_pair__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4
      H u v hH huv
  exact ⟨u, v, (fun hadjH => huv (Relation.ReflTransGen.single hadjH)),
    G, hsub, hG, hadj, huv⟩