-- Prove2me | solution 1 for WilliamsonShmoys.connected_extension_of_planar_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:44:32.726349+00:00
-- url     : https://prove2.me/submissions/0839e5c3-d6e9-4b90-93bd-2a44efa1badb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hstep : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ¬ G.Connected →
      ∃ H : SimpleGraph V,
        (∀ u v, G.Adj u v → H.Adj u v) ∧
        WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard < H.edgeSet.ncard) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      N.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V =>
      M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeSet.ncard) ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hM⟩⟩
  obtain ⟨hMQ, hQ⟩ := (Finset.mem_filter.mp hQm).2
  have hmono : M.edgeSet.ncard ≤ Q.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMQ) (Set.toFinite _)
  by_cases hc : Q.Connected
  · exact ⟨Q, fun u v h => hMQ h, hc, hQ, hmono⟩
  · obtain ⟨H, hQH, hH, hlt⟩ := hstep Q hQ hc
    have hle : M ≤ H := fun u v h => hQH u v (hMQ h)
    have := hmax H (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle, hH⟩)
    omega
