-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:19:27.703814+00:00
-- url     : https://prove2.me/submissions/0caecce4-e136-4b26-9dcb-b1c9c0292a96

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) := by
  classical
  let s : Set (SimpleGraph V) := {H | G ≤ H ∧ HasPlanarDrawingOn H}
  have hs : s.Finite := Set.toFinite s
  have hn : s.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hmem, hmax⟩ := hs.exists_maximal hn
  refine ⟨H, hmem.1, hmem.2, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hmem.1), ?_⟩
  intro K hHK hK
  exact hmax ⟨hmem.1.trans hHK, hK⟩ hHK

