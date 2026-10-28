-- Prove2me | solution 2 for WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:32:05.644998+00:00
-- url     : https://prove2.me/submissions/27904054-d1fb-4e01-a896-a0ee89bc2a40

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by 
  classical
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hG
  refine ⟨H, fun u v h => hGH h, hmax.1, fun u v => ⟨(Classical.choice (hconn u v)).mapLe hGH⟩,
    fun K hHK hK => le_antisymm (hmax.2 hK (fun u v h => hHK h)) (fun u v h => hHK h),
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)⟩
