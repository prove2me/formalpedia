-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:31:47.643986+00:00
-- url     : https://prove2.me/submissions/9e813620-c15a-4b56-8428-be31465ea53b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hG : P G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      P H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        P K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by 
  classical
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal (p := P) hG
  refine ⟨H, fun u v h => hGH h, hmax.1, fun K hHK hK => le_antisymm (hmax.2 hK (fun u v h => hHK h))
    (fun u v h => hHK h), Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)⟩
