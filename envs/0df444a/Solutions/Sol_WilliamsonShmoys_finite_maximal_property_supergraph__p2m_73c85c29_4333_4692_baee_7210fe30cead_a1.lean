-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_property_supergraph__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:11:53.249996+00:00
-- url     : https://prove2.me/submissions/b29bebf6-1896-4d20-988c-a978b1463880

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem _root_.solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ N : SimpleGraph V,
      P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by
  have hF : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  obtain ⟨G, hG⟩ := hP
  obtain ⟨N, hN⟩ := (Set.toFinite {N : SimpleGraph V | P N}).exists_maximal ⟨G, hG⟩
  exact ⟨N, hN.1, fun K hNK hK => le_antisymm (hN.2 hK hNK) hNK⟩
