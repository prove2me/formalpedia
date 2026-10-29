-- Prove2me | solution 1 for WilliamsonShmoys.finite_extension_maximal_property__p2m_73c85c29_4333_4692_baee_7210fe30cead_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:10:00.294778+00:00
-- url     : https://prove2.me/submissions/aa4a1fde-52d7-4362-a9e7-5774b6c066ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem _root_.solution
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (P : SimpleGraph V -> Prop)
    (hP : exists G : SimpleGraph V, M <= G /\ P G) :
    exists N : SimpleGraph V,
      M <= N /\
      P N /\
      forall K : SimpleGraph V, N <= K -> P K -> K = N := by
  have hF : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  obtain ⟨G, hG⟩ := hP
  obtain ⟨N, hN⟩ := (Set.toFinite {N : SimpleGraph V | M ≤ N ∧ P N}).exists_maximal ⟨G, hG⟩
  exact ⟨N, hN.1.1, hN.1.2, fun K hNK hPK => le_antisymm (hN.2 ⟨hN.1.1.trans hNK, hPK⟩ hNK) hNK⟩
