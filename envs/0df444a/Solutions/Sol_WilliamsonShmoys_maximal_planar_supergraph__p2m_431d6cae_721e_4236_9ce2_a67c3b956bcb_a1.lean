-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:40:05.891016+00:00
-- url     : https://prove2.me/submissions/f467ba3e-2101-4d81-b368-10eda383a089

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K = H := by
  obtain ⟨H, -, hH⟩ := Finite.exists_le_maximal
    (p := fun S : SimpleGraph V => G ≤ S ∧ HasPlanarDrawingOn S) (a := G) ⟨le_rfl, hG⟩
  refine ⟨H, SimpleGraph.edgeSet_subset_edgeSet.mpr hH.1.1, hH.1.2, fun K hK hKd => ?_⟩
  have h1 : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hK
  exact le_antisymm (hH.2 ⟨hH.1.1.trans h1, hKd⟩ h1) h1
