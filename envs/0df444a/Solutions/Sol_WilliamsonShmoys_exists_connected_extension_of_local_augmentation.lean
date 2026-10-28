-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_extension_of_local_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:47:18.958778+00:00
-- url     : https://prove2.me/submissions/050d120b-057d-4343-91d7-e96e2559223d

import Mathlib

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P X)
    (hAugment :
      ∀ G : SimpleGraph V, X ≤ G → P G → ¬ G.Connected →
        ∃ H : SimpleGraph V, G < H ∧ P H) :
    ∃ Y : SimpleGraph V,
      X.edgeSet.ncard ≤ Y.edgeSet.ncard ∧ Y.Connected ∧ P Y := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => X ≤ G ∧ P G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hP⟩⟩
  obtain ⟨hTQ, hQ⟩ : X ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hTQ) (Set.toFinite _), ?_, hQ⟩
  by_contra hc
  obtain ⟨R, hlt, hR⟩ := hAugment Q hTQ hQ hc
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTQ.trans hlt.le, hR⟩)
  omega
end WilliamsonShmoys

