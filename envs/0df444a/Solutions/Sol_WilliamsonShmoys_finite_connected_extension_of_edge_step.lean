-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_extension_of_edge_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:32:55.650632+00:00
-- url     : https://prove2.me/submissions/1833144b-1a5d-4587-911e-03bbeaefee11

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P T)
    (hStep : ∀ G : SimpleGraph V, T ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ S : SimpleGraph V, T ≤ S ∧ P S ∧ S.Connected := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => T ≤ G ∧ P G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hP⟩⟩
  obtain ⟨hTQ, hQ⟩ : T ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hTQ, hQ, ?_⟩
  by_contra hc
  obtain ⟨R, hQR, hR, u, v, hnr, hadj⟩ := hStep Q hTQ hQ hc
  have hne : Q ≠ R := by
    rintro rfl
    exact hnr hadj.reachable
  have hlt : Q < R := lt_of_le_of_ne hQR hne
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTQ.trans hQR, hR⟩)
  omega
