-- Prove2me | solution 1 for WilliamsonShmoys.finite_extension_by_pair_connections_cert38ffb807
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:36:13.782787+00:00
-- url     : https://prove2.me/submissions/e964a4f1-8b03-4635-8336-1c65cbb0b9b3

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (P : SimpleGraph V → Prop) (hPK : P K)
    (hstep : ∀ (G : SimpleGraph V), K ≤ G → P G →
      ∀ u v : V, u ≠ v → ¬ Relation.ReflTransGen G.Adj u v →
        ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ Relation.ReflTransGen H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => K ≤ G ∧ P G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hPK⟩⟩
  obtain ⟨hTQ, hQ⟩ : K ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hTQ, ?_, hQ⟩
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, hne⟩
  by_cases huv : u = v
  · subst huv; rfl
  rw [SimpleGraph.reachable_iff_reflTransGen]
  by_contra hnr
  obtain ⟨R, hle, hR, hr⟩ := hstep Q hTQ hQ u v huv hnr
  have hlt : Q < R := lt_of_le_of_ne hle (by rintro rfl; exact hnr hr)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTQ.trans hlt.le, hR⟩)
  omega
