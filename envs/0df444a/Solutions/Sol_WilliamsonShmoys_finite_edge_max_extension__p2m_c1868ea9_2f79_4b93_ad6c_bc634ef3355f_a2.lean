-- Prove2me | solution 1 for WilliamsonShmoys.finite_edge_max_extension__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:26.30784+00:00
-- url     : https://prove2.me/submissions/6d623f18-d857-40f5-9365-7b35588a4305

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V,
      P H ∧ K ≤ H ∧
        ∀ G : SimpleGraph V, P G → K ≤ G →
          G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let S := {G : SimpleGraph V // P G ∧ K ≤ G}
  have hinj : Function.Injective (fun G : S => G.1.edgeSet.toFinset) := by
    intro G H h
    apply Subtype.ext
    exact SimpleGraph.edgeFinset_inj.mp (by simpa [SimpleGraph.edgeFinset] using h)
  haveI : Finite S :=
    Finite.of_injective (fun G : S => G.1.edgeSet.toFinset) hinj
  letI : Fintype S := Fintype.ofFinite S
  have hne : (Finset.univ : Finset S).Nonempty := by
    exact ⟨⟨K, hK, le_rfl⟩, Finset.mem_univ _⟩
  obtain ⟨H, hH, hmax⟩ :=
    Finset.exists_max_image Finset.univ
      (fun G : S => G.1.edgeSet.ncard) hne
  refine ⟨H.1, H.2.1, H.2.2, ?_⟩
  intro G hG hKG
  exact hmax ⟨G, hG, hKG⟩ (Finset.mem_univ _)