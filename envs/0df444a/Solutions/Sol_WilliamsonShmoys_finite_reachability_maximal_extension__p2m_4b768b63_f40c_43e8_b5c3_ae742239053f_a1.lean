-- Prove2me | solution 1 for WilliamsonShmoys.finite_reachability_maximal_extension__p2m_4b768b63_f40c_43e8_b5c3_ae742239053f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:52:15.93315+00:00
-- url     : https://prove2.me/submissions/275fd237-ef67-4e49-a29f-e6ef43cba7d7

import Mathlib

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hP : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, G ≤ K → P K → G.edgeSet.ncard ≤ K.edgeSet.ncard →
        (∀ u v, H.Reachable u v → K.Reachable u v) → ∀ u v, K.Reachable u v → H.Reachable u v) := by
  classical
  let reachPairs (H : SimpleGraph V) : Finset (V × V) :=
    Finset.univ.filter fun p => H.Reachable p.1 p.2
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H => G ≤ H ∧ P H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard
  have hG : G ∈ admissible := by
    simp [admissible, hP]
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image admissible (fun H => (reachPairs H).card) ⟨G, hG⟩
  have hHadm : G ≤ H ∧ P H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard := by
    simpa [admissible] using hHmem
  refine ⟨H, hHadm.1, hHadm.2.1, hHadm.2.2, ?_⟩
  intro K hGK hPK hKcard hHK u v hKreach
  by_contra hH
  have hKmem : K ∈ admissible := by
    simp [admissible, hGK, hPK, hKcard]
  have hsub : reachPairs H ⊆ reachPairs K := by
    intro p hp
    simp only [reachPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hHK p.1 p.2 hp
  have hne : reachPairs H ≠ reachPairs K := by
    intro heq
    have hmemK : (u, v) ∈ reachPairs K := by
      simp [reachPairs, hKreach]
    have hmemH : (u, v) ∈ reachPairs H := heq.symm ▸ hmemK
    exact hH (by simpa [reachPairs] using hmemH)
  have hstrict : reachPairs H ⊂ reachPairs K :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  have hcardlt : (reachPairs H).card < (reachPairs K).card := Finset.card_lt_card hstrict
  have hmaxK := hmax K hKmem
  omega