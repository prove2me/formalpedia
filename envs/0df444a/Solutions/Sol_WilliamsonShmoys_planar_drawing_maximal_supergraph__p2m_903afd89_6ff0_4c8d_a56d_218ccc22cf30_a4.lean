-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:02:35.151485+00:00
-- url     : https://prove2.me/submissions/a9339b93-ce84-40dd-aecf-5a1db7b841ff

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (∀ Q : SimpleGraph V, N ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ N) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hMmem : M ∈ S := by
    simp [S, hplanar]
  let C : Finset ℕ := S.image fun G : SimpleGraph V => G.edgeSet.ncard
  have hC : C.Nonempty := by
    exact ⟨M.edgeSet.ncard, Finset.mem_image.mpr ⟨M, hMmem, rfl⟩⟩
  let c : ℕ := C.max' hC
  have hcmax : ∀ x ∈ C, x ≤ c := by
    intro x hx
    simpa [c] using (Finset.le_max' C x hx)
  have hc_mem : c ∈ C := by
    simpa [c] using (Finset.max'_mem C hC)
  change c ∈ S.image (fun G : SimpleGraph V => G.edgeSet.ncard) at hc_mem
  obtain ⟨N, hNS, hNc⟩ := Finset.mem_image.mp hc_mem
  have hNprops : M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N :=
    (Finset.mem_filter.mp hNS).2
  refine ⟨N, hNprops.1, hNprops.2, ?_, ?_⟩
  · exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hNprops.1)
  · intro Q hNQ hQplanar
    have hQmem : Q ∈ S := by
      simp [S, hNprops.1.trans hNQ, hQplanar]
    have hQc : Q.edgeSet.ncard ≤ c :=
      hcmax _ (Finset.mem_image.mpr ⟨Q, hQmem, rfl⟩)
    have hQN : Q ≤ N := by
      by_contra hnot
      have hne : N ≠ Q := by
        intro heq
        apply hnot
        simpa [heq] using (le_rfl : N ≤ N)
      have hlt : N < Q := lt_of_le_of_ne hNQ hne
      have hcardlt : N.edgeSet.ncard < Q.edgeSet.ncard :=
        Set.ncard_lt_ncard (SimpleGraph.edgeSet_strict_mono hlt)
      rw [hNc] at hcardlt
      omega
    exact hQN