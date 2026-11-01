-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:08.046362+00:00
-- url     : https://prove2.me/submissions/2e173885-1a84-42df-bfe1-e37989f55ae6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hKmem : K ∈ candidates := by
    simp [candidates, hK]
  let edgeCounts : Finset ℕ := candidates.image fun G => G.edgeFinset.card
  have hCountsNonempty : edgeCounts.Nonempty := by
    exact ⟨K.edgeFinset.card, Finset.mem_image.mpr ⟨K, hKmem, rfl⟩⟩
  obtain ⟨M, hMmem, hMcard⟩ :=
    Finset.mem_image.mp (Finset.max'_mem edgeCounts hCountsNonempty)
  have hMprops : K ≤ M ∧ HasPlanarDrawingOn M := by
    simpa [candidates] using hMmem
  refine ⟨M, hMprops.1, hMprops.2, ?_⟩
  intro N hMN hNplanar
  have hKN : K ≤ N := le_trans hMprops.1 hMN
  have hNmem : N ∈ candidates := by
    simp [candidates, hKN, hNplanar]
  have hNcount : N.edgeFinset.card ∈ edgeCounts :=
    Finset.mem_image.mpr ⟨N, hNmem, rfl⟩
  have hNle : N.edgeFinset.card ≤ M.edgeFinset.card := by
    have hle := Finset.le_max' edgeCounts N.edgeFinset.card hNcount
    simpa [hMcard] using hle
  have hsubset : M.edgeFinset ⊆ N.edgeFinset :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hMN
  have hedge : M.edgeFinset = N.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hNle
  exact SimpleGraph.edgeFinset_inj.mp hedge.symm