-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_edge_maximizer__p2m_0117d7a7_55cc_4763_b339_05a114946f12_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:52:37.720102+00:00
-- url     : https://prove2.me/submissions/ba647d6b-8243-4d01-8207-bcc871b0bb9b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
            N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  classical
  let p : SimpleGraph V → Prop := fun G =>
    L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨L, le_rfl, hL⟩
  obtain ⟨M, _, hM⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := p)).2 hp
  rcases hM with ⟨hMp, hMmax⟩
  refine ⟨M, hMp.1, hMp.2, ?_⟩
  intro N hMN hN
  have hNp : p N := ⟨le_trans hMp.1 hMN, hN⟩
  have hcard : N.edgeFinset.card ≤ M.edgeFinset.card := hMmax hNp
  have hNcard : N.edgeSet.ncard = N.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hMcard : M.edgeSet.ncard = M.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hNcard, hMcard]
  exact hcard