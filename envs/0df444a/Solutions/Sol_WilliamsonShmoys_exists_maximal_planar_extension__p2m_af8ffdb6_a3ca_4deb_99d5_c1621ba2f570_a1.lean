-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:05.035737+00:00
-- url     : https://prove2.me/submissions/fbfb0e20-493f-4d8b-b825-c400e0b9c66d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  classical
  let P : SimpleGraph V → Prop := fun G => L ≤ G ∧ HasPlanarDrawingOn G
  have hPL : P L := ⟨le_rfl, hL⟩
  have hfinite : {G : SimpleGraph V | P G}.Finite :=
    Set.finite_univ.subset (by intro G hG; trivial)
  obtain ⟨M, hMP, hmax⟩ :=
    Set.exists_max_image {G : SimpleGraph V | P G} (fun G => G.edgeFinset.card)
      hfinite ⟨L, hPL⟩
  refine ⟨M, hMP.1, hMP.2, ?_⟩
  intro N hMN hN
  have hPN : P N := ⟨hMP.1.trans hMN, hN⟩
  have hNmem : N ∈ {G : SimpleGraph V | P G} := hPN
  have hcardEdges : N.edgeFinset.card ≤ M.edgeFinset.card := hmax N hNmem
  have hedge : M.edgeFinset = N.edgeFinset :=
    Finset.eq_of_subset_of_card_le
      (SimpleGraph.edgeFinset_subset_edgeFinset.2 hMN) hcardEdges
  have hgraph : M = N := SimpleGraph.edgeFinset_inj.1 hedge
  exact le_of_eq hgraph.symm