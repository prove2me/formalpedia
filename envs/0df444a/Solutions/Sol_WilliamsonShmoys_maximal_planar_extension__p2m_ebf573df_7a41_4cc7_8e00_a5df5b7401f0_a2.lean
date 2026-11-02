-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:29.127195+00:00
-- url     : https://prove2.me/submissions/598542f3-13a5-4f76-af65-6fa3c498bbc4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeFinset ⊆ M.edgeFinset ∧
      ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn N →
        M.edgeFinset ⊆ N.edgeFinset → N.edgeFinset ⊆ M.edgeFinset := by
  classical
  let edgeSet : SimpleGraph V → Finset (Sym2 V) := fun G => G.edgeFinset
  let A := {G : SimpleGraph V //
    WilliamsonShmoys.HasPlanarDrawingOn G ∧ edgeSet L ⊆ edgeSet G}
  have hne : (Finset.univ : Finset A).Nonempty := by
    refine ⟨⟨L, hL, ?_⟩, Finset.mem_univ _⟩
    intro e he
    simpa [edgeSet] using he
  obtain ⟨m, hm_mem, hm_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset A)
      (fun G => (edgeSet G.1).card) hne
  refine ⟨m.1, Classical.decRel _, m.2.1, ?_, ?_⟩
  · intro e he
    have heL : e ∈ edgeSet L := by simpa [edgeSet] using he
    simpa [edgeSet] using m.2.2 heL
  · intro N dN hN hMN
    have hMN' : edgeSet m.1 ⊆ edgeSet N := by
      intro e he
      have heN := hMN (by simpa [edgeSet] using he)
      simpa [edgeSet] using heN
    have hLN : edgeSet L ⊆ edgeSet N := by
      intro e he
      have heM : e ∈ edgeSet m.1 := m.2.2 he
      exact hMN' heM
    have hNmem : (⟨N, hN, hLN⟩ : A) ∈ (Finset.univ : Finset A) :=
      Finset.mem_univ _
    by_contra hNM
    have hss : edgeSet m.1 ⊂ edgeSet N :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hMN', by
        intro heq
        apply hNM
        simpa [edgeSet, heq]⟩
    have hlt := Finset.card_lt_card hss
    have hcard := hm_max ⟨N, hN, hLN⟩ hNmem
    exact (not_lt_of_ge hcard) hlt