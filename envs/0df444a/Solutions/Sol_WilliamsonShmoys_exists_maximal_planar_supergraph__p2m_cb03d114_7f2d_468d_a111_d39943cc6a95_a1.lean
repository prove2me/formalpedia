-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:12.995551+00:00
-- url     : https://prove2.me/submissions/4cc0e872-5446-4a75-b043-e3cc7958392b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ P : SimpleGraph V,
        (∀ u v, N.Adj u v → P.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        ∀ u v, P.Adj u v → N.Adj u v) := by
  classical
  let good : SimpleGraph V → Prop := fun G =>
    (∀ u v, M.Adj u v → G.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  let candidates : Finset (SimpleGraph V) := Finset.univ.filter good
  have hcan : candidates.Nonempty := by
    refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨by intro u v huv; exact huv, hM⟩
  obtain ⟨N, hNc, hmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeFinset.card) hcan
  have hN : good N := (Finset.mem_filter.mp hNc).2
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro P hNP hP u v hPuv
  have hMP : ∀ x y, M.Adj x y → P.Adj x y := by
    intro x y hMxy
    exact hNP x y (hN.1 x y hMxy)
  have hPc : P ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hMP, hP⟩⟩
  by_contra hnot
  have hproper : ¬ (∀ x y, P.Adj x y → N.Adj x y) := by
    intro hPN
    exact hnot (hPN u v hPuv)
  have hsub : N.edgeFinset ⊆ P.edgeFinset := by
    exact SimpleGraph.edgeFinset_mono hNP
  have hne : N.edgeFinset ≠ P.edgeFinset := by
    intro heq
    apply hproper
    intro x y hPxy
    have hmem : s(x, y) ∈ P.edgeFinset := by
      simpa using hPxy
    rw [← heq] at hmem
    simpa using hmem
  have hcard : N.edgeFinset.card < P.edgeFinset.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hle : P.edgeFinset.card ≤ N.edgeFinset.card := hmax P hPc
  omega
