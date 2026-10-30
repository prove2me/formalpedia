-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:33.037801+00:00
-- url     : https://prove2.me/submissions/5fafa75d-6973-48bd-8353-e24b7ca77fd8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H' : SimpleGraph V, H ≤ H' ∧ WilliamsonShmoys.HasPlanarDrawingOn H' ∧
      (∀ K : SimpleGraph V, H' ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H') := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  let measure : SimpleGraph V → ℕ := fun G =>
    (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2).card
  have hcandidates : candidates.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ?_⟩
    simp [candidates, hDraw]
  obtain ⟨H', hH'mem, hmax⟩ := Finset.exists_max_image candidates measure hcandidates
  have hH' : H ≤ H' ∧ WilliamsonShmoys.HasPlanarDrawingOn H' := by
    simpa [candidates] using (Finset.mem_filter.mp hH'mem).2
  refine ⟨H', hH'.1, hH'.2, ?_⟩
  intro K hH'K hKdraw
  have hKmem : K ∈ candidates := by
    simp [candidates, hH'.1.trans hH'K, hKdraw]
  have hsubset :
      (Finset.univ.filter fun p : V × V => H'.Adj p.1 p.2) ⊆
        (Finset.univ.filter fun p : V × V => K.Adj p.1 p.2) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH'K (Finset.mem_filter.mp hp).2⟩
  have hmaxK : measure K ≤ measure H' := hmax K hKmem
  have hedge_eq :
      (Finset.univ.filter fun p : V × V => H'.Adj p.1 p.2) =
        (Finset.univ.filter fun p : V × V => K.Adj p.1 p.2) := by
    exact Finset.eq_of_subset_of_card_le hsubset (by simpa [measure] using hmaxK)
  intro a b hab
  have hpK : (a, b) ∈ Finset.univ.filter (fun p : V × V => K.Adj p.1 p.2) := by
    simp [hab]
  have hpH' : (a, b) ∈ Finset.univ.filter (fun p : V × V => H'.Adj p.1 p.2) := by
    rw [hedge_eq]
    exact hpK
  exact (Finset.mem_filter.mp hpH').2