-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:48:07.218998+00:00
-- url     : https://prove2.me/submissions/62bbf244-e093-4b6e-9674-476d973336a0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  classical
  let edgePairs : SimpleGraph V → Finset (V × V) := fun G =>
    Finset.univ.filter fun p => G.Adj p.1 p.2
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hne : candidates.Nonempty := by
    refine ⟨H, ?_⟩
    simp [candidates, hH]
  obtain ⟨K, hKmem, hKmax⟩ :=
    candidates.exists_max_image (fun G => (edgePairs G).card) hne
  have hKH : H ≤ K := (Finset.mem_filter.mp hKmem).2.1
  have hKplanar : HasPlanarDrawingOn K := (Finset.mem_filter.mp hKmem).2.2
  refine ⟨K, hKH, hKplanar, ?_⟩
  intro L hKL hLplanar
  by_contra hnot
  have hsubset : edgePairs K ⊂ edgePairs L := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro p hp
      have hpAdj : K.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKL hpAdj⟩
    · intro heq
      apply hnot
      intro u v huv
      have hpL : (u, v) ∈ edgePairs L := by
        simp [edgePairs, huv]
      have hpK : (u, v) ∈ edgePairs K := by
        rw [heq]
        exact hpL
      exact (Finset.mem_filter.mp hpK).2
  have hHL : H ≤ L := hKH.trans hKL
  have hLmem : L ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHL, hLplanar⟩
  have hmax := hKmax L hLmem
  have hcard := Finset.card_lt_card hsubset
  omega