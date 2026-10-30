-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_max_card_exists__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:08.115917+00:00
-- url     : https://prove2.me/submissions/28cfdbaf-4f1b-4bf9-9c51-32d5829ca3cc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        Nat.card {p : V × V // L.Adj p.1 p.2} ≤
          Nat.card {p : V × V // K.Adj p.1 p.2} := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => J ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hadmissible : admissible.Nonempty := by
    refine ⟨J, ?_⟩
    simp only [admissible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hJ⟩
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image admissible
      (fun G => Nat.card {p : V × V // G.Adj p.1 p.2}) hadmissible
  have hKprop : J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
    simpa [admissible] using (Finset.mem_filter.mp hKmem).2
  refine ⟨K, hKprop.1, hKprop.2, ?_⟩
  intro L hKL hL
  apply hKmax L
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_univ _
  · exact ⟨le_trans hKprop.1 hKL, hL⟩