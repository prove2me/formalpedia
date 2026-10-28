-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:00:51.966501+00:00
-- url     : https://prove2.me/submissions/0e7e5da9-7d21-4c89-a973-01fe2cacde47

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hstep : ∀ G : SimpleGraph V, H ≤ G →
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
          G.edgeSet.ncard < K.edgeSet.ncard) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
  have hS : S.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, le_rfl, hdraw⟩
  let E : Finset ℕ := S.image fun G => G.edgeSet.ncard
  have hE : E.Nonempty := by
    obtain ⟨G, hG⟩ := hS
    exact ⟨G.edgeSet.ncard, Finset.mem_image.mpr ⟨G, hG, rfl⟩⟩
  obtain ⟨K, hKS, hKcard⟩ : ∃ K, K ∈ S ∧ K.edgeSet.ncard = E.max' hE := by
    have hm : E.max' hE ∈ E := Finset.max'_mem E hE
    rcases Finset.mem_image.mp hm with ⟨K, hKS, hval⟩
    exact ⟨K, hKS, hval⟩
  have hKmax : ∀ G, G ∈ S → G.edgeSet.ncard ≤ K.edgeSet.ncard := by
    intro G hG
    have hmem : G.edgeSet.ncard ∈ E :=
      Finset.mem_image.mpr ⟨G, hG, rfl⟩
    have hle : G.edgeSet.ncard ≤ E.max' hE := by
      exact Finset.le_max' E _ hmem
    calc
      G.edgeSet.ncard ≤ E.max' hE := hle
      _ = K.edgeSet.ncard := hKcard.symm
  have hKmem : H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
    simpa [S] using hKS
  refine ⟨K, hKmem.1, ?_, hKmem.2⟩
  by_contra hconn
  have hnotconn : ¬ K.Connected := by
    simpa using hconn
  obtain ⟨K', hKK', hK'draw, hlt⟩ := hstep K hKmem.1 hKmem.2 hnotconn
  have hK'S : K' ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨le_trans hKmem.1 hKK', hK'draw⟩
  have hle := hKmax K' hK'S
  exact (Nat.not_lt_of_ge hle) hlt