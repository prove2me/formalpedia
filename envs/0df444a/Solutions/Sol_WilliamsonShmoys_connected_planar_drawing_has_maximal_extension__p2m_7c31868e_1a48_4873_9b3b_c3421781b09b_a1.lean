-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_has_maximal_extension__p2m_7c31868e_1a48_4873_9b3b_c3421781b09b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:04.156617+00:00
-- url     : https://prove2.me/submissions/26a5d745-05fc-4551-8efe-c504e992396b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let drawable : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H => G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)
  have hG : G ∈ drawable := by
    simp [drawable, hDraw]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image drawable
      (fun H => (Finset.univ.filter (fun p : V × V => H.Adj p.1 p.2)).card)
      ⟨G, hG⟩
  have hK : G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
    simpa [drawable] using hKmem
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hLDraw
  have hGL : G ≤ L := le_trans hK.1 hKL
  have hLmem : L ∈ drawable := by
    simp [drawable, hGL, hLDraw]
  let edges (H : SimpleGraph V) : Finset (V × V) :=
    Finset.univ.filter (fun p => H.Adj p.1 p.2)
  have hsubset : edges K ⊆ edges L := by
    intro p hp
    have hpK : K.Adj p.1 p.2 := by
      simpa [edges] using hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKL hpK⟩
  have hcard : (edges L).card ≤ (edges K).card := by
    simpa [edges] using hKmax L hLmem
  have heq : edges K = edges L := Finset.eq_of_subset_of_card_le hsubset hcard
  apply SimpleGraph.ext
  funext v w
  apply propext
  have hmem : (v, w) ∈ edges K ↔ (v, w) ∈ edges L := by rw [heq]
  simpa [edges] using hmem.symm