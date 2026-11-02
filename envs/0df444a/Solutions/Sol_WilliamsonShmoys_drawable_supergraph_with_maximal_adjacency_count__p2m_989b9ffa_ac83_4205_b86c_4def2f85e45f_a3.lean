-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_with_maximal_adjacency_count__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:39:09.936223+00:00
-- url     : https://prove2.me/submissions/7f55ddf7-1f5c-449f-b369-bf23a6bd37e3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧
        ∀ K : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K →
            Nat.card {p : V × V // H.Adj p.1 p.2} ≥
              Nat.card {p : V × V // K.Adj p.1 p.2} := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun X =>
      WilliamsonShmoys.HasPlanarDrawingOn X ∧ G ≤ X
  have hGmem : G ∈ candidates := by
    simp [candidates, hG]
  let scores : Finset ℕ :=
    candidates.image fun X => Nat.card {p : V × V // X.Adj p.1 p.2}
  have hscores : scores.Nonempty := by
    refine ⟨Nat.card {p : V × V // G.Adj p.1 p.2}, ?_⟩
    exact Finset.mem_image.mpr ⟨G, hGmem, rfl⟩
  let m : ℕ := scores.max' hscores
  have hm : m ∈ scores := by
    exact Finset.max'_mem scores hscores
  obtain ⟨H, hHmem, hHm⟩ := Finset.mem_image.mp hm
  have hHmem' := Finset.mem_filter.mp hHmem
  have hHcond : WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H := by
    simpa [candidates] using hHmem'.2
  refine ⟨H, hHcond.1, hHcond.2, ?_⟩
  intro K hK hHK
  have hGK : G ≤ K := le_trans hHcond.2 hHK
  have hKmem : K ∈ candidates := by
    simp [candidates, hK, hGK]
  have hKscore : Nat.card {p : V × V // K.Adj p.1 p.2} ∈ scores := by
    exact Finset.mem_image.mpr ⟨K, hKmem, rfl⟩
  have hle := Finset.le_max' scores
    (Nat.card {p : V × V // K.Adj p.1 p.2}) hKscore
  change Nat.card {p : V × V // K.Adj p.1 p.2} ≤ m at hle
  rw [← hHm] at hle
  exact hle