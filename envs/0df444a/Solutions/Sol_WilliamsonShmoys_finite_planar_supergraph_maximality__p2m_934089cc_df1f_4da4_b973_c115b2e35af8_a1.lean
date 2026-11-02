-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:33.807222+00:00
-- url     : https://prove2.me/submissions/ac65b466-0506-4a55-b8f0-8baf720ccd9d

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop), P H →
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, H ≤ L → P L → L = K) := by
  intro h
  let G1 : SimpleGraph (Fin 3) := SimpleGraph.edge 0 1
  let G2 : SimpleGraph (Fin 3) := SimpleGraph.edge 1 2
  let P : SimpleGraph (Fin 3) → Prop := fun G => G = ⊥ ∨ G = G1 ∨ G = G2
  have hbot : P (⊥ : SimpleGraph (Fin 3)) := by
    simp [P]
  have hx := h (V := Fin 3) (H := (⊥ : SimpleGraph (Fin 3))) (P := P) hbot
  rcases hx with ⟨K, hHK, hPK, hmax⟩
  have hG1 : P G1 := by
    simp [P, G1]
  have hG2 : P G2 := by
    simp [P, G2]
  have h1 : G1 = K := hmax G1 bot_le hG1
  have h2 : G2 = K := hmax G2 bot_le hG2
  have hne : G1 ≠ G2 := by
    intro heq
    have hadj : G1.Adj (0 : Fin 3) 1 := by
      simp [G1, SimpleGraph.edge_adj]
    rw [heq] at hadj
    simp [G2, SimpleGraph.edge_adj] at hadj
  exact hne (h1.trans h2.symm)