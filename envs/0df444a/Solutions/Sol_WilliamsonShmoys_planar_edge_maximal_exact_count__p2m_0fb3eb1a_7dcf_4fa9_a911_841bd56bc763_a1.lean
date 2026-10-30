-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_exact_count__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:42:32.747724+00:00
-- url     : https://prove2.me/submissions/7ee05eea-3ef5-4219-9655-ffbef9856051

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (M N : SimpleGraph V)
      (hCard : 3 ≤ Fintype.card V)
      (hMN : M ≤ N)
      (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
      (hMax : ∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
        N.edgeSet.ncard ≤ K.edgeSet.ncard),
      N.edgeSet.ncard + 6 = 3 * Fintype.card V) := by
  intro h
  let V := Fin 3
  let M : SimpleGraph V := ⊥
  let N : SimpleGraph V := ⊥
  have hCard : 3 ≤ Fintype.card V := by simp [V]
  have hMN : M ≤ N := le_rfl
  have hN : WilliamsonShmoys.HasPlanarDrawingOn N := by
    let p : V → ℝ × ℝ := fun i => ((i.val : ℝ), 0)
    let arc : V → V → ℝ → ℝ × ℝ := fun _ _ _ => (0, 0)
    refine ⟨p, arc, ?_, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      have hval : (i.val : ℝ) = (j.val : ℝ) := by
        simpa [p] using congrArg Prod.fst hij
      exact Nat.cast_injective hval
    · intro u v huv hadj
      simp [N] at hadj
    · intro u v x y huv hxy huvAdj hxyAdj hneq t ht s hs heq
      simp [N] at huvAdj
  have hMax : ∀ K : SimpleGraph V,
      M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      N.edgeSet.ncard ≤ K.edgeSet.ncard := by
    intro K hMK hK
    simp [N]
  have hBad := h (M := M) (N := N) hCard hMN hN hMax
  have hNCard : N.edgeSet.ncard = 0 := by simp [N]
  rw [hNCard] at hBad
  norm_num [V] at hBad