-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.gTilde_subsequence_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T23:12:52.455991+00:00
-- url     : https://prove2.me/submissions/2a1e548e-375c-4d99-b495-3b98224a09d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_never_stopped_subseq_bound

open ShorNonsmooth.SpaceDilation

/-- Theorem 3.1 (Shor 1985, p. 53) by case split on the stopping rule.

If `g(x_J) = 0` for some `J`, the SDG state freezes from `J` on, so
`gTilde` is identically `0` on the tail `J, J+1, ...`, which satisfies the
required bound for any `c > 0`. Otherwise the run never stops and the
determinant-trace-liminf core is discharged by the published child
`sdg_never_stopped_subseq_bound`. -/
theorem solution {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d αstar δ : ℝ) (hd : 0 < d) (hαstar : 0 < αstar) (hδ : 0 < δ)
    (hg : ∀ k : ℕ, ‖g (sdg g h α x₀ B₀ k).x‖ ≤ d)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k ∧ α k ≤ αstar) :
    ∃ c : ℝ, 0 < c ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p : ℕ, ‖gTilde g h α x₀ B₀ (kp p)‖ <
        c * (∏ j ∈ Finset.Icc 1 (kp p), α j) ^ (-(1 : ℝ) / n) := by
  have hPpos : ∀ k : ℕ, 0 < ∏ j ∈ Finset.Icc 1 k, α j := by
    intro k
    apply Finset.prod_pos
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h1 := (hα j hj1).1
    linarith
  by_cases hstopcase : ∃ j : ℕ, g (sdg g h α x₀ B₀ j).x = 0
  · obtain ⟨J, hJ⟩ := hstopcase
    have hunfold : ∀ k : ℕ, sdg g h α x₀ B₀ (k + 1) =
        sdgStep g h α k (sdg g h α x₀ B₀ k) := fun k => rfl
    have hfr : ∀ k : ℕ, J ≤ k → sdg g h α x₀ B₀ k = sdg g h α x₀ B₀ J := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        have hJk : g (sdg g h α x₀ B₀ k).x = 0 := by rw [ih]; exact hJ
        calc sdg g h α x₀ B₀ (k + 1)
            = sdgStep g h α k (sdg g h α x₀ B₀ k) := hunfold k
          _ = sdgStep g h α k (sdg g h α x₀ B₀ J) := by rw [ih]
          _ = sdg g h α x₀ B₀ J := by unfold sdgStep; rw [if_pos hJ]
    have hg0 : ∀ p : ℕ, gTilde g h α x₀ B₀ (J + p) = 0 := by
      intro p
      have hst : sdg g h α x₀ B₀ (J + p) = sdg g h α x₀ B₀ J :=
        hfr (J + p) (Nat.le_add_right J p)
      show ContinuousLinearMap.adjoint (sdg g h α x₀ B₀ (J + p)).B
        (g (sdg g h α x₀ B₀ (J + p)).x) = 0
      rw [hst, hJ]
      exact map_zero _
    refine ⟨1, one_pos, (fun p => J + p),
      (by intro p q hpq; show J + p < J + q; omega), ?_⟩
    intro p
    show ‖gTilde g h α x₀ B₀ (J + p)‖ <
      1 * (∏ j ∈ Finset.Icc 1 (J + p), α j) ^ (-(1 : ℝ) / n)
    rw [hg0 p, norm_zero, one_mul]
    exact Real.rpow_pos_of_pos (hPpos _) _
  · have hnever : ∀ j : ℕ, g (sdg g h α x₀ B₀ j).x ≠ 0 :=
      fun j hj => hstopcase ⟨j, hj⟩
    exact sdg_never_stopped_subseq_bound hn g h α x₀ B₀ d αstar δ hd hαstar hδ
      hg hα hnever
