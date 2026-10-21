-- Prove2me | solution 1 for ShorNonsmooth.Fejer.cfm_inner_direction_ge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:23:44.030654+00:00
-- url     : https://prove2.me/submissions/b188a5a1-c505-42bf-a14f-3cb66097ebb0

import Mathlib
import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

open ShorNonsmooth.Fejer

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xstar : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ y, f xstar ≤ f y)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (γ β : ℕ → ℝ) (hγ : ∀ k, 0 < γ k ∧ γ k ≤ 1) (hβ : ∀ k, 0 ≤ β k)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (hs0 : s 0 = g (x 0))
    (hx : ∀ k, x (k + 1) = x k - cfmStepsize f (f xstar) (γ k) (x k) (s k) • s k)
    (hs : ∀ k, s (k + 1) = g (x (k + 1)) + β (k + 1) • s k) :
    ∀ k, inner ℝ (x k - xstar) (s k) ≥ inner ℝ (x k - xstar) (g (x k)) := by
  intro k
  induction k with
  | zero =>
      rw [hs0]
  | succ k ih =>
      -- Step 0: the subgradient bound and `f xstar ≤ f (x k)`.
      have hsub : ∀ j, inner ℝ (x j - xstar) (g (x j)) ≥ f (x j) - f xstar := by
        intro j
        have h : f xstar - f (x j) ≥ inner ℝ (g (x j)) (xstar - x j) := hg (x j) xstar
        have hy : inner ℝ (g (x j)) (xstar - x j)
            = inner ℝ (g (x j)) xstar - inner ℝ (g (x j)) (x j) := by
          rw [inner_sub_right]
        rw [hy] at h
        have hx' : inner ℝ (x j - xstar) (g (x j))
            = inner ℝ (g (x j)) (x j) - inner ℝ (g (x j)) xstar := by
          rw [real_inner_comm, inner_sub_right]
        rw [hx']
        linarith
      have hfk : ∀ j, 0 ≤ f (x j) - f xstar := by
        intro j
        have h := hmin (x j)
        linarith
      -- Step 1: the step-size bound `h k * ‖s k‖^2 ≤ γ k * (f (x k) - f xstar)`.
      have hstep : ∀ j, cfmStepsize f (f xstar) (γ j) (x j) (s j) * ‖s j‖ ^ 2
          ≤ γ j * (f (x j) - f xstar) := by
        intro j
        by_cases hsj : s j = 0
        · -- `s j = 0`: the stepsize is `0`, so the left-hand side is `0`.
          have hcs : cfmStepsize f (f xstar) (γ j) (x j) (s j) = 0 := if_pos hsj
          have hn : ‖s j‖ ^ 2 = 0 := by simp [hsj]
          rw [hcs, hn]
          simp only [zero_mul]
          have : 0 ≤ (f (x j) - f xstar) * γ j :=
            mul_nonneg (hfk j) (hγ j).1.le
          simpa [mul_comm] using this
        · -- `s j ≠ 0`: the stepsize is `(f (x j) - f xstar) * γ j / ‖s j‖^2`.
          have hcs : cfmStepsize f (f xstar) (γ j) (x j) (s j)
              = (f (x j) - f xstar) * γ j / ‖s j‖ ^ 2 := by
            rw [cfmStepsize, if_neg hsj]
          have hnorm : 0 < ‖s j‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hsj)
          have hcancel : (f (x j) - f xstar) * γ j / ‖s j‖ ^ 2 * ‖s j‖ ^ 2
              = (f (x j) - f xstar) * γ j := by
            field_simp
          rw [hcs, hcancel]
          have : 0 ≤ (f (x j) - f xstar) * γ j :=
            mul_nonneg (hfk j) (hγ j).1.le
          simpa [mul_comm] using this
      -- Step 2: the induction step.
      have hxstep : x (k + 1) = x k - cfmStepsize f (f xstar) (γ k) (x k) (s k) • s k := hx k
      have hsstep : s (k + 1) = g (x (k + 1)) + β (k + 1) • s k := hs k
      -- The inner product `inner ℝ (x (k+1) - xstar) (s k)` is nonnegative.
      have hkey : 0 ≤ inner ℝ (x (k + 1) - xstar) (s k) := by
        have hM : inner ℝ (x k - xstar) (s k) ≥ inner ℝ (x k - xstar) (g (x k)) := ih
        have hexp : inner ℝ (x (k + 1) - xstar) (s k)
            = inner ℝ (x k - xstar) (s k)
              - cfmStepsize f (f xstar) (γ k) (x k) (s k) * ‖s k‖ ^ 2 := by
          rw [hxstep]
          simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
          ring
        rw [hexp]
        have hAD : f (x k) - f xstar ≤ inner ℝ (x k - xstar) (s k) :=
          le_trans (hsub k) hM
        have hcQ : cfmStepsize f (f xstar) (γ k) (x k) (s k) * ‖s k‖ ^ 2
            ≤ γ k * (f (x k) - f xstar) := hstep k
        have hgamma : 0 ≤ (1 - γ k) * (f (x k) - f xstar) :=
          mul_nonneg (sub_nonneg.mpr (hγ k).2) (hfk k)
        nlinarith
      -- Assemble: `M (k+1) = N (k+1) + β (k+1) * (nonneg)`.
      have hmain : inner ℝ (x (k + 1) - xstar) (s (k + 1))
          ≥ inner ℝ (x (k + 1) - xstar) (g (x (k + 1))) := by
        rw [hsstep]
        rw [inner_add_right, real_inner_smul_right]
        linarith [mul_nonneg (hβ (k + 1)) hkey]
      exact hmain
