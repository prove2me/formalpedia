-- Prove2me | solution 1 for TaoAnDCA.Restart.restart_case_b2_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:52:45.037322+00:00
-- url     : https://prove2.me/submissions/dafc874e-ca5f-4d3d-a325-67e663f0e624

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

open TaoAnDCA.Restart

private theorem perturb {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b xs u : EuclideanSpace ℝ (Fin n)) (lam τ : ℝ)
    (hk : A xs + lam • xs = -b) :
    inner ℝ (u + τ • xs) (A (u + τ • xs) + lam • (u + τ • xs)) =
    inner ℝ u (A u + lam • u) - 2 * τ * inner ℝ b u - τ ^ 2 * inner ℝ b xs := by
  have hc : inner ℝ xs (A u) = inner ℝ u (A xs) := by
    calc
      _ = inner ℝ (A u) xs := real_inner_comm _ _
      _ = inner ℝ u (A xs) := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) u xs
  have h1 := congrArg (fun z => inner ℝ u z) hk
  have h2 := congrArg (fun z => inner ℝ xs z) hk
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right] at h1 h2
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hc, real_inner_comm xs u, real_inner_comm xs b, real_inner_comm u b] at *
  nlinarith [congrArg (fun z : ℝ => 2 * τ * z) h1,
    congrArg (fun z : ℝ => τ ^ 2 * z) h2]

theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar) (hnorm : ‖xs‖ = r)
    (u : EuclideanSpace ℝ (Fin n)) (hu : inner ℝ u (A u + lamStar • u) < 0) (hux : inner ℝ u xs = 0)
    (hb : inner ℝ b xs = 0) :
    (inner ℝ b u ≤ 0 → ∀ τ : ℝ, τ < 0 →
        inner ℝ (u + τ • xs) xs ≠ 0 ∧
          inner ℝ (u + τ • xs) (A (u + τ • xs) + lamStar • (u + τ • xs)) < 0) ∧
      (0 < inner ℝ b u → ∀ τ : ℝ, inner ℝ u (A u + lamStar • u) / (2 * inner ℝ b u) < τ → τ < 0 →
        inner ℝ (u + τ • xs) xs ≠ 0 ∧
          inner ℝ (u + τ • xs) (A (u + τ • xs) + lamStar • (u + τ • xs)) < 0) := by
  have hp (τ : ℝ) := perturb A hA b xs u lamStar τ hkkt.2.1
  have hn (τ : ℝ) (ht : τ < 0) : inner ℝ (u + τ • xs) xs ≠ 0 := by
    simp only [inner_add_left, real_inner_smul_left, hux, zero_add,
      real_inner_self_eq_norm_sq, hnorm]
    exact ne_of_lt (mul_neg_of_neg_of_pos ht (sq_pos_of_pos hr))
  constructor
  · intro hbu τ ht
    refine ⟨hn τ ht, ?_⟩
    rw [hp, hb, mul_zero, sub_zero]
    have hm : 0 ≤ τ * inner ℝ b u := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ht) hbu
    linarith
  · intro hbu τ hlo ht
    refine ⟨hn τ ht, ?_⟩
    rw [hp, hb, mul_zero, sub_zero]
    have := (div_lt_iff₀ (show 0 < 2 * inner ℝ b u by positivity)).mp hlo
    nlinarith

#print axioms solution
