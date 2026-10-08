-- Prove2me | solution 1 for TaoAnDCA.Restart.restart_case_b2_neg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:52:47.39679+00:00
-- url     : https://prove2.me/submissions/79ef3223-ccc6-4c2b-b5ce-83659b01a66d

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
    (hb : inner ℝ b xs < 0) :
    let τ₁ : ℝ := (Real.sqrt (inner ℝ b u ^ 2 + inner ℝ b xs * inner ℝ u (A u + lamStar • u))
      - inner ℝ b u) / inner ℝ b xs
    τ₁ < 0 ∧
      -(inner ℝ b xs) * τ₁ ^ 2 - 2 * inner ℝ b u * τ₁ + inner ℝ u (A u + lamStar • u) = 0 ∧
      (∀ τ : ℝ, -(inner ℝ b xs) * τ ^ 2 - 2 * inner ℝ b u * τ + inner ℝ u (A u + lamStar • u) = 0 →
        τ₁ ≤ τ) ∧
      ∀ τ : ℝ, τ₁ < τ → τ < 0 →
        inner ℝ (u + τ • xs) xs ≠ 0 ∧
          inner ℝ (u + τ • xs) (A (u + τ • xs) + lamStar • (u + τ • xs)) < 0 := by
  dsimp only
  let B := inner ℝ b u
  let D := inner ℝ b xs
  let C := inner ℝ u (A u + lamStar • u)
  let S := Real.sqrt (B ^ 2 + D * C)
  let T := (S - B) / D
  have hD : D < 0 := hb
  have hC : C < 0 := hu
  have hDC : 0 < D * C := mul_pos_of_neg_of_neg hD hC
  have hrad : 0 ≤ B ^ 2 + D * C := by nlinarith [sq_nonneg B]
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = B ^ 2 + D * C := Real.sq_sqrt hrad
  have hSB : B < S := by nlinarith [sq_nonneg B]
  have hBm : -S < B := by nlinarith [sq_nonneg B]
  have hDn : D ≠ 0 := ne_of_lt hD
  have hT : T < 0 := div_neg_of_pos_of_neg (sub_pos.mpr hSB) hD
  have hDT : D * T = S - B := by dsimp [T]; field_simp
  have hroot : -D * T ^ 2 - 2 * B * T + C = 0 := by
    have he : D * (-D * T ^ 2 - 2 * B * T + C) = 0 := by
      nlinarith [sq_nonneg (D * T + B), hS2]
    exact (mul_eq_zero.mp he).resolve_left hDn
  refine ⟨hT, hroot, ?_, ?_⟩
  · intro τ he
    change -D * τ ^ 2 - 2 * B * τ + C = 0 at he
    change T ≤ τ
    by_contra hn
    have hlt : τ < T := lt_of_not_ge hn
    have hz : S < D * τ + B := by nlinarith
    have hp : 0 < (D * τ + B - S) * (D * τ + B + S) := by
      apply mul_pos <;> linarith
    nlinarith
  · intro τ hlo ht
    change T < τ at hlo
    have hn : inner ℝ (u + τ • xs) xs ≠ 0 := by
      simp only [inner_add_left, real_inner_smul_left, hux, zero_add,
        real_inner_self_eq_norm_sq, hnorm]
      exact ne_of_lt (mul_neg_of_neg_of_pos ht (sq_pos_of_pos hr))
    refine ⟨hn, ?_⟩
    rw [perturb A hA b xs u lamStar τ hkkt.2.1]
    change C - 2 * τ * B - τ ^ 2 * D < 0
    have hz1 : D * τ + B < S := by nlinarith
    have hz2 : -S < D * τ + B := by nlinarith
    have hp : 0 < (S - (D * τ + B)) * (S + (D * τ + B)) :=
      mul_pos (by linarith) (by linarith)
    have hm : 0 < D * (C - 2 * τ * B - τ ^ 2 * D) := by nlinarith
    exact neg_of_mul_pos_right hm (le_of_lt hD)

#print axioms solution
