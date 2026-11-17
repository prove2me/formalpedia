-- Prove2me | solution 1 for SubquadCutReach.Faster.Supplement.corollary_4_2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:25:35.454343+00:00
-- url     : https://prove2.me/submissions/eaef90ae-8128-4609-85f7-c2ff838609b3

import Definitions.Def_SubquadCutReach_Faster_Supplement_FTRL

set_option autoImplicit false
namespace SubquadCutReach.Faster.Supplement

theorem ftrl_identity_aux {n : ℕ} (η : ℝ) (ℓ : ℕ → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) (T : ℕ) :
    2 * η * (∑ t ∈ Finset.range T, inner ℝ (ℓ t) (ftrlIter η ℓ t - u)) + ‖ftrlIter η ℓ T - u‖ ^ 2 =
      ‖u‖ ^ 2 + η ^ 2 * ∑ t ∈ Finset.range T, ‖ℓ t‖ ^ 2 := by
  induction T with
  | zero => simp [ftrlIter]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h : ftrlIter η ℓ (T + 1) - u = (ftrlIter η ℓ T - u) - η • ℓ T := by
      simp only [ftrlIter]; abel
    rw [h, norm_sub_sq_real, norm_smul, inner_smul_right, real_inner_comm, Real.norm_eq_abs,
      mul_pow, sq_abs]
    linarith

theorem corollary_4_2 (n : ℕ) (D L : ℝ) (hD : 0 < D) (hL : 0 < L) (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin n)) (hℓ : ∀ t < T, ‖ℓ t‖ ≤ L) :
    ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ D →
      ftrlRegret (D / (L * Real.sqrt (2 * (T : ℝ)))) ℓ T u ≤ D * L * Real.sqrt (2 * (T : ℝ)) := by
  intro u hu
  set s := Real.sqrt (2 * (T : ℝ)) with hs
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hss : s ^ 2 = 2 * T := Real.sq_sqrt (by linarith)
  set η := D / (L * s) with hη
  have hη0 : 0 < η := by positivity
  have hreg : ftrlRegret η ℓ T u = ∑ t ∈ Finset.range T, inner ℝ (ℓ t) (ftrlIter η ℓ t - u) := by
    simp only [ftrlRegret, inner_sub_right, Finset.sum_sub_distrib]
  have hid := ftrl_identity_aux η ℓ u T
  have hsum : ∑ t ∈ Finset.range T, ‖ℓ t‖ ^ 2 ≤ T * L ^ 2 := by
    calc ∑ t ∈ Finset.range T, ‖ℓ t‖ ^ 2 ≤ ∑ t ∈ Finset.range T, L ^ 2 :=
          Finset.sum_le_sum (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hℓ t (Finset.mem_range.1 ht)) 2)
      _ = T * L ^ 2 := by simp
  have hu2 : ‖u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  rw [hreg]
  set R := ∑ t ∈ Finset.range T, inner ℝ (ℓ t) (ftrlIter η ℓ t - u)
  have hnn : 0 ≤ ‖ftrlIter η ℓ T - u‖ ^ 2 := by positivity
  have h2 : 2 * η * R ≤ D ^ 2 + η ^ 2 * (T * L ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg η)]
  -- η * L * s = D
  have hηLs : η * (L * s) = D := by rw [hη]; field_simp
  -- multiply target by 2η > 0
  have key : 2 * η * R ≤ 2 * η * (D * L * s) := by
    have : D ^ 2 + η ^ 2 * (T * L ^ 2) ≤ 2 * η * (D * L * s) := by
      -- D^2 = η L s D, η^2 T L^2 = η L D T / s ... use s^2 = 2T
      have e1 : D ^ 2 = η * (L * s) * D := by rw [hηLs]; ring
      have e2 : η ^ 2 * (T * L ^ 2) * 2 = η * (L * s) * η * L * s := by
        have : (T : ℝ) * 2 = s ^ 2 := by rw [hss]; ring
        calc η ^ 2 * (T * L ^ 2) * 2 = η ^ 2 * L ^ 2 * ((T : ℝ) * 2) := by ring
          _ = η ^ 2 * L ^ 2 * s ^ 2 := by rw [this]
          _ = η * (L * s) * η * L * s := by ring
      rw [hηLs] at e2
      nlinarith [hη0, hL, hs0, hD]
    linarith
  exact le_of_mul_le_mul_left key (by positivity)

end SubquadCutReach.Faster.Supplement

theorem solution (n : ℕ) (D L : ℝ) (hD : 0 < D) (hL : 0 < L) (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin n)) (hℓ : ∀ t < T, ‖ℓ t‖ ≤ L) :
    ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ D →
      SubquadCutReach.Faster.Supplement.ftrlRegret (D / (L * Real.sqrt (2 * (T : ℝ)))) ℓ T u ≤ D * L * Real.sqrt (2 * (T : ℝ)) :=
  SubquadCutReach.Faster.Supplement.corollary_4_2 n D L hD hL T hT ℓ hℓ
