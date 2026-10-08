-- Prove2me | solution 1 for TaoAnDCA.TRS.eq20_iff_kkt
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:11:39.727346+00:00
-- url     : https://prove2.me/submissions/dcbd99fc-0e58-43b3-98c1-47f459b25cc8

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology TaoAnDCA.TRS TaoAnDCA.GlobalOpt

private lemma small_coeff (a c : ℝ)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → t * a ≤ t ^ 2 * c) : a ≤ 0 := by
  by_contra hn
  have ha : 0 < a := lt_of_not_ge hn
  let t := min (1 / 2) (a / (2 * (|c| + 1)))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hta : t * (2 * (|c| + 1)) ≤ a := by
    exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hh := h t ht ht1
  have hd : a ≤ t * c := by nlinarith
  have hc := le_abs_self c
  have := mul_le_mul_of_nonneg_left hc ht.le
  nlinarith [abs_nonneg c]

private lemma hquad {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (ρ : ℝ) (x d : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (1 / 2 * inner ℝ (x + t • d) (ρ • (x + t • d) - A (x + t • d))) =
      1 / 2 * inner ℝ x (ρ • x - A x) +
      t * inner ℝ (ρ • x - A x) d + t ^ 2 / 2 * inner ℝ d (ρ • d - A d) := by
  have hs := hA.isSymmetric x d
  simp only [ContinuousLinearMap.coe_coe] at hs
  simp only [map_add, map_smul, smul_add, inner_add_left, inner_add_right,
    inner_sub_right, inner_sub_left, real_inner_smul_left, real_inner_smul_right]
  have hs' : inner ℝ d (A x) = inner ℝ x (A d) := (real_inner_comm d (A x)).symm.trans hs
  simp only [hs', hs, real_inner_comm d x]
  ring

private lemma hdiff {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (ρ : ℝ) (hρA : ∀ z, 0 ≤ inner ℝ z (ρ • z - A z)) (x : EuclideanSpace ℝ (Fin n)) :
    subdiff (hDec A ρ) x = {ρ • x - A x} := by
  ext v
  change InertialFB.IFB.IsSubgradient (hDec A ρ) x v ↔ v = ρ • x - A x
  constructor
  · intro hv
    let d := v - (ρ • x - A x)
    have hh (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
        t * ‖d‖ ^ 2 ≤ t ^ 2 * (inner ℝ d (ρ • d - A d) / 2) := by
      have h := hv.2 (x + t • d)
      simp only [hDec, ← EReal.coe_add, EReal.coe_le_coe_iff, add_sub_cancel_left,
        real_inner_smul_right] at h
      rw [hquad A hA] at h
      have he : inner ℝ v d - inner ℝ (ρ • x - A x) d = ‖d‖ ^ 2 := by
        rw [← inner_sub_left]
        exact real_inner_self_eq_norm_sq d
      nlinarith
    have hz := small_coeff _ _ hh
    have : d = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg d])
    exact sub_eq_zero.mp this
  · intro hv
    subst v
    refine ⟨EReal.coe_ne_top _, ?_⟩
    intro z
    have he : z = x + (1 : ℝ) • (z - x) := by simp
    have hh := hquad A hA ρ x (z - x) 1
    rw [← he] at hh
    have hp := hρA (z - x)
    simp only [hDec, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith

private lemma gquad {n : ℕ} (b x d : EuclideanSpace ℝ (Fin n)) (ρ t : ℝ) :
    ρ / 2 * ‖x + t • d‖ ^ 2 + inner ℝ b (x + t • d) =
      ρ / 2 * ‖x‖ ^ 2 + inner ℝ b x +
      t * inner ℝ (ρ • x + b) d + t ^ 2 * (ρ / 2 * ‖d‖ ^ 2) := by
  rw [norm_add_sq_real]
  simp only [inner_add_right, real_inner_smul_right, inner_add_left, real_inner_smul_left,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private lemma gdiff {n : ℕ} (b : EuclideanSpace ℝ (Fin n)) (ρ r : ℝ) (hρ : 0 ≤ ρ)
    (x v : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ r) :
    v ∈ subdiff (gDec b ρ r) x ↔
      ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ r → inner ℝ (v - (ρ • x + b)) (z - x) ≤ 0 := by
  constructor
  · intro hv z hz
    apply small_coeff (inner ℝ (v - (ρ • x + b)) (z - x)) (ρ / 2 * ‖z - x‖ ^ 2)
    intro t ht ht1
    have hm : ‖x + t • (z - x)‖ ≤ r := by
      have he : x + t • (z - x) = (1 - t) • x + t • z := by module
      rw [he]
      calc
        _ ≤ ‖(1 - t) • x‖ + ‖t • z‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖z‖ := by simp [norm_smul, abs_of_nonneg ht.le, abs_of_nonneg (sub_nonneg.mpr ht1)]
        _ ≤ (1 - t) * r + t * r := add_le_add
          (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hz ht.le)
        _ = r := by ring
    have h := hv.2 (x + t • (z - x))
    simp only [gDec, if_pos hx, if_pos hm, ← EReal.coe_add, EReal.coe_le_coe_iff,
      add_sub_cancel_left, real_inner_smul_right] at h
    rw [gquad] at h
    rw [inner_sub_left]
    nlinarith
  · intro hv
    refine ⟨by rw [gDec, if_pos hx]; exact EReal.coe_ne_top _, ?_⟩
    intro z
    by_cases hz : ‖z‖ ≤ r
    · have hh := gquad b x (z - x) ρ 1
      simp only [one_smul, add_sub_cancel] at hh
      have hp := hv z hz
      rw [inner_sub_left] at hp
      simp only [gDec, if_pos hx, if_pos hz, ← EReal.coe_add, EReal.coe_le_coe_iff]
      nlinarith [sq_nonneg ‖z - x‖]
    · simp [gDec, hx, hz]

private lemma ball_normal {n : ℕ} (r : ℝ) (hr : 0 < r)
    (x q : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ r) :
    (∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ r → inner ℝ q (z - x) ≤ 0) ↔
      ∃ a : ℝ, 0 ≤ a ∧ q = a • x ∧ a * (‖x‖ - r) = 0 := by
  constructor
  · intro h
    by_cases hq : q = 0
    · exact ⟨0, le_rfl, by simp [hq], by simp⟩
    have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
    let z := (r / ‖q‖) • q
    have hz : ‖z‖ = r := by simp [z, norm_smul, abs_of_pos hr, hn.ne']
    have hh := h z hz.le
    simp only [inner_sub_right, z, real_inner_smul_right, real_inner_self_eq_norm_sq] at hh
    have he : (r / ‖q‖) * ‖q‖ ^ 2 = r * ‖q‖ := by field_simp
    rw [he] at hh
    have hc := real_inner_le_norm q x
    have hxr : ‖x‖ = r := by nlinarith
    have hi : inner ℝ q x = ‖q‖ * ‖x‖ := by nlinarith
    have hscale := inner_eq_norm_mul_iff_real.mp hi
    refine ⟨‖q‖ / r, (div_pos hn hr).le, ?_, by rw [hxr]; simp⟩
    rw [hxr] at hscale
    calc
      q = (1 / r) • (r • q) := by rw [smul_smul]; simp [hr.ne']
      _ = (1 / r) • (‖q‖ • x) := by rw [hscale]
      _ = (‖q‖ / r) • x := by rw [smul_smul]; congr 1; ring
  · rintro ⟨a, ha, rfl, hcomp⟩ z hz
    rw [real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
    have hc := real_inner_le_norm x z
    have hh := mul_le_mul_of_nonneg_left hz (norm_nonneg x)
    have ht := mul_le_mul_of_nonneg_left (hc.trans hh) ha
    have he : a * ‖x‖ * (‖x‖ - r) = 0 := by nlinarith [congrArg (fun t : ℝ => t * ‖x‖) hcomp]
    nlinarith

theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρA : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ z (ρ • z - A z)) (xs : EuclideanSpace ℝ (Fin n)) (hxs : ‖xs‖ ≤ r) :
    subdiff (hDec A ρ) xs = {ρ • xs - A xs} ∧
      (subdiff (hDec A ρ) xs ⊆ subdiff (gDec b ρ r) xs ↔ ∃ lam : ℝ, IsKKT A b r xs lam) := by
  have hh := hdiff A hA ρ hρA xs
  refine ⟨hh, ?_⟩
  rw [hh, Set.singleton_subset_iff, gdiff b ρ r hρ.le xs _ hxs, ball_normal r hr _ _ hxs]
  constructor
  · rintro ⟨a, ha, he, hc⟩
    refine ⟨a, ha, ?_, hc, hxs⟩
    rw [← he]
    module
  · rintro ⟨a, ha, he, hc, hx⟩
    refine ⟨a, ha, ?_, hc⟩
    apply sub_eq_zero.mp
    calc
      _ = -(A xs + a • xs + b) := by module
      _ = 0 := by rw [he]; simp

#print axioms solution
