-- Prove2me | solution 1 for RevShareCoord.Effort.Linear.optimal_wholesale_price
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:08:05.208994+00:00
-- url     : https://prove2.me/submissions/9534d1f6-10f1-4ef9-8170-d94ca034be5e

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

set_option autoImplicit false

namespace RevShareCoord.Effort.Linear

/-- the quadratic branch of the supplier profit, written in the order quantity `q`. -/
noncomputable def p88323dbf_gq (τ c φ w : ℝ) : ℝ :=
  (1 - c) * ((φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)))
    - (1 + φ * (1 - 2 * τ ^ 2)) * ((φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2))) ^ 2

lemma p88323dbf_f_eq (τ c φ w : ℝ) (hD : (2 * (φ - φ ^ 2 * τ ^ 2)) ≠ 0) (hw : w ≤ φ) :
    supplierProfitAt τ c φ w = p88323dbf_gq τ c φ w := by
  unfold p88323dbf_gq supplierProfitAt supplierProfit orderQty revenue price effort
  rcases lt_or_eq_of_le hw with h | h
  · rw [if_pos h]
    set q := (φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)) with hq
    have hw' : w = φ - 2 * (φ - φ ^ 2 * τ ^ 2) * q := by
      rw [hq]
      generalize 2 * (φ - φ ^ 2 * τ ^ 2) = D at hD ⊢
      field_simp
      ring
    clear_value q
    subst hw'
    ring
  · subst h
    simp

lemma p88323dbf_f_ge (τ c φ w : ℝ) (hw : φ ≤ w) : supplierProfitAt τ c φ w = 0 := by
  unfold supplierProfitAt supplierProfit orderQty revenue price effort
  rw [if_neg (not_lt.mpr hw)]
  ring

lemma p88323dbf_quad_hasDeriv (a K φ D w : ℝ) :
    HasDerivAt (fun x : ℝ => a * ((φ - x) / D) - K * ((φ - x) / D) ^ 2)
      (-a / D + 2 * K * (φ - w) / D ^ 2) w := by
  have hq : HasDerivAt (fun x : ℝ => (φ - x) / D) (-1 / D) w := by
    simpa using ((hasDerivAt_id w).const_sub φ).div_const D
  have h2 := (hq.const_mul a).sub ((hq.mul hq).const_mul K)
  have h3 : HasDerivAt (fun x : ℝ => a * ((φ - x) / D) - K * ((φ - x) / D * ((φ - x) / D)))
      (a * (-1 / D) - K * (-1 / D * ((φ - w) / D) + (φ - w) / D * (-1 / D))) w := h2
  have hfun : (fun x : ℝ => a * ((φ - x) / D) - K * ((φ - x) / D) ^ 2) =
      (fun x : ℝ => a * ((φ - x) / D) - K * ((φ - x) / D * ((φ - x) / D))) := by
    funext x; ring
  rw [hfun]
  refine h3.congr_deriv ?_
  ring

lemma p88323dbf_lin_hasDeriv (a K φ D w : ℝ) :
    HasDerivAt (fun x : ℝ => -a / D + 2 * K * (φ - x) / D ^ 2) (-(2 * K) / D ^ 2) w := by
  have h := ((((hasDerivAt_id w).const_sub φ).const_mul (2 * K)).div_const (D ^ 2)).const_add
    (-a / D)
  have h3 : HasDerivAt (fun x : ℝ => -a / D + 2 * K * (φ - x) / D ^ 2) (2 * K * (-1) / D ^ 2) w := h
  refine h3.congr_deriv ?_
  ring

end RevShareCoord.Effort.Linear

open RevShareCoord.Effort.Linear in
theorem solution (τ c φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    StrictConcaveOn ℝ (Set.Iic φ) (supplierProfitAt τ c φ) ∧
    (∀ w : ℝ, w < φ → iteratedDeriv 2 (supplierProfitAt τ c φ) w =
      -(1 + φ * (1 - 2 * τ ^ 2)) / (2 * φ ^ 2 * (1 - φ * τ ^ 2) ^ 2)) ∧
    0 ≤ wholesalePrice τ c φ ∧ wholesalePrice τ c φ < φ ∧
    IsMaxOn (supplierProfitAt τ c φ) (Set.Ici 0) (wholesalePrice τ c φ) ∧
    (∀ w : ℝ, 0 ≤ w → IsMaxOn (supplierProfitAt τ c φ) (Set.Ici 0) w →
      w = wholesalePrice τ c φ) := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hA : 0 < 1 - φ * τ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hφ1 (sq_nonneg τ)]
  have hDraw : 0 < 2 * (φ - φ ^ 2 * τ ^ 2) := by nlinarith
  have hDne : 2 * (φ - φ ^ 2 * τ ^ 2) ≠ 0 := hDraw.ne'
  have hKraw : 0 < 1 + φ * (1 - 2 * τ ^ 2) := by nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 2 * (φ - φ ^ 2 * τ ^ 2) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + φ * (1 - 2 * τ ^ 2) := ⟨_, rfl⟩
  have hDpos : 0 < D := by rw [hDdef]; exact hDraw
  have hD : D ≠ 0 := hDpos.ne'
  have hK : 0 < K := by rw [hKdef]; exact hKraw
  have hKne : K ≠ 0 := hK.ne'
  have hc : 0 < 1 - c := by linarith
  -- value of the quadratic branch in terms of q
  have hg : ∀ w, p88323dbf_gq τ c φ w = (1 - c) * ((φ - w) / D) - K * ((φ - w) / D) ^ 2 := by
    intro w; subst hDdef hKdef; rfl
  -- the wholesale price in terms of the optimal quantity
  have hW : wholesalePrice τ c φ = φ - D * ((1 - c) / (2 * K)) := by
    unfold wholesalePrice
    rw [← hKdef]
    field_simp
    subst hDdef hKdef
    ring
  have hqstar : (φ - wholesalePrice τ c φ) / D = (1 - c) / (2 * K) := by
    rw [hW]; field_simp; ring
  have hWlt : wholesalePrice τ c φ < φ := by
    rw [hW]
    have : 0 < D * ((1 - c) / (2 * K)) := by
      apply mul_pos hDpos; apply div_pos hc; linarith
    linarith
  have hW0 : 0 ≤ wholesalePrice τ c φ := by
    unfold wholesalePrice
    apply div_nonneg
    · apply mul_nonneg hφ0.le
      have h1 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - τ ^ 2) hφ0.le
      nlinarith [mul_pos hc0 hA]
    · exact hKraw.le
  have hfW : supplierProfitAt τ c φ (wholesalePrice τ c φ) = (1 - c) ^ 2 / (4 * K) := by
    rw [p88323dbf_f_eq τ c φ _ hDne hWlt.le, hg, hqstar]
    field_simp
    ring
  have hbound : ∀ w, supplierProfitAt τ c φ w ≤ (1 - c) ^ 2 / (4 * K) := by
    intro w
    rcases le_or_gt w φ with h | h
    · rw [p88323dbf_f_eq τ c φ _ hDne h, hg]
      generalize (φ - w) / D = q
      rw [le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg (2 * K * q - (1 - c))]
    · rw [p88323dbf_f_ge τ c φ w h.le]
      exact div_nonneg (sq_nonneg _) (by linarith)
  refine ⟨?_, ?_, hW0, hWlt, ?_, ?_⟩
  · -- strict concavity
    refine ⟨convex_Iic φ, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hz : a • x + b • y ∈ Set.Iic φ := convex_Iic φ hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hz ⊢
    rw [p88323dbf_f_eq τ c φ _ hDne hx, p88323dbf_f_eq τ c φ _ hDne hy, p88323dbf_f_eq τ c φ _ hDne hz, hg, hg, hg]
    have hu : (φ - (a * x + b * y)) / D = a * ((φ - x) / D) + b * ((φ - y) / D) := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      field_simp
      ring
    have huv : (φ - x) / D ≠ (φ - y) / D := by
      intro h
      apply hxy
      have := (div_left_inj' hD).mp h
      linarith
    rw [hu]
    generalize (φ - x) / D = u at huv ⊢
    generalize (φ - y) / D = v at huv ⊢
    have hne : 0 < (u - v) ^ 2 := by
      have : u - v ≠ 0 := sub_ne_zero.mpr huv
      positivity
    have hb' : b = 1 - a := by linarith
    subst hb'
    have : 0 < K * a * (1 - a) * (u - v) ^ 2 := by
      apply mul_pos (mul_pos (mul_pos hK ha) hb) hne
    nlinarith
  · -- second derivative
    intro w hw
    have heq : supplierProfitAt τ c φ =ᶠ[nhds w] p88323dbf_gq τ c φ := by
      filter_upwards [Iio_mem_nhds hw] with x hx using p88323dbf_f_eq τ c φ x hDne (le_of_lt hx)
    rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv.deriv_eq]
    have hd : deriv (p88323dbf_gq τ c φ) = fun x => -(1 - c) / D + 2 * K * (φ - x) / D ^ 2 := by
      funext x
      subst hDdef hKdef
      exact (p88323dbf_quad_hasDeriv (1 - c) _ φ _ x).deriv
    rw [hd, (p88323dbf_lin_hasDeriv (1 - c) K φ D w).deriv, ← hKdef]
    have hden : 0 < 2 * φ ^ 2 * (1 - φ * τ ^ 2) ^ 2 :=
      mul_pos (mul_pos two_pos (pow_pos hφ0 2)) (pow_pos hA 2)
    rw [div_eq_div_iff (pow_ne_zero 2 hD) hden.ne', hDdef]
    ring
  · -- maximality
    intro w _
    rw [hfW]
    exact hbound w
  · -- uniqueness
    intro w hw0 hmax
    have hle : supplierProfitAt τ c φ (wholesalePrice τ c φ) ≤ supplierProfitAt τ c φ w :=
      hmax (show wholesalePrice τ c φ ∈ Set.Ici 0 from hW0)
    rw [hfW] at hle
    have hpos : 0 < (1 - c) ^ 2 / (4 * K) := div_pos (pow_pos hc 2) (by linarith)
    rcases le_or_gt φ w with h | h
    · rw [p88323dbf_f_ge τ c φ w h] at hle
      linarith
    · rw [p88323dbf_f_eq τ c φ _ hDne h.le, hg] at hle
      have hq : (φ - w) / D = (1 - c) / (2 * K) := by
        generalize (φ - w) / D = q at hle ⊢
        rw [div_le_iff₀ (by linarith)] at hle
        have hsq : (2 * K * q - (1 - c)) ^ 2 ≤ 0 := by nlinarith
        have h0 : 2 * K * q - (1 - c) = 0 :=
          (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hsq (sq_nonneg _))
        rw [eq_div_iff (by linarith)]
        linarith
      rw [← hqstar] at hq
      have := (div_left_inj' hD).mp hq
      linarith
