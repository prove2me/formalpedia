-- Prove2me | solution 1 for ReferencePricing.PriceMonotone.value_convex_of_demand_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:26:32.030202+00:00
-- url     : https://prove2.me/submissions/98c9d323-eff7-451a-a5ba-65f4fdef7311

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

namespace RefPrice3VC

theorem refPath_mem (pbar α r₀ : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hr : r₀ ∈ Set.Icc (0 : ℝ) pbar)
    (q : ℕ → Set.Icc (0 : ℝ) pbar) (t : ℕ) :
    refPath α r₀ (fun s => (q s : ℝ)) t ∈ Set.Icc (0 : ℝ) pbar := by
  induction t with
  | zero => exact hr
  | succ t ih =>
    show α * refPath α r₀ (fun s => (q s : ℝ)) t + (1 - α) * (q t : ℝ) ∈ _
    have h1 := (q t).2
    constructor
    · have := mul_nonneg hα₀ ih.1
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) h1.1
      linarith
    · nlinarith [ih.2, h1.2, ih.1, h1.1]

theorem refPath_comb (α x y a b : ℝ) (hab : a + b = 1) (f : ℕ → ℝ) (t : ℕ) :
    refPath α (a * x + b * y) f t = a * refPath α x f t + b * refPath α y f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show α * refPath α (a * x + b * y) f t + (1 - α) * f t =
      a * (α * refPath α x f t + (1 - α) * f t) + b * (α * refPath α y f t + (1 - α) * f t)
    rw [ih]
    have : b = 1 - a := by linarith
    subst this
    ring

end RefPrice3VC

open RefPrice3VC

theorem solution
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hconv : ∀ p ∈ Set.Icc (0 : ℝ) pbar,
      ConvexOn ℝ (Set.Icc (0 : ℝ) pbar) (fun r => demand d R p r)) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) pbar) (value (profit d R) α β pbar) := by
  set P := Set.Icc (0 : ℝ) pbar with hP
  set Pf := profit d R with hPi
  obtain ⟨M, hM⟩ := hA1.bounded
  set C := pbar * M with hC
  have hPib : ∀ p ∈ P, ∀ r ∈ P, |Pf p r| ≤ C := by
    intro p hp r hr
    have h0 := hA1.nonneg p hp r hr
    have h1 := hM p hp r hr
    have : Pf p r = p * demand d R p r := rfl
    rw [this, abs_of_nonneg (mul_nonneg hp.1 h0)]
    exact mul_le_mul hp.2 h1 h0 hpbar.le
  -- profit is convex in r
  have hPconv : ∀ p ∈ P, ConvexOn ℝ P (fun r => Pf p r) := by
    intro p hp
    have : (fun r => Pf p r) = fun r => p • demand d R p r := by funext r; rfl
    rw [this]
    exact (hconv p hp).smul hp.1
  set F : (ℕ → P) → ℝ → ℝ := fun q x =>
    ∑' t : ℕ, β ^ t * Pf (q t) (refPath α x (fun s => (q s : ℝ)) t) with hF
  have hgeo := summable_geometric_of_lt_one hβ₀.le hβ₁
  have hsum : ∀ q : ℕ → P, ∀ x ∈ P,
      Summable (fun t : ℕ => β ^ t * Pf (q t) (refPath α x (fun s => (q s : ℝ)) t)) := by
    intro q x hx
    refine Summable.of_norm_bounded (g := fun t : ℕ => C * β ^ t) (hgeo.mul_left C) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ₀ t), mul_comm]
    exact mul_le_mul_of_nonneg_right
      (hPib _ (q t).2 _ (refPath_mem pbar α x hα₀ hα₁ hx q t)) (pow_pos hβ₀ t).le
  have hFb : ∀ q : ℕ → P, ∀ x ∈ P, F q x ≤ C * (1 - β)⁻¹ := by
    intro q x hx
    rw [← tsum_geometric_of_lt_one hβ₀.le hβ₁, ← tsum_mul_left]
    refine (hsum q x hx).tsum_le_tsum (fun t => ?_) (hgeo.mul_left C)
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left
      (le_trans (le_abs_self _) (hPib _ (q t).2 _ (refPath_mem pbar α x hα₀ hα₁ hx q t)))
      (pow_pos hβ₀ t).le
  have : Nonempty (ℕ → P) := ⟨fun _ => ⟨0, le_rfl, hpbar.le⟩⟩
  have hV : ∀ x, value Pf α β pbar x = ⨆ q : ℕ → P, F q x := fun x => rfl
  have hbdd : ∀ x ∈ P, BddAbove (Set.range fun q : ℕ → P => F q x) := by
    intro x hx
    exact ⟨C * (1 - β)⁻¹, by rintro _ ⟨q, rfl⟩; exact hFb q x hx⟩
  -- each discounted sum is convex in the initial reference price
  have hFconv : ∀ q : ℕ → P, ∀ x ∈ P, ∀ y ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      F q (a * x + b * y) ≤ a * F q x + b * F q y := by
    intro q x hx y hy a b ha hb hab
    have hxy : a * x + b * y ∈ P := by
      have := convex_Icc (0 : ℝ) pbar hx hy ha hb hab
      simpa [smul_eq_mul, hP] using this
    simp only [hF]
    rw [← tsum_mul_left, ← tsum_mul_left,
      ← ((hsum q x hx).mul_left a).tsum_add ((hsum q y hy).mul_left b)]
    refine (hsum q _ hxy).tsum_le_tsum (fun t => ?_)
      (((hsum q x hx).mul_left a).add ((hsum q y hy).mul_left b))
    rw [refPath_comb α x y a b hab]
    have hxt := refPath_mem pbar α x hα₀ hα₁ hx q t
    have hyt := refPath_mem pbar α y hα₀ hα₁ hy q t
    have := (hPconv (q t) (q t).2).2 hxt hyt ha hb hab
    simp only [smul_eq_mul] at this
    have hβt := (pow_pos hβ₀ t).le
    have := mul_le_mul_of_nonneg_left this hβt
    linarith
  refine ⟨convex_Icc 0 pbar, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [hV, hV, hV]
  refine ciSup_le (fun q => ?_)
  have h1 := hFconv q x hx y hy a b ha hb hab
  have h2 : F q x ≤ ⨆ q : ℕ → P, F q x := le_ciSup (hbdd x hx) q
  have h3 : F q y ≤ ⨆ q : ℕ → P, F q y := le_ciSup (hbdd y hy) q
  have := mul_le_mul_of_nonneg_left h2 ha
  have := mul_le_mul_of_nonneg_left h3 hb
  linarith
