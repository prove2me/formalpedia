-- Prove2me | solution 1 for ReferencePricing.PriceMonotone.lemma3b_convex_demand
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:25:09.107249+00:00
-- url     : https://prove2.me/submissions/bda1be5a-3a0a-4fb7-8bbf-072298c8e434

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
import Theorems.Thm_ReferencePricing_PriceMonotone_value_convex_of_demand_convex
open RobustBooking.Shared

namespace RefPrice3L3b

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

theorem refPath_sub (α x y : ℝ) (f : ℕ → ℝ) (t : ℕ) :
    refPath α x f t - refPath α y f t = α ^ t * (x - y) := by
  induction t with
  | zero => simp [refPath]
  | succ t ih =>
    show α * refPath α x f t + (1 - α) * f t - (α * refPath α y f t + (1 - α) * f t) = _
    rw [pow_succ]
    linear_combination α * ih

/-- Convex `g`: for `a ≤ b ≤ c`, `a ≤ e ≤ c`, `b + e = a + c`, `g b + g e ≤ g a + g c`. -/
theorem convex_sum_le (s : Set ℝ) (g : ℝ → ℝ) (hg : ConvexOn ℝ s g) (a b c e : ℝ)
    (ha : a ∈ s) (hc : c ∈ s) (hab : a ≤ b) (hbc : b ≤ c) (hae : a ≤ e) (hec : e ≤ c)
    (hsum : b + e = a + c) : g b + g e ≤ g a + g c := by
  rcases eq_or_lt_of_le (le_trans hab hbc) with h | h
  · have hb : b = a := le_antisymm (h ▸ hbc) hab
    have he : e = a := le_antisymm (h ▸ hec) hae
    rw [hb, he, h]
  · have hca : 0 < c - a := by linarith
    have hne : c - a ≠ 0 := hca.ne'
    have hb : g (((c - b) / (c - a)) • a + ((b - a) / (c - a)) • c) ≤
        ((c - b) / (c - a)) • g a + ((b - a) / (c - a)) • g c :=
      hg.2 ha hc (div_nonneg (by linarith) hca.le) (div_nonneg (by linarith) hca.le)
        (by field_simp; ring)
    have he : g (((c - e) / (c - a)) • a + ((e - a) / (c - a)) • c) ≤
        ((c - e) / (c - a)) • g a + ((e - a) / (c - a)) • g c :=
      hg.2 ha hc (div_nonneg (by linarith) hca.le) (div_nonneg (by linarith) hca.le)
        (by field_simp; ring)
    have eb : ((c - b) / (c - a)) • a + ((b - a) / (c - a)) • c = b := by
      simp only [smul_eq_mul]; field_simp; ring
    have ee : ((c - e) / (c - a)) • a + ((e - a) / (c - a)) • c = e := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [eb] at hb
    rw [ee] at he
    simp only [smul_eq_mul] at hb he
    have h1 : (c - b) / (c - a) + (c - e) / (c - a) = 1 := by
      field_simp; linarith
    have h2 : (b - a) / (c - a) + (e - a) / (c - a) = 1 := by
      field_simp; linarith
    have : g b + g e ≤ ((c - b) / (c - a) + (c - e) / (c - a)) * g a +
        ((b - a) / (c - a) + (e - a) / (c - a)) * g c := by linarith
    rw [h1, h2] at this
    linarith

end RefPrice3L3b

open RefPrice3L3b

theorem solution
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hconv : ∀ p ∈ Set.Icc (0 : ℝ) pbar,
      ConvexOn ℝ (Set.Icc (0 : ℝ) pbar) (fun r => demand d R p r)) :
    MonotoneOn (optPrice (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by
  have hVconv := ReferencePricing.PriceMonotone.value_convex_of_demand_convex pbar α β d R
    hpbar hα₀ hα₁ hβ₀ hβ₁ hA1 hA2 hA3 hd hconv
  set P := Set.Icc (0 : ℝ) pbar with hP
  set Pf := profit d R with hPi
  obtain ⟨M, hM⟩ := hA1.bounded
  have hM0 : 0 ≤ M := le_trans (hA1.nonneg 0 ⟨le_rfl, hpbar.le⟩ 0 ⟨le_rfl, hpbar.le⟩)
    (hM 0 ⟨le_rfl, hpbar.le⟩ 0 ⟨le_rfl, hpbar.le⟩)
  set C := pbar * M with hC
  have hPib : ∀ p ∈ P, ∀ r ∈ P, |Pf p r| ≤ C := by
    intro p hp r hr
    have h0 := hA1.nonneg p hp r hr
    have h1 := hM p hp r hr
    have : Pf p r = p * demand d R p r := rfl
    rw [this, abs_of_nonneg (mul_nonneg hp.1 h0)]
    exact mul_le_mul hp.2 h1 h0 hpbar.le
  have hPic : ContinuousOn (Function.uncurry Pf) (P ×ˢ P) := by
    have : Function.uncurry Pf = fun z : ℝ × ℝ => z.1 * Function.uncurry (demand d R) z := by
      funext z; rfl
    rw [this]
    exact continuousOn_fst.mul hA1.continuous
  have hcompact : IsCompact (P ×ˢ P) := isCompact_Icc.prod isCompact_Icc
  have hPiu := hcompact.uniformContinuousOn_of_continuous hPic
  rw [Metric.uniformContinuousOn_iff] at hPiu
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
  -- uniform closeness of the discounted sums
  have hFdiff : ∀ q : ℕ → P, ∀ x ∈ P, ∀ y ∈ P, ∀ η : ℝ,
      (∀ t, Pf (q t) (refPath α x (fun s => (q s : ℝ)) t) -
        Pf (q t) (refPath α y (fun s => (q s : ℝ)) t) ≤ η) →
      F q x - F q y ≤ η * (1 - β)⁻¹ := by
    intro q x hx y hy η hη
    simp only [hF]
    rw [← (hsum q x hx).tsum_sub (hsum q y hy), ← tsum_geometric_of_lt_one hβ₀.le hβ₁,
      ← tsum_mul_left]
    refine ((hsum q x hx).sub (hsum q y hy)).tsum_le_tsum (fun t => ?_) (hgeo.mul_left η)
    rw [← mul_sub, mul_comm η]
    exact mul_le_mul_of_nonneg_left (hη t) (pow_pos hβ₀ t).le
  have : Nonempty (ℕ → P) := ⟨fun _ => ⟨0, le_rfl, hpbar.le⟩⟩
  have hV : ∀ x, value Pf α β pbar x = ⨆ q : ℕ → P, F q x := fun x => rfl
  have hbdd : ∀ x ∈ P, BddAbove (Set.range fun q : ℕ → P => F q x) := by
    intro x hx
    exact ⟨C * (1 - β)⁻¹, by rintro _ ⟨q, rfl⟩; exact hFb q x hx⟩
  have hVle : ∀ x ∈ P, ∀ y ∈ P, ∀ η : ℝ,
      (∀ q : ℕ → P, ∀ t, Pf (q t) (refPath α x (fun s => (q s : ℝ)) t) -
        Pf (q t) (refPath α y (fun s => (q s : ℝ)) t) ≤ η) →
      value Pf α β pbar x ≤ value Pf α β pbar y + η * (1 - β)⁻¹ := by
    intro x hx y hy η hη
    rw [hV, hV]
    refine ciSup_le (fun q => ?_)
    have h1 := hFdiff q x hx y hy η (hη q)
    have h2 : F q y ≤ ⨆ q : ℕ → P, F q y := le_ciSup (hbdd y hy) q
    linarith
  have hVc : ContinuousOn (value Pf α β pbar) P := by
    rw [Metric.continuousOn_iff]
    intro y hy ε hε
    have h1β : 0 < 1 - β := by linarith
    obtain ⟨δ, hδ, hδu⟩ := hPiu (ε * (1 - β) / 2) (by positivity)
    refine ⟨δ, hδ, fun x hx hxy => ?_⟩
    have hclose : ∀ q : ℕ → P, ∀ t, |Pf (q t) (refPath α x (fun s => (q s : ℝ)) t) -
        Pf (q t) (refPath α y (fun s => (q s : ℝ)) t)| < ε * (1 - β) / 2 := by
      intro q t
      have hxt := refPath_mem pbar α x hα₀ hα₁ hx q t
      have hyt := refPath_mem pbar α y hα₀ hα₁ hy q t
      have hdist : dist (refPath α x (fun s => (q s : ℝ)) t)
          (refPath α y (fun s => (q s : ℝ)) t) < δ := by
        rw [Real.dist_eq, refPath_sub, abs_mul]
        rw [Real.dist_eq] at hxy
        have : |α ^ t| ≤ 1 := by
          rw [abs_of_nonneg (pow_nonneg hα₀ t)]; exact pow_le_one₀ hα₀ hα₁.le
        nlinarith [abs_nonneg (x - y)]
      have := hδu ((q t : ℝ), _) ⟨(q t).2, hxt⟩ ((q t : ℝ), _) ⟨(q t).2, hyt⟩ (by
        rw [Prod.dist_eq]; simpa [dist_self] using hdist)
      simpa [Real.dist_eq] using this
    have a1 := hVle x hx y hy (ε * (1 - β) / 2)
      (fun q t => (abs_lt.mp (hclose q t)).2.le)
    have a2 := hVle y hy x hx (ε * (1 - β) / 2) (fun q t => by
      have := (abs_lt.mp (hclose q t)).1; linarith)
    have e : ε * (1 - β) / 2 * (1 - β)⁻¹ = ε / 2 := by field_simp
    rw [e] at a1 a2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- W(·, r) is continuous on P
  have hW : ∀ p r, bellmanObj Pf α β pbar p r =
      Pf p r + β * value Pf α β pbar (α * r + (1 - α) * p) := fun p r => rfl
  have hmemP : ∀ p ∈ P, ∀ r ∈ P, α * r + (1 - α) * p ∈ P := by
    intro p hp r hr
    constructor
    · have := mul_nonneg hα₀ hr.1
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) hp.1
      linarith
    · nlinarith [hp.1, hp.2, hr.1, hr.2]
  have hWc : ∀ r ∈ P, ContinuousOn (fun p => bellmanObj Pf α β pbar p r) P := by
    intro r hr
    simp only [hW]
    refine ContinuousOn.add ?_ (continuousOn_const.mul ?_)
    · have : (fun p => Pf p r) = Function.uncurry Pf ∘ (fun p => (p, r)) := rfl
      rw [this]
      exact hPic.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun p hp => ⟨hp, hr⟩)
    · exact hVc.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
        (fun p hp => hmemP p hp r hr)
  set S : ℝ → Set ℝ := fun r => {p | p ∈ P ∧
    ∀ p' ∈ P, bellmanObj Pf α β pbar p' r ≤ bellmanObj Pf α β pbar p r} with hS
  have hSne : ∀ r ∈ P, (S r).Nonempty := by
    intro r hr
    obtain ⟨p, hp, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hpbar.le) (hWc r hr)
    exact ⟨p, hp, fun p' hp' => hmax hp'⟩
  have hSbdd : ∀ r, BddAbove (S r) := fun r => ⟨pbar, fun x hx => hx.1.2⟩
  have hopt : ∀ r, optPrice Pf α β pbar r = sSup (S r) := fun r => rfl
  -- supermodularity of W
  have hsup : ∀ p₁ ∈ P, ∀ p₂ ∈ P, ∀ r₁ ∈ P, ∀ r₂ ∈ P, p₁ ≤ p₂ → r₁ ≤ r₂ →
      bellmanObj Pf α β pbar p₂ r₁ + bellmanObj Pf α β pbar p₁ r₂ ≤
        bellmanObj Pf α β pbar p₂ r₂ + bellmanObj Pf α β pbar p₁ r₁ := by
    intro p₁ hp₁ p₂ hp₂ r₁ hr₁ r₂ hr₂ hp hr
    have hR := hA3.ref_supermodular p₁ hp₁ p₂ hp₂ r₁ hr₁ r₂ hr₂ hp hr
    have hVs := convex_sum_le P (value Pf α β pbar) hVconv
      (α * r₁ + (1 - α) * p₁) (α * r₁ + (1 - α) * p₂) (α * r₂ + (1 - α) * p₂)
      (α * r₂ + (1 - α) * p₁) (hmemP p₁ hp₁ r₁ hr₁) (hmemP p₂ hp₂ r₂ hr₂)
      (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) (by ring)
    rw [hW, hW, hW, hW]
    simp only [refProfit] at hR
    simp only [hPi, profit, demand]
    nlinarith
  -- Topkis
  intro r₁ hr₁ r₂ hr₂ hr
  rw [hopt, hopt]
  refine csSup_le (hSne r₁ hr₁) (fun p₁ hp₁ => ?_)
  obtain ⟨p₂, hp₂⟩ := hSne r₂ hr₂
  rcases le_total p₁ p₂ with h | h
  · exact le_trans h (le_csSup (hSbdd r₂) hp₂)
  · have hmem : p₁ ∈ S r₂ := by
      refine ⟨hp₁.1, fun p' hp' => ?_⟩
      have e1 := hsup p₂ hp₂.1 p₁ hp₁.1 r₁ hr₁ r₂ hr₂ h hr
      have e2 := hp₁.2 p₂ hp₂.1
      have e3 := hp₂.2 p' hp'
      linarith
    exact le_csSup (hSbdd r₂) hmem
