-- Prove2me | solution 1 for ReferencePricing.PriceMonotone.lemma3a_short_memory
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:22:30.232656+00:00
-- url     : https://prove2.me/submissions/de225f06-bda2-4b8e-a594-b5327717a7b2

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

namespace RefPrice3L3a

theorem refPath_zero_succ (r₀ : ℝ) (f : ℕ → ℝ) (t : ℕ) :
    refPath 0 r₀ f (t + 1) = f t := by
  simp [refPath]

theorem refPath_mem (pbar r₀ : ℝ) (hr : r₀ ∈ Set.Icc (0 : ℝ) pbar)
    (q : ℕ → Set.Icc (0 : ℝ) pbar) (t : ℕ) :
    refPath 0 r₀ (fun s => (q s : ℝ)) t ∈ Set.Icc (0 : ℝ) pbar := by
  cases t with
  | zero => exact hr
  | succ t => rw [refPath_zero_succ]; exact (q t).2

end RefPrice3L3a

open RefPrice3L3a

theorem solution
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hα : α = 0) :
    MonotoneOn (optPrice (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by
  subst hα
  set P := Set.Icc (0 : ℝ) pbar with hP
  set Pf := profit d R with hPi
  obtain ⟨M, hM⟩ := hA1.bounded
  have hM0 : 0 ≤ M := le_trans (hA1.nonneg 0 ⟨le_rfl, hpbar.le⟩ 0 ⟨le_rfl, hpbar.le⟩)
    (hM 0 ⟨le_rfl, hpbar.le⟩ 0 ⟨le_rfl, hpbar.le⟩)
  set C := pbar * M with hC
  -- bounds on profit
  have hPib : ∀ p ∈ P, ∀ r ∈ P, |Pf p r| ≤ C := by
    intro p hp r hr
    have h0 := hA1.nonneg p hp r hr
    have h1 := hM p hp r hr
    have : Pf p r = p * demand d R p r := rfl
    rw [this, abs_of_nonneg (mul_nonneg hp.1 h0)]
    exact mul_le_mul hp.2 h1 h0 hpbar.le
  -- continuity of profit on P × P
  have hPic : ContinuousOn (Function.uncurry Pf) (P ×ˢ P) := by
    have : Function.uncurry Pf = fun z : ℝ × ℝ => z.1 * Function.uncurry (demand d R) z := by
      funext z; rfl
    rw [this]
    exact continuousOn_fst.mul hA1.continuous
  have hcompact : IsCompact (P ×ˢ P) := isCompact_Icc.prod isCompact_Icc
  have hPiu := hcompact.uniformContinuousOn_of_continuous hPic
  rw [Metric.uniformContinuousOn_iff] at hPiu
  -- the discounted sums
  set F : (ℕ → P) → ℝ → ℝ := fun q x =>
    ∑' t : ℕ, β ^ t * Pf (q t) (refPath 0 x (fun s => (q s : ℝ)) t) with hF
  have hsum : ∀ q : ℕ → P, ∀ x ∈ P,
      Summable (fun t : ℕ => β ^ t * Pf (q t) (refPath 0 x (fun s => (q s : ℝ)) t)) := by
    intro q x hx
    refine Summable.of_norm_bounded (g := fun t : ℕ => C * β ^ t)
      ((summable_geometric_of_lt_one hβ₀.le hβ₁).mul_left C) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ₀ t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hPib _ (q t).2 _ (refPath_mem pbar x hx q t))
      (pow_pos hβ₀ t).le
  have hFb : ∀ q : ℕ → P, ∀ x ∈ P, F q x ≤ C * (1 - β)⁻¹ := by
    intro q x hx
    rw [← tsum_geometric_of_lt_one hβ₀.le hβ₁, ← tsum_mul_left]
    refine (hsum q x hx).tsum_le_tsum (fun t => ?_)
      ((summable_geometric_of_lt_one hβ₀.le hβ₁).mul_left C)
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left
      (le_trans (le_abs_self _) (hPib _ (q t).2 _ (refPath_mem pbar x hx q t)))
      (pow_pos hβ₀ t).le
  have hFdiff : ∀ q : ℕ → P, ∀ x ∈ P, ∀ y ∈ P,
      F q x - F q y = Pf (q 0) x - Pf (q 0) y := by
    intro q x hx y hy
    simp only [hF]
    rw [← (hsum q x hx).tsum_sub (hsum q y hy)]
    rw [tsum_eq_single 0]
    · simp [refPath]
    · intro t ht
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
      rw [refPath_zero_succ, refPath_zero_succ]; ring
  haveI : Nonempty (ℕ → P) := ⟨fun _ => ⟨0, le_rfl, hpbar.le⟩⟩
  have hV : ∀ x, value Pf 0 β pbar x = ⨆ q : ℕ → P, F q x := fun x => rfl
  have hbdd : ∀ x ∈ P, BddAbove (Set.range fun q : ℕ → P => F q x) := by
    intro x hx
    exact ⟨C * (1 - β)⁻¹, by rintro _ ⟨q, rfl⟩; exact hFb q x hx⟩
  -- V is continuous on P
  have hVle : ∀ x ∈ P, ∀ y ∈ P, ∀ ε : ℝ,
      (∀ p ∈ P, Pf p x - Pf p y ≤ ε) → value Pf 0 β pbar x ≤ value Pf 0 β pbar y + ε := by
    intro x hx y hy ε hε
    rw [hV, hV]
    refine ciSup_le (fun q => ?_)
    have h1 := hFdiff q x hx y hy
    have h2 : F q y ≤ ⨆ q : ℕ → P, F q y := le_ciSup (hbdd y hy) q
    have h3 := hε (q 0) (q 0).2
    linarith
  have hVc : ContinuousOn (value Pf 0 β pbar) P := by
    rw [Metric.continuousOn_iff]
    intro y hy ε hε
    obtain ⟨δ, hδ, hδu⟩ := hPiu (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun x hx hxy => ?_⟩
    have hclose : ∀ p ∈ P, |Pf p x - Pf p y| < ε / 2 := by
      intro p hp
      have := hδu (p, x) ⟨hp, hx⟩ (p, y) ⟨hp, hy⟩ (by
        rw [Prod.dist_eq]; simpa [dist_self] using hxy)
      simpa [Real.dist_eq] using this
    have a1 := hVle x hx y hy (ε / 2) (fun p hp => (abs_lt.mp (hclose p hp)).2.le)
    have a2 := hVle y hy x hx (ε / 2) (fun p hp => by
      have := (abs_lt.mp (hclose p hp)).1; linarith)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- W(·, r) is continuous on P and attains its maximum
  have hW : ∀ p r, bellmanObj Pf 0 β pbar p r = Pf p r + β * value Pf 0 β pbar p := by
    intro p r; simp [bellmanObj]
  have hWc : ∀ r ∈ P, ContinuousOn (fun p => bellmanObj Pf 0 β pbar p r) P := by
    intro r hr
    simp only [hW]
    refine ContinuousOn.add ?_ (continuousOn_const.mul hVc)
    have : (fun p => Pf p r) = Function.uncurry Pf ∘ (fun p => (p, r)) := rfl
    rw [this]
    exact hPic.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun p hp => ⟨hp, hr⟩)
  set S : ℝ → Set ℝ := fun r => {p | p ∈ P ∧
    ∀ p' ∈ P, bellmanObj Pf 0 β pbar p' r ≤ bellmanObj Pf 0 β pbar p r} with hS
  have hSne : ∀ r ∈ P, (S r).Nonempty := by
    intro r hr
    obtain ⟨p, hp, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hpbar.le) (hWc r hr)
    exact ⟨p, hp, fun p' hp' => hmax hp'⟩
  have hSbdd : ∀ r, BddAbove (S r) := fun r => ⟨pbar, fun x hx => hx.1.2⟩
  have hopt : ∀ r, optPrice Pf 0 β pbar r = sSup (S r) := fun r => rfl
  -- supermodularity of W
  have hsup : ∀ p₁ ∈ P, ∀ p₂ ∈ P, ∀ r₁ ∈ P, ∀ r₂ ∈ P, p₁ ≤ p₂ → r₁ ≤ r₂ →
      bellmanObj Pf 0 β pbar p₂ r₁ + bellmanObj Pf 0 β pbar p₁ r₂ ≤
        bellmanObj Pf 0 β pbar p₂ r₂ + bellmanObj Pf 0 β pbar p₁ r₁ := by
    intro p₁ hp₁ p₂ hp₂ r₁ hr₁ r₂ hr₂ hp hr
    have := hA3.ref_supermodular p₁ hp₁ p₂ hp₂ r₁ hr₁ r₂ hr₂ hp hr
    rw [hW, hW, hW, hW]
    simp only [refProfit] at this
    simp only [hPi, profit, demand]
    linarith
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
