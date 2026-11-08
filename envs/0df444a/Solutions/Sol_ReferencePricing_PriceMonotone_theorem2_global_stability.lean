-- Prove2me | solution 1 for ReferencePricing.PriceMonotone.theorem2_global_stability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:48:05.227451+00:00
-- url     : https://prove2.me/submissions/10862d76-5a96-471d-b6c7-7d9e2882e8db

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
import Theorems.Thm_ReferencePricing_PriceMonotone_lemma2_optRef_monotone
open RobustBooking.Shared
open Filter Topology

namespace RefPrice3T2

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

theorem refPath_shift (α x : ℝ) (f : ℕ → ℝ) (t : ℕ) :
    refPath α x f (t + 1) = refPath α (α * x + (1 - α) * f 0) (fun s => f (s + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show α * refPath α x f (t + 1) + (1 - α) * f (t + 1) = _
    rw [ih]; rfl

theorem refPath_const (α x c : ℝ) (t : ℕ) :
    refPath α x (fun _ => c) t - c = α ^ t * (x - c) := by
  induction t with
  | zero => simp [refPath]
  | succ t ih =>
    show α * refPath α x (fun _ => c) t + (1 - α) * c - c = _
    rw [pow_succ]
    linear_combination α * ih

end RefPrice3T2

open RefPrice3T2

theorem solution
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d) :
    ∃ p : ℝ, IsSteadyState (profit d R) α β pbar p ∧
      (∀ q : ℝ, IsSteadyState (profit d R) α β pbar q → q = p) ∧
      deriv (baseProfit d) p / (1 - β) = p * refSlope R p / (1 - α * β) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) pbar,
        deriv (baseProfit d) q / (1 - β) = q * refSlope R q / (1 - α * β) → q = p) ∧
      ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
        Tendsto (pricePath (profit d R) α β pbar r₀) atTop (𝓝 p) ∧
        (Monotone (statePath (profit d R) α β pbar r₀) ∨
          Antitone (statePath (profit d R) α β pbar r₀)) ∧
        Tendsto (statePath (profit d R) α β pbar r₀) atTop (𝓝 p) := by
  have hqmono := ReferencePricing.PriceMonotone.lemma2_optRef_monotone pbar α β d R hpbar hα₀ hα₁
    hβ₀ hβ₁ hA1 hA2 hA3 hd
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
  have h1α : 0 < 1 - α := by linarith
  have h1β : 0 < 1 - β := by linarith
  have h1αβ : 0 < 1 - α * β := by nlinarith
  -- closedness: the largest maximizer is a maximizer
  have hSmem : ∀ r ∈ P, sSup (S r) ∈ S r := by
    intro r hr
    obtain ⟨p₀, hp₀⟩ := hSne r hr
    have hEq : S r = P ∩ (fun p => bellmanObj Pf α β pbar p r) ⁻¹' Set.Ici
        (bellmanObj Pf α β pbar p₀ r) := by
      ext p
      constructor
      · intro hp; exact ⟨hp.1, hp.2 p₀ hp₀.1⟩
      · intro hp
        exact ⟨hp.1, fun p' hp' => le_trans (hp₀.2 p' hp') hp.2⟩
    have hcl : IsClosed (S r) := by
      rw [hEq]
      exact (hWc r hr).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    exact hcl.csSup_mem ⟨p₀, hp₀⟩ (hSbdd r)
  -- joint continuity of W
  have hWjc : ContinuousOn (fun z : ℝ × ℝ => bellmanObj Pf α β pbar z.1 z.2) (P ×ˢ P) := by
    simp only [hW]
    refine ContinuousOn.add ?_ (continuousOn_const.mul ?_)
    · exact hPic
    · refine hVc.comp ((continuous_const.mul continuous_snd).add
        (continuous_const.mul continuous_fst)).continuousOn (fun z hz => hmemP z.1 hz.1 z.2 hz.2)
  -- shift identity for discounted sums
  have hshift : ∀ q : ℕ → P, ∀ x ∈ P,
      F q x = Pf (q 0) x + β * F (fun t => q (t + 1)) (α * x + (1 - α) * (q 0 : ℝ)) := by
    intro q x hx
    simp only [hF]
    rw [(hsum q x hx).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, refPath_shift]
    rw [← tsum_mul_left]
    congr 1
    congr 1; funext t; rw [pow_succ]; ring
  have hFle : ∀ q : ℕ → P, ∀ x ∈ P, F q x ≤ value Pf α β pbar x := fun q x hx => by
    rw [hV]; exact le_ciSup (hbdd x hx) q
  -- Bellman upper bound at a weak steady state
  have hVbell : ∀ r ∈ P, r ∈ S r → value Pf α β pbar r * (1 - β) ≤ Pf r r := by
    intro r hr hrS
    have hb : value Pf α β pbar r ≤ Pf r r + β * value Pf α β pbar r := by
      rw [hV]
      refine ciSup_le (fun q => ?_)
      rw [hshift q r hr]
      have h1 := hFle (fun t => q (t + 1)) _ (hmemP (q 0) (q 0).2 r hr)
      have h2 := hrS.2 (q 0) (q 0).2
      rw [hW, hW] at h2
      have e : α * r + (1 - α) * r = r := by ring
      rw [e] at h2
      rw [← hV]
      nlinarith
    nlinarith
  -- splitting the short-term profit
  have hsplit : ∀ p r, Pf p r = baseProfit d p + p * R (r - p) r := by
    intro p r; simp only [hPi, profit, demand, baseProfit]; ring
  have hdiag : ∀ p, Pf p p = baseProfit d p := by
    intro p; rw [hsplit, sub_self, hA1.R_zero, mul_zero, add_zero]
  have hdiffπ : Differentiable ℝ (baseProfit d) := by
    have : baseProfit d = fun p => p * d p := rfl
    rw [this]; exact differentiable_id.mul hd
  have hK : ∀ r (hr : r ∈ P), F (fun _ => ⟨r, hr⟩) r * (1 - β) = Pf r r := by
    intro r hr
    have := hshift (fun _ => ⟨r, hr⟩) r hr
    rw [show α * r + (1 - α) * r = r by ring] at this
    simp only at this
    linarith
  have hVK : ∀ r ∈ P, r ∈ S r → value Pf α β pbar r * (1 - β) ≤ Pf r r := hVbell
  -- interior first-order condition
  have hFOC : ∀ r ∈ P, r ∈ S r → 0 < r → r < pbar →
      (1 - α * β) * deriv (baseProfit d) r - (1 - β) * (r * refSlope R r) = 0 := by
    intro r hr hrS h0 h1
    set m := min r (pbar - r) with hmdef
    have hm : 0 < m := lt_min h0 (by linarith)
    set H : ℝ → ℝ := fun ε =>
      Pf (r + ε) r + β * Pf (r - α * ε) (α * r + (1 - α) * (r + ε)) with hH
    have hdev : ∀ ε, |ε| < m → H ε ≤ H 0 := by
      intro ε hε
      have hε1 : |ε| < r := lt_of_lt_of_le hε (min_le_left _ _)
      have hε2 : |ε| < pbar - r := lt_of_lt_of_le hε (min_le_right _ _)
      have k1 := le_abs_self ε
      have k2 := neg_abs_le ε
      have hαε : |α * ε| ≤ |ε| := by
        rw [abs_mul, abs_of_nonneg hα₀]; nlinarith [abs_nonneg ε]
      have k3 := le_abs_self (α * ε)
      have k4 := neg_abs_le (α * ε)
      have m0 : r + ε ∈ P := ⟨by linarith, by linarith⟩
      have m1 : r - α * ε ∈ P := ⟨by linarith, by linarith⟩
      set q : ℕ → P := fun t => if t = 0 then ⟨r + ε, m0⟩ else
        if t = 1 then ⟨r - α * ε, m1⟩ else ⟨r, hr⟩ with hq
      have hq0 : ((q 0 : P) : ℝ) = r + ε := by simp [hq]
      have hq1 : ((q 1 : P) : ℝ) = r - α * ε := by simp [hq]
      have hqq : (fun t => (fun t => q (t + 1)) (t + 1)) = fun _ => (⟨r, hr⟩ : P) := by
        funext t; simp [hq]
      have r1P := hmemP (r + ε) m0 r hr
      have e1 := hshift q r hr
      rw [hq0] at e1
      have e2 := hshift (fun t => q (t + 1)) _ r1P
      simp only [hq1] at e2
      rw [hqq, show α * (α * r + (1 - α) * (r + ε)) + (1 - α) * (r - α * ε) = r by ring] at e2
      have eK := hK r hr
      have hFq := hFle q r hr
      have hVr := hVK r hr hrS
      set K := F (fun _ => (⟨r, hr⟩ : P)) r
      have hVK' : value Pf α β pbar r ≤ K := by nlinarith
      have hKK : K - β ^ 2 * K = Pf r r + β * Pf r r := by
        have : K = Pf r r + β * K := by linarith
        linear_combination (1 + β) * this
      have H0 : H 0 = Pf r r + β * Pf r r := by
        simp only [hH]
        rw [show r + 0 = r by ring, show r - α * 0 = r by ring,
          show α * r + (1 - α) * r = r by ring]
      rw [H0]
      simp only [hH]
      nlinarith
    have hloc : IsLocalMax H 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hm] with ε hε
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
      exact hdev ε hε
    -- derivative of H at 0
    set L := fderiv ℝ (Function.uncurry R) ((0 : ℝ), r) with hL
    have hRd : HasFDerivAt (Function.uncurry R) L ((0 : ℝ), r) :=
      (hA2.differentiable _).hasFDerivAt
    have hpath1 : HasDerivAt (fun ε : ℝ => ((-ε, r) : ℝ × ℝ)) ((-1, 0) : ℝ × ℝ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).neg).prodMk (hasDerivAt_const (0 : ℝ) r)
    have hpath2 : HasDerivAt (fun ε : ℝ => ((ε, r + (1 - α) * ε) : ℝ × ℝ))
        ((1, (1 - α) * 1) : ℝ × ℝ) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (((hasDerivAt_id (0 : ℝ)).const_mul (1 - α)).const_add r)
    have hg1 : HasDerivAt (fun ε : ℝ => R (-ε) r) (L ((-1, 0) : ℝ × ℝ)) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq _ hRd hpath1 (by simp)
    have hg2 : HasDerivAt (fun ε : ℝ => R ε (r + (1 - α) * ε)) (L ((1, (1 - α) * 1) : ℝ × ℝ)) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq _ hRd hpath2 (by simp)
    have hpx : HasDerivAt (fun x : ℝ => ((x, r) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) r)
    have hgx : HasDerivAt (fun x : ℝ => R x r) (L ((1, 0) : ℝ × ℝ)) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq _ hRd hpx (by simp)
    have hpy : HasDerivAt (fun y : ℝ => (((0 : ℝ), y) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) r :=
      (hasDerivAt_const r (0 : ℝ)).prodMk (hasDerivAt_id r)
    have hgy : HasDerivAt (fun y : ℝ => R 0 y) (L ((0, 1) : ℝ × ℝ)) r :=
      HasFDerivAt.comp_hasDerivAt_of_eq _ hRd hpy (by simp)
    have hL01 : L ((0, 1) : ℝ × ℝ) = 0 := by
      have hc : (fun y : ℝ => R 0 y) = fun _ => (0 : ℝ) := by funext y; exact hA1.R_zero y
      rw [hc] at hgy
      exact hgy.unique (hasDerivAt_const r 0)
    have hL10 : L ((1, 0) : ℝ × ℝ) = refSlope R r := by
      unfold refSlope; rw [hgx.deriv]
    have hLneg : L ((-1, 0) : ℝ × ℝ) = - L ((1, 0) : ℝ × ℝ) := by
      rw [← map_neg]; congr 1; ext <;> simp
    have hLsum : L ((1, (1 - α) * 1) : ℝ × ℝ) = L ((1, 0) : ℝ × ℝ) + (1 - α) * L ((0, 1) : ℝ × ℝ) := by
      have e : ((1, (1 - α) * 1) : ℝ × ℝ) = ((1, 0) : ℝ × ℝ) + (1 - α) • ((0, 1) : ℝ × ℝ) := by
        ext <;> simp
      rw [e, map_add, map_smul, smul_eq_mul]
    have hπ0 : HasDerivAt (baseProfit d) (deriv (baseProfit d) r) r := (hdiffπ r).hasDerivAt
    have hπ1 : HasDerivAt (fun ε => baseProfit d (r + ε)) (deriv (baseProfit d) r) 0 := by
      have := HasDerivAt.comp_of_eq 0 hπ0 ((hasDerivAt_id (0 : ℝ)).const_add r) (by simp)
      rw [mul_one] at this
      exact this
    have hπ2 : HasDerivAt (fun ε => baseProfit d (r - α * ε)) (deriv (baseProfit d) r * (-α)) 0 := by
      have hp : HasDerivAt (fun ε : ℝ => r - α * ε) (-α) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul α).const_sub r
      exact HasDerivAt.comp_of_eq 0 hπ0 hp (by simp)
    have hHeq : H = fun ε => (baseProfit d (r + ε) + (r + ε) * R (-ε) r) +
        β * (baseProfit d (r - α * ε) + (r - α * ε) * R ε (r + (1 - α) * ε)) := by
      funext ε
      simp only [hH]
      rw [hsplit, hsplit, show r - (r + ε) = -ε by ring,
        show α * r + (1 - α) * (r + ε) - (r - α * ε) = ε by ring,
        show α * r + (1 - α) * (r + ε) = r + (1 - α) * ε by ring]
    have hHd := ((hπ1.add (((hasDerivAt_id (0 : ℝ)).const_add r).mul hg1)).add
      ((hπ2.add ((((hasDerivAt_id (0 : ℝ)).const_mul α).const_sub r).mul hg2)).const_mul β))
    have hz := hloc.hasDerivAt_eq_zero (f := H) (by rw [hHeq]; exact hHd)
    rw [hLneg, hLsum, hL01, hL10] at hz
    simp only [id, neg_zero, hA1.R_zero, add_zero, mul_zero, sub_zero, zero_add, mul_one,
      one_mul] at hz
    linarith
  -- the boundary points are never weak steady states
  have hπnn : ∀ a ∈ P, 0 ≤ baseProfit d a := by
    intro a ha
    rw [← hdiag]
    have := hA1.nonneg a ha a ha
    exact mul_nonneg ha.1 this
  have hnot0 : ¬ ((0 : ℝ) ∈ S 0) := by
    intro h0S
    have h0P : (0 : ℝ) ∈ P := ⟨le_rfl, hpbar.le⟩
    obtain ⟨b, hbP, hbpos⟩ : ∃ b ∈ P, 0 < baseProfit d b := by
      have h := hA3.base_not_antitone
      simp only [AntitoneOn, not_forall, not_le] at h
      obtain ⟨a, ha, b, hb, -, hlt⟩ := h
      exact ⟨b, hb, lt_of_le_of_lt (hπnn a ha) hlt⟩
    have hb0 : 0 < b := by
      rcases eq_or_lt_of_le hbP.1 with h | h
      · rw [← h] at hbpos; simp [baseProfit] at hbpos
      · exact h
    have hdb : 0 < demand d R b b := by
      have : baseProfit d b = b * demand d R b b := by rw [← hdiag]; rfl
      rw [this] at hbpos
      exact pos_of_mul_pos_right hbpos hb0.le
    set c : ℕ → P := fun _ => ⟨b, hbP⟩ with hc
    set rt : ℕ → ℝ := fun t => refPath α 0 (fun s => ((c s : P) : ℝ)) t with hrt
    have hrtP : ∀ t, rt t ∈ P := fun t => refPath_mem pbar α 0 hα₀ hα₁ h0P c t
    have hrtlim : Tendsto rt atTop (𝓝 b) := by
      have e : ∀ t, rt t = b + α ^ t * (0 - b) := by
        intro t
        have := refPath_const α 0 b t
        simp only [hrt, hc]
        linarith
      have : Tendsto (fun t : ℕ => b + α ^ t * (0 - b)) atTop (𝓝 (b + 0 * (0 - b))) :=
        tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hα₀ hα₁).mul_const _)
      simp only [zero_mul, add_zero] at this
      exact (tendsto_congr e).mpr this
    have hcont : ContinuousWithinAt (fun r => demand d R b r) P b := by
      have h1 := (hA1.continuous (b, b) ⟨hbP, hbP⟩)
      have h2 : ContinuousWithinAt (fun r : ℝ => ((b, r) : ℝ × ℝ)) P b :=
        (continuous_const.prodMk continuous_id).continuousWithinAt
      exact h1.comp h2 (fun r hr => ⟨hbP, hr⟩)
    have hlim2 : Tendsto (fun t => demand d R b (rt t)) atTop (𝓝 (demand d R b b)) :=
      hcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hrtlim, Filter.Eventually.of_forall hrtP⟩)
    obtain ⟨t₀, ht₀⟩ := (hlim2.eventually_const_lt hdb).exists
    have hterm : ∀ t, 0 ≤ β ^ t * Pf ((c t : P) : ℝ) (rt t) := by
      intro t
      exact mul_nonneg (pow_pos hβ₀ t).le (mul_nonneg hbP.1 (hA1.nonneg b hbP _ (hrtP t)))
    have hpos : 0 < β ^ t₀ * Pf ((c t₀ : P) : ℝ) (rt t₀) :=
      mul_pos (pow_pos hβ₀ t₀) (mul_pos hb0 ht₀)
    have hle : β ^ t₀ * Pf ((c t₀ : P) : ℝ) (rt t₀) ≤ F c 0 :=
      (hsum c 0 h0P).le_tsum t₀ (fun j _ => hterm j)
    have h1 := hFle c 0 h0P
    have h2 := hVK 0 h0P h0S
    have h3 : Pf 0 0 = 0 := by simp [hPi, profit]
    rw [h3] at h2
    have : value Pf α β pbar 0 ≤ 0 := by nlinarith
    linarith
  have hnotp : ¬ (pbar ∈ S pbar) := by
    intro hpS
    have hpP : pbar ∈ P := ⟨hpbar.le, le_rfl⟩
    obtain ⟨y, hyP, hylt⟩ : ∃ y ∈ P, baseProfit d pbar < baseProfit d y := by
      have h := hA3.base_not_monotone
      simp only [MonotoneOn, not_forall, not_le] at h
      obtain ⟨x, hx, y, hy, hxy, hlt⟩ := h
      rcases eq_or_lt_of_le hy.2 with hyp | hyp
      · exact ⟨x, hx, hyp ▸ hlt⟩
      · refine ⟨y, hy, ?_⟩
        by_contra hcon
        push_neg at hcon
        have hxy' : x < y := lt_of_le_of_ne hxy (by rintro rfl; exact lt_irrefl _ hlt)
        have hpx : 0 < pbar - x := by linarith
        have hconc : ((pbar - y) / (pbar - x)) • baseProfit d x +
            ((y - x) / (pbar - x)) • baseProfit d pbar ≤
            baseProfit d (((pbar - y) / (pbar - x)) • x + ((y - x) / (pbar - x)) • pbar) :=
          hA3.base_concave.2 hx hpP (div_nonneg (by linarith) hpx.le)
          (div_nonneg (by linarith) hpx.le) (by field_simp; ring)
        have e : ((pbar - y) / (pbar - x)) • x + ((y - x) / (pbar - x)) • pbar = y := by
          simp only [smul_eq_mul]; field_simp; ring
        rw [e] at hconc
        simp only [smul_eq_mul] at hconc
        have ht : 0 < (pbar - y) / (pbar - x) := div_pos (by linarith) hpx
        have hs : (pbar - y) / (pbar - x) + (y - x) / (pbar - x) = 1 := by
          field_simp; ring
        have hs0 : 0 ≤ (y - x) / (pbar - x) := div_nonneg (by linarith) hpx.le
        have k1 := mul_nonneg hs0 (sub_nonneg.mpr hcon)
        have k2 := mul_pos ht (sub_pos.mpr hlt)
        have k3 : ((pbar - y) / (pbar - x) + (y - x) / (pbar - x)) * baseProfit d y =
          baseProfit d y := by rw [hs, one_mul]
        nlinarith
    set c : ℕ → P := fun _ => ⟨y, hyP⟩ with hc
    set rt : ℕ → ℝ := fun t => refPath α pbar (fun s => ((c s : P) : ℝ)) t with hrt
    have hrtP : ∀ t, rt t ∈ P := fun t => refPath_mem pbar α pbar hα₀ hα₁ hpP c t
    have hterm : ∀ t, β ^ t * baseProfit d y ≤ β ^ t * Pf ((c t : P) : ℝ) (rt t) := by
      intro t
      refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ₀ t).le
      show baseProfit d y ≤ Pf y (rt t)
      rw [hsplit]
      have hgap : rt t - y = α ^ t * (pbar - y) := by
        have := refPath_const α pbar y t
        simp only [hrt, hc]
        linarith
      have hgap0 : 0 ≤ rt t - y := by rw [hgap]; exact mul_nonneg (pow_nonneg hα₀ t) (by linarith [hyP.2])
      have hm := hA1.monotone_gain (rt t) (hrtP t)
      have hR0 : R 0 (rt t) ≤ R (rt t - y) (rt t) :=
        hm ⟨by linarith [(hrtP t).2], (hrtP t).1⟩ ⟨by linarith [hyP.2], by linarith [hyP.1]⟩ hgap0
      rw [hA1.R_zero] at hR0
      nlinarith [hyP.1]
    have hgeo' := hgeo.mul_right (baseProfit d y)
    have hle : baseProfit d y * (1 - β)⁻¹ ≤ F c pbar := by
      rw [← tsum_geometric_of_lt_one hβ₀.le hβ₁, ← tsum_mul_left]
      have := hgeo'.tsum_le_tsum hterm (hsum c pbar hpP)
      simpa [mul_comm] using this
    have h1 := hFle c pbar hpP
    have h2 := hVK pbar hpP hpS
    rw [hdiag] at h2
    have h3 : baseProfit d y * (1 - β)⁻¹ * (1 - β) = baseProfit d y := by field_simp
    nlinarith
  -- every weak steady state satisfies equation (3)
  have hEq3 : ∀ r ∈ P, r ∈ S r →
      deriv (baseProfit d) r / (1 - β) = r * refSlope R r / (1 - α * β) := by
    intro r hr hrS
    have h0 : 0 < r := by
      rcases eq_or_lt_of_le hr.1 with h | h
      · exact absurd (h ▸ hrS) hnot0
      · exact h
    have h1 : r < pbar := by
      rcases eq_or_lt_of_le hr.2 with h | h
      · exact absurd (h ▸ hrS) hnotp
      · exact h
    have := hFOC r hr hrS h0 h1
    rw [div_eq_div_iff h1β.ne' h1αβ.ne']
    linarith
  -- uniqueness of the root of (3) in P
  have hπanti : AntitoneOn (deriv (baseProfit d)) P :=
    hA3.base_concave.antitoneOn_deriv (fun x _ => hdiffπ x)
  have hroot : ∀ q₁ ∈ P, ∀ q₂ ∈ P,
      deriv (baseProfit d) q₁ / (1 - β) = q₁ * refSlope R q₁ / (1 - α * β) →
      deriv (baseProfit d) q₂ / (1 - β) = q₂ * refSlope R q₂ / (1 - α * β) → q₁ = q₂ := by
    have key : ∀ q₁ ∈ P, ∀ q₂ ∈ P, q₁ < q₂ →
        deriv (baseProfit d) q₁ / (1 - β) = q₁ * refSlope R q₁ / (1 - α * β) →
        deriv (baseProfit d) q₂ / (1 - β) = q₂ * refSlope R q₂ / (1 - α * β) → False := by
      intro q₁ h₁ q₂ h₂ hlt e₁ e₂
      rw [div_eq_div_iff h1β.ne' h1αβ.ne'] at e₁ e₂
      have hs := hA3.diag_strictAnti h₁ h₂ hlt
      have ha := hπanti h₁ h₂ hlt.le
      simp only at hs
      -- q λ = κ π' with κ = (1 - αβ)/(1 - β) ≥ 1
      have hk : (1 - α * β) - (1 - β) = β * (1 - α) := by ring
      have hk0 : 0 ≤ β * (1 - α) := mul_nonneg hβ₀.le h1α.le
      nlinarith
    intro q₁ h₁ q₂ h₂ e₁ e₂
    rcases lt_trichotomy q₁ q₂ with h | h | h
    · exact (key q₁ h₁ q₂ h₂ h e₁ e₂).elim
    · exact h
    · exact (key q₂ h₂ q₁ h₁ h e₂ e₁).elim
  -- optimal paths
  have hpriceS : ∀ r ∈ P, optPrice Pf α β pbar r ∈ S r := fun r hr => by
    rw [hopt]; exact hSmem r hr
  have hoptP : ∀ r ∈ P, optPrice Pf α β pbar r ∈ P := fun r hr => (hpriceS r hr).1
  have hstateP : ∀ r₀ ∈ P, ∀ t, statePath Pf α β pbar r₀ t ∈ P := by
    intro r₀ hr₀ t
    induction t with
    | zero => exact hr₀
    | succ t ih =>
      show α * statePath Pf α β pbar r₀ t +
        (1 - α) * optPrice Pf α β pbar (statePath Pf α β pbar r₀ t) ∈ P
      exact hmemP _ (hoptP _ ih) _ ih
  have hpath : ∀ r₀ ∈ P, ∃ L ∈ P, L ∈ S L ∧
      (Monotone (statePath Pf α β pbar r₀) ∨ Antitone (statePath Pf α β pbar r₀)) ∧
      Tendsto (statePath Pf α β pbar r₀) atTop (𝓝 L) ∧
      Tendsto (pricePath Pf α β pbar r₀) atTop (𝓝 L) := by
    intro r₀ hr₀
    have hsP := hstateP r₀ hr₀
    have hmono : Monotone (statePath Pf α β pbar r₀) ∨ Antitone (statePath Pf α β pbar r₀) := by
      rcases le_total (statePath Pf α β pbar r₀ 0) (statePath Pf α β pbar r₀ 1) with h | h
      · left
        apply monotone_nat_of_le_succ
        intro t
        induction t with
        | zero => exact h
        | succ t ih => exact hqmono (hsP t) (hsP (t + 1)) ih
      · right
        apply antitone_nat_of_succ_le
        intro t
        induction t with
        | zero => exact h
        | succ t ih => exact hqmono (hsP (t + 1)) (hsP t) ih
    obtain ⟨L, hL⟩ : ∃ L, Tendsto (statePath Pf α β pbar r₀) atTop (𝓝 L) := by
      rcases hmono with h | h
      · exact ⟨_, tendsto_atTop_ciSup h ⟨pbar, by rintro _ ⟨t, rfl⟩; exact (hsP t).2⟩⟩
      · exact ⟨_, tendsto_atTop_ciInf h ⟨0, by rintro _ ⟨t, rfl⟩; exact (hsP t).1⟩⟩
    have hLP : L ∈ P := isClosed_Icc.mem_of_tendsto hL (Filter.Eventually.of_forall hsP)
    have hpp : ∀ t, pricePath Pf α β pbar r₀ t =
        (statePath Pf α β pbar r₀ (t + 1) - α * statePath Pf α β pbar r₀ t) / (1 - α) := by
      intro t
      show optPrice Pf α β pbar (statePath Pf α β pbar r₀ t) =
        (α * statePath Pf α β pbar r₀ t + (1 - α) * optPrice Pf α β pbar
          (statePath Pf α β pbar r₀ t) - α * statePath Pf α β pbar r₀ t) / (1 - α)
      field_simp
      ring
    have hppL : Tendsto (pricePath Pf α β pbar r₀) atTop (𝓝 L) := by
      have h1 : Tendsto (fun t => (statePath Pf α β pbar r₀ (t + 1) -
          α * statePath Pf α β pbar r₀ t) / (1 - α)) atTop (𝓝 ((L - α * L) / (1 - α))) :=
        ((hL.comp (tendsto_add_atTop_nat 1)).sub (hL.const_mul α)).div_const _
      have e : (L - α * L) / (1 - α) = L := by field_simp
      rw [e] at h1
      exact (tendsto_congr hpp).mpr h1
    have hppP : ∀ t, pricePath Pf α β pbar r₀ t ∈ P := fun t => hoptP _ (hsP t)
    have hppS : ∀ t, pricePath Pf α β pbar r₀ t ∈ S (statePath Pf α β pbar r₀ t) :=
      fun t => hpriceS _ (hsP t)
    have hLS : L ∈ S L := by
      refine ⟨hLP, fun p' hp' => ?_⟩
      have hz : Tendsto (fun t => ((pricePath Pf α β pbar r₀ t, statePath Pf α β pbar r₀ t) :
          ℝ × ℝ)) atTop (𝓝[P ×ˢ P] (L, L)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hppL.prodMk_nhds hL,
          Filter.Eventually.of_forall (fun t => ⟨hppP t, hsP t⟩)⟩
      have h1 : Tendsto (fun t => bellmanObj Pf α β pbar (pricePath Pf α β pbar r₀ t)
          (statePath Pf α β pbar r₀ t)) atTop (𝓝 (bellmanObj Pf α β pbar L L)) :=
        (hWjc (L, L) ⟨hLP, hLP⟩).tendsto.comp hz
      have hz' : Tendsto (fun t => ((p', statePath Pf α β pbar r₀ t) : ℝ × ℝ)) atTop
          (𝓝[P ×ˢ P] (p', L)) :=
        tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds hL,
          Filter.Eventually.of_forall (fun t => ⟨hp', hsP t⟩)⟩
      have h2 : Tendsto (fun t => bellmanObj Pf α β pbar p' (statePath Pf α β pbar r₀ t)) atTop
          (𝓝 (bellmanObj Pf α β pbar p' L)) :=
        (hWjc (p', L) ⟨hp', hLP⟩).tendsto.comp hz'
      exact le_of_tendsto_of_tendsto' h2 h1 (fun t => (hppS t).2 p' hp')
    exact ⟨L, hLP, hLS, hmono, hL, hppL⟩
  have h0P : (0 : ℝ) ∈ P := ⟨le_rfl, hpbar.le⟩
  obtain ⟨p, hpP, hpS, -, -, -⟩ := hpath 0 h0P
  have hp3 := hEq3 p hpP hpS
  have hss : optPrice Pf α β pbar p = p := by
    have hge : p ≤ optPrice Pf α β pbar p := by rw [hopt]; exact le_csSup (hSbdd p) hpS
    by_contra hne
    have hgt : p < optPrice Pf α β pbar p := lt_of_le_of_ne hge (Ne.symm hne)
    obtain ⟨L', hL'P, hL'S, hmon, hL', -⟩ := hpath p hpP
    have hL'eq : L' = p := hroot L' hL'P p hpP (hEq3 L' hL'P hL'S) hp3
    have hs1 : p < statePath Pf α β pbar p 1 := by
      show p < α * p + (1 - α) * optPrice Pf α β pbar p
      nlinarith
    rcases hmon with hm | hm
    · have : statePath Pf α β pbar p 1 ≤ L' := hm.ge_of_tendsto hL' 1
      linarith
    · have : statePath Pf α β pbar p 1 ≤ statePath Pf α β pbar p 0 := hm (Nat.zero_le 1)
      have h00 : statePath Pf α β pbar p 0 = p := rfl
      linarith
  refine ⟨p, ⟨hpP, hss⟩, ?_, hp3, ?_, ?_⟩
  · intro q hq
    have hqS : q ∈ S q := by
      have := hSmem q hq.1
      rw [← hopt, hq.2] at this
      exact this
    exact hroot q hq.1 p hpP (hEq3 q hq.1 hqS) hp3
  · intro q hq hq3
    exact hroot q hq p hpP hq3 hp3
  · intro r₀ hr₀
    obtain ⟨L, hLP, hLS, hmon, hL, hpp⟩ := hpath r₀ hr₀
    have hLp : L = p := hroot L hLP p hpP (hEq3 L hLP hLS) hp3
    rw [hLp] at hL hpp
    exact ⟨hpp, hmon, hL⟩
