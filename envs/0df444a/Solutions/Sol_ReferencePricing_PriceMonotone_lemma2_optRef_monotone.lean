-- Prove2me | solution 1 for ReferencePricing.PriceMonotone.lemma2_optRef_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:31:04.831758+00:00
-- url     : https://prove2.me/submissions/14d5e6e1-6cd3-49e2-9725-d24bd26b8f65

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

namespace RefPrice3L2

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

end RefPrice3L2

open RefPrice3L2

theorem solution
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d) :
    MonotoneOn (optRef (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by
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
  -- concave four-point inequality
  have hcc : ∀ f : ℝ → ℝ, ConcaveOn ℝ P f → ∀ a b c e : ℝ, a ∈ P → c ∈ P → a ≤ b → b ≤ c →
      a ≤ e → e ≤ c → b + e = a + c → f a + f c ≤ f b + f e := by
    intro f hf a b c e ha hc h1 h2 h3 h4 h5
    have := convex_sum_le P (fun x => -f x) hf.neg a b c e ha hc h1 h2 h3 h4 h5
    linarith
  have h1α : 0 < 1 - α := by linarith
  -- Topkis on q = α r + (1 - α) p
  intro r₁ hr₁ r₂ hr₂ hr
  show α * r₁ + (1 - α) * optPrice Pf α β pbar r₁ ≤ α * r₂ + (1 - α) * optPrice Pf α β pbar r₂
  rw [hopt, hopt]
  obtain ⟨p₂, hp₂⟩ := hSne r₂ hr₂
  have hS2 : ∀ x ∈ S r₂, x ≤ sSup (S r₂) := fun x hx => le_csSup (hSbdd r₂) hx
  have key : ∀ p₁ ∈ S r₁, p₁ ≤ (α * r₂ + (1 - α) * sSup (S r₂) - α * r₁) / (1 - α) := by
    intro p₁ hp₁
    rw [le_div_iff₀ h1α]
    rcases le_total (α * r₁ + (1 - α) * p₁) (α * r₂ + (1 - α) * p₂) with hq | hq
    · have := hS2 p₂ hp₂
      nlinarith
    · set δ := α * (r₂ - r₁) / (1 - α) with hδ
      have hδ0 : 0 ≤ δ := div_nonneg (mul_nonneg hα₀ (by linarith)) h1α.le
      have hq' : p₂ ≤ p₁ - δ := by
        rw [hδ, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ h1α]; nlinarith
      have hp1 := hp₁.1
      have hp2 := hp₂.1
      have m1 : p₁ - δ ∈ P := ⟨by linarith [hp2.1], by linarith [hp1.2]⟩
      have m2 : p₂ + δ ∈ P := ⟨by linarith [hp2.1], by linarith [hp1.2]⟩
      have eq1 : α * r₂ + (1 - α) * (p₁ - δ) = α * r₁ + (1 - α) * p₁ := by
        rw [hδ]; field_simp; ring
      have eq2 : α * r₁ + (1 - α) * (p₂ + δ) = α * r₂ + (1 - α) * p₂ := by
        rw [hδ]; field_simp; ring
      -- supermodularity of the short-term profit along the shifted points
      have c1 := hcc (baseProfit d) hA3.base_concave p₂ (p₂ + δ) p₁ (p₁ - δ) hp2 hp1
        (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
      have c2 := hcc (fun p => refProfit R p r₁) (hA3.ref_concave r₁ hr₁) p₂ (p₂ + δ) p₁
        (p₁ - δ) hp2 hp1 (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
      have c3 := hA3.ref_supermodular p₂ hp2 (p₁ - δ) m1 r₁ hr₁ r₂ hr₂ hq' hr
      have hsplit : ∀ p r, Pf p r = baseProfit d p + refProfit R p r := by
        intro p r; simp only [hPi, profit, demand, baseProfit, refProfit]; ring
      have hmem : p₁ - δ ∈ S r₂ := by
        refine ⟨m1, fun p' hp' => ?_⟩
        have e2 := hp₁.2 (p₂ + δ) m2
        have e3 := hp₂.2 p' hp'
        rw [hW, hW] at e2
        rw [hW, hW] at e3
        rw [hW (p₁ - δ), eq1, hW p']
        rw [eq2] at e2
        simp only [hsplit] at e2 e3 ⊢
        linarith
      have := hS2 _ hmem
      nlinarith
  have hsup1 : sSup (S r₁) ≤ (α * r₂ + (1 - α) * sSup (S r₂) - α * r₁) / (1 - α) :=
    csSup_le (hSne r₁ hr₁) key
  rw [le_div_iff₀ h1α] at hsup1
  nlinarith
