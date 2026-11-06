-- Prove2me | solution 1 for SAARate.SharpLD.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:52:35.003201+00:00
-- url     : https://prove2.me/submissions/dece95aa-d8ff-4d6d-900d-732f6fc9eed4

import Mathlib
import Definitions.Def_SAARate_SharpLD_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace SharpLDSol

open SAARate.Sharp

/-- the line restriction of a convex function is convex -/
lemma line_convex {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x d : E m) :
    ConvexOn ℝ univ (fun t : ℝ => g (x + t • d)) := by
  refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
  have h1 : x + (μ • a + ν • b) • d = μ • (x + a • d) + ν • (x + b • d) := by
    have : x = (μ + ν) • x := by rw [hμν, one_smul]
    conv_lhs => rw [this]
    simp only [add_smul, smul_add, smul_smul, smul_eq_mul]
    try abel
  simp only [smul_eq_mul] at h1 ⊢
  rw [show x + (μ * a + ν * b) • d = μ • (x + a • d) + ν • (x + b • d) by
    rw [← h1]]
  exact hg.2 (mem_univ _) (mem_univ _) hμ hν hμν

lemma dd_tendsto {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x d : E m) :
    Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t) (𝓝[>] 0) (𝓝 (dirDeriv g x d)) := by
  set φ := fun t : ℝ => g (x + t • d) with hφdef
  have hφ := line_convex hg x d
  have H := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (x := 0) (by simp)
  have H2 := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mp H
  have hT : Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t) (𝓝[>] 0)
      (𝓝 (derivWithin φ (Ioi 0) 0)) := by
    refine H2.congr' ?_
    filter_upwards with t
    simp [slope_def_field]
  have : dirDeriv g x d = derivWithin φ (Ioi 0) 0 := hT.limUnder_eq
  rw [this]; exact hT

lemma dd_le {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x d : E m) {t : ℝ} (ht : 0 < t) :
    dirDeriv g x d ≤ (g (x + t • d) - g x) / t := by
  refine le_of_tendsto (dd_tendsto hg x d) ?_
  have hφ := line_convex hg x d
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), s < t := nhdsWithin_le_nhds (eventually_lt_nhds ht)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
  have := hφ.secant_mono (a := 0) (x := s) (y := t) (mem_univ _) (mem_univ _) (mem_univ _)
    hs0.ne' ht.ne' hs.le
  simpa using this

lemma dd_quot_mono {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x d : E m) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    (g (x + s • d) - g x) / s ≤ (g (x + t • d) - g x) / t := by
  have hφ := line_convex hg x d
  have := hφ.secant_mono (a := 0) (x := s) (y := t) (mem_univ _) (mem_univ _) (mem_univ _)
    hs.ne' (hs.trans_le hst).ne' hst
  simpa using this

lemma dd_zero {m : ℕ} (g : E m → ℝ) (x : E m) : dirDeriv g x 0 = 0 := by
  have hT : Tendsto (fun t : ℝ => (g (x + t • (0 : E m)) - g x) / t) (𝓝[>] 0) (𝓝 0) := by
    simp
  exact hT.limUnder_eq

lemma dd_smul {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x b : E m) {r : ℝ} (hr : 0 < r) :
    dirDeriv g x (r • b) = r * dirDeriv g x b := by
  have h1 := dd_tendsto hg x (r • b)
  have h2 : Tendsto (fun t : ℝ => r * ((g (x + (r * t) • b) - g x) / (r * t))) (𝓝[>] 0)
      (𝓝 (r * dirDeriv g x b)) := by
    refine (dd_tendsto hg x b).comp ?_ |>.const_mul r
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => r * t) (𝓝 0) (𝓝 (r * 0)) := tendsto_id.const_mul r
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos hr ht
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [smul_smul, mul_comm t r]
  field_simp

lemma dd_add {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x a b : E m) :
    dirDeriv g x (a + b) ≤ dirDeriv g x a + dirDeriv g x b := by
  have h1 := dd_tendsto hg x (a + b)
  have h2 : Tendsto (fun t : ℝ => (g (x + (2 * t) • a) - g x) / (2 * t) +
      (g (x + (2 * t) • b) - g x) / (2 * t)) (𝓝[>] 0)
      (𝓝 (dirDeriv g x a + dirDeriv g x b)) := by
    have hc : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => 2 * t) (𝓝 0) (𝓝 (2 * 0)) := tendsto_id.const_mul 2
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        show 0 < 2 * t
        positivity
    exact ((dd_tendsto hg x a).comp hc).add ((dd_tendsto hg x b).comp hc)
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hconv := hg.2 (mem_univ (x + (2 * t) • a)) (mem_univ (x + (2 * t) • b))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have heq : (1/2 : ℝ) • (x + (2 * t) • a) + (1/2 : ℝ) • (x + (2 * t) • b) = x + t • (a + b) := by
    simp only [smul_add, smul_smul]
    have : x = (1/2 : ℝ) • x + (1/2 : ℝ) • x := by rw [← add_smul]; norm_num
    rw [show (1/2 : ℝ) * (2 * t) = t by ring]
    conv_rhs => rw [this]
    abel
  rw [heq] at hconv
  simp only [smul_eq_mul] at hconv
  have hr : (g (x + (2 * t) • a) - g x) / (2 * t) + (g (x + (2 * t) • b) - g x) / (2 * t)
      = ((1/2 * g (x + (2 * t) • a) + 1/2 * g (x + (2 * t) • b)) - g x) / t := by
    field_simp; ring
  rw [hr]
  exact div_le_div_of_nonneg_right (by linarith) ht.le


lemma dd_bound {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x : E m) {κ : ℝ}
    (hb : ∀ d ∈ Metric.sphere (0 : E m) 1, |dirDeriv g x d| ≤ κ) (v : E m) :
    dirDeriv g x v ≤ κ * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv; simp [dd_zero]
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E m) 1 := by
      simp [norm_smul, hn.ne']
    have hvv : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [hvv, dd_smul hg x _ hn, ← hvv]
    have := (abs_le.mp (hb _ hu)).2
    nlinarith

lemma dd_lip {m : ℕ} {g : E m → ℝ} (hg : ConvexOn ℝ univ g) (x : E m) {κ : ℝ}
    (hb : ∀ d ∈ Metric.sphere (0 : E m) 1, |dirDeriv g x d| ≤ κ) (d d' : E m) :
    dirDeriv g x d' ≤ dirDeriv g x d + κ * ‖d' - d‖ := by
  have := dd_add hg x d (d' - d)
  rw [add_sub_cancel] at this
  linarith [dd_bound hg x hb (d' - d)]

lemma hoeff {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (Q : Measure S) [IsProbabilityMeasure Q] (ω : ℕ → S → Ω) (hmeas : ∀ j, Measurable (ω j))
    (hind : iIndepFun ω Q) (hmap : ∀ j, Q.map (ω j) = P) (g : Ω → ℝ) (hg : Measurable g)
    {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hgb : ∀ x, g x ∈ Icc (-κ) κ)
    (hmean : c ≤ ∫ x, g x ∂P) (N : ℕ) :
    Q {s | ∑ j ∈ Finset.range N, g (ω j s) ≤ N * (c / 2)} ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2 / (8 * κ ^ 2)) * N)) := by
  set μ' := ∫ x, g x ∂P with hμ'
  have hXmean : ∀ j, Q[fun s => g (ω j s)] = μ' := by
    intro j
    rw [hμ', ← hmap j, integral_map (hmeas j).aemeasurable hg.aestronglyMeasurable]
  set c' : NNReal := (‖κ - -κ‖₊ / 2) ^ 2 with hc'
  have hc'r : (c' : ℝ) = κ ^ 2 := by
    simp only [hc', NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    rw [show κ - -κ = 2 * κ by ring, abs_of_pos (by linarith)]
    push_cast; ring
  have hsub : ∀ j < N, HasSubgaussianMGF (fun s => μ' - g (ω j s)) c' Q := by
    intro j _
    have := hasSubgaussianMGF_of_mem_Icc (μ := Q) (X := fun s => g (ω j s))
      ((hg.comp (hmeas j)).aemeasurable) (ae_of_all _ (fun s => hgb _))
    rw [hXmean j] at this
    convert this.neg using 1
    funext s; simp
  have hind' : iIndepFun (fun j s => μ' - g (ω j s)) Q :=
    hind.comp (fun _ x => μ' - g x) (fun _ => measurable_const.sub hg)
  have hH := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind' hsub (ε := N * (c / 2))
    (by positivity)
  have hsubset : {s | ∑ j ∈ Finset.range N, g (ω j s) ≤ N * (c / 2)} ⊆
      {s | (N : ℝ) * (c / 2) ≤ ∑ j ∈ Finset.range N, (μ' - g (ω j s))} := by
    intro s hs
    simp only [mem_setOf_eq] at hs ⊢
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  calc Q {s | ∑ j ∈ Finset.range N, g (ω j s) ≤ N * (c / 2)}
      ≤ Q {s | (N : ℝ) * (c / 2) ≤ ∑ j ∈ Finset.range N, (μ' - g (ω j s))} :=
        measure_mono hsubset
    _ = ENNReal.ofReal (Q.real {s | (N : ℝ) * (c / 2) ≤
          ∑ j ∈ Finset.range N, (μ' - g (ω j s))}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-(c ^ 2 / (8 * κ ^ 2)) * N)) := by
        apply ENNReal.ofReal_le_ofReal
        refine hH.trans (le_of_eq ?_)
        congr 1
        rw [hc'r]
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN; simp
        · have : (0 : ℝ) < N := by exact_mod_cast hN
          field_simp
          ring


lemma tn_tendsto : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall (fun n => by simp only [mem_Ioi]; positivity)⟩

lemma mean_ge {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : E m → Ω → ℝ) (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P) (Θ : Set (E m)) (hΘv : Convex ℝ Θ) (xbar : E m)
    (hxbar : xbar ∈ Θ) {c : ℝ}
    (hsharp : ∀ x ∈ Θ, expectedObj P h x ≥ expectedObj P h xbar + c * ‖x - xbar‖)
    {κ : ℝ} (hκ : 0 < κ)
    (hB : ∀ᵐ ω ∂P, ∀ d ∈ Metric.sphere (0 : E m) 1, |SAARate.SharpLD.eta h xbar d ω| ≤ κ)
    (y : E m) (hy : y ∈ Θ) (hyx : y ≠ xbar) (d : E m) (hd : d = ‖y - xbar‖⁻¹ • (y - xbar)) :
    ∃ g₁ : Ω → ℝ, Measurable g₁ ∧ (∀ x, g₁ x ∈ Icc (-κ) κ) ∧
      (fun ω => SAARate.SharpLD.eta h xbar d ω) =ᵐ[P] g₁ ∧ c ≤ ∫ x, g₁ x ∂P := by
  have hr : 0 < ‖y - xbar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hd1 : d ∈ Metric.sphere (0 : E m) 1 := by
    subst hd; simp [norm_smul, hr.ne']
  have hdn : ‖d‖ = 1 := by simpa using hd1
  set tn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with htn
  have htn_pos : ∀ n, 0 < tn n := fun n => by simp only [htn]; positivity
  have htn_le : ∀ n, tn n ≤ tn 0 := fun n => by
    simp only [htn, Nat.cast_zero, zero_add]
    apply div_le_div_of_nonneg_left zero_le_one zero_lt_one
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  set q : ℕ → Ω → ℝ := fun n ω => (h (xbar + tn n • d) ω - h xbar ω) / tn n with hq
  have hq_int : ∀ n, Integrable (q n) P := fun n => ((hint _).sub (hint _)).div_const _
  have hlim : ∀ ω, Tendsto (fun n => q n ω) atTop (𝓝 (SAARate.SharpLD.eta h xbar d ω)) :=
    fun ω => (dd_tendsto (hconv ω) xbar d).comp tn_tendsto
  have hae : AEMeasurable (fun ω => SAARate.SharpLD.eta h xbar d ω) P :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => (hq_int n).aemeasurable) (ae_of_all _ hlim)
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖q n ω‖ ≤ |q 0 ω| + κ := by
    intro n
    filter_upwards [hB] with ω hω
    have h1 := abs_le.mp (hω d hd1)
    have h2 : SAARate.SharpLD.eta h xbar d ω ≤ q n ω := dd_le (hconv ω) xbar d (htn_pos n)
    have h3 : q n ω ≤ q 0 ω := dd_quot_mono (hconv ω) xbar d (htn_pos n) (htn_le n)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [abs_nonneg (q 0 ω)]
    · linarith [le_abs_self (q 0 ω)]
  have hDCT : Tendsto (fun n => ∫ ω, q n ω ∂P) atTop
      (𝓝 (∫ ω, SAARate.SharpLD.eta h xbar d ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |q 0 ω| + κ)
      (fun n => (hq_int n).aestronglyMeasurable) ((hq_int 0).abs.add (integrable_const κ))
      hbound (ae_of_all _ hlim)
  have hev : ∀ᶠ n in atTop, tn n < ‖y - xbar‖ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)
  have hge : ∀ᶠ n in atTop, c ≤ ∫ ω, q n ω ∂P := by
    filter_upwards [hev] with n hn
    have hmem : xbar + tn n • d ∈ Θ := by
      have := hΘv.add_smul_sub_mem hxbar hy (t := tn n / ‖y - xbar‖)
        ⟨by have := htn_pos n; positivity, (div_le_one hr).mpr hn.le⟩
      convert this using 2
      rw [hd, smul_smul]; congr 1
    have hs := hsharp _ hmem
    simp only [add_sub_cancel_left, norm_smul, hdn, mul_one, Real.norm_eq_abs,
      abs_of_pos (htn_pos n)] at hs
    have hI : ∫ ω, q n ω ∂P = (expectedObj P h (xbar + tn n • d) - expectedObj P h xbar) / tn n := by
      simp only [hq, expectedObj]
      rw [integral_div, integral_sub (hint _) (hint _)]
    rw [hI, le_div_iff₀ (htn_pos n)]
    linarith
  have hmeanEta : c ≤ ∫ ω, SAARate.SharpLD.eta h xbar d ω ∂P := ge_of_tendsto hDCT hge
  set g₀ := hae.mk _ with hg₀
  refine ⟨fun x => max (-κ) (min κ (g₀ x)), measurable_const.max
    (measurable_const.min hae.measurable_mk), fun x => ⟨le_max_left _ _,
      max_le (by linarith) (min_le_left _ _)⟩, ?_, ?_⟩
  · filter_upwards [hae.ae_eq_mk, hB] with ω h1 h2
    have := abs_le.mp (h2 d hd1)
    simp only [← hg₀] at h1
    rw [← h1, min_eq_right this.2, max_eq_right this.1]
  · have hae2 : (fun ω => SAARate.SharpLD.eta h xbar d ω) =ᵐ[P]
        (fun x => max (-κ) (min κ (g₀ x))) := by
      filter_upwards [hae.ae_eq_mk, hB] with ω h1 h2
      have := abs_le.mp (h2 d hd1)
      simp only [← hg₀] at h1
      rw [← h1, min_eq_right this.2, max_eq_right this.1]
    rw [← integral_congr_ae hae2]
    exact hmeanEta

end SharpLDSol

open SAARate.Sharp SharpLDSol in
theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : SAARate.Sharp.E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : SAARate.Sharp.E m) (hA : SAARate.Sharp.AssumptionA P h Θ xbar)
    (κ : ℝ) (hB : SAARate.SharpLD.AssumptionB P h xbar κ)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) :
    ∃ β > 0, ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Q {s | SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ ≠ {xbar}} ≤
        ENNReal.ofReal (Real.exp (-(β - ε) * N)) := by
  obtain ⟨c, hc, hsharp⟩ := hA.sharp
  obtain ⟨hκ, hBae⟩ := hB
  obtain ⟨hmeas, hind, hmap⟩ := hω
  refine ⟨c ^ 2 / (8 * κ ^ 2), by positivity, ?_⟩
  intro ε hε
  set D : Set (E m) := {d | ∃ y ∈ Θ, y ≠ xbar ∧ d = ‖y - xbar‖⁻¹ • (y - xbar)} with hDdef
  have hDs : D ⊆ Metric.sphere 0 1 := by
    rintro d ⟨y, hy, hyx, rfl⟩
    have hr : 0 < ‖y - xbar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    simp [norm_smul, hr.ne']
  have hTB : TotallyBounded D := (isCompact_sphere (0 : E m) 1).totallyBounded.subset hDs
  have hδ : 0 < c / (2 * κ) := by positivity
  obtain ⟨D', hD'D, hD'fin, hcover⟩ := Metric.finite_approx_of_totallyBounded hTB _ hδ
  have hmod : ∀ d, ∃ g₁ : Ω → ℝ, d ∈ D → (Measurable g₁ ∧ (∀ x, g₁ x ∈ Icc (-κ) κ) ∧
      (fun ω => SAARate.SharpLD.eta h xbar d ω) =ᵐ[P] g₁ ∧ c ≤ ∫ x, g₁ x ∂P) := by
    intro d
    by_cases hd : d ∈ D
    · obtain ⟨y, hy, hyx, hdy⟩ := hd
      obtain ⟨g₁, hg⟩ := mean_ge P h hconv hint Θ hΘv xbar hA.mem hsharp hκ hBae y hy hyx d hdy
      exact ⟨g₁, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hd⟩
  choose G hG using hmod
  set goodS : Set S := {s | ∀ j, (∀ d ∈ Metric.sphere (0 : E m) 1,
      |SAARate.SharpLD.eta h xbar d (ω j s)| ≤ κ) ∧
      ∀ d (hd : d ∈ D'), SAARate.SharpLD.eta h xbar d (ω j s) = G d (ω j s)} with hgoodS
  have hgood : Q goodSᶜ = 0 := by
    have hj : ∀ j, ∀ᵐ s ∂Q, (∀ d ∈ Metric.sphere (0 : E m) 1,
        |SAARate.SharpLD.eta h xbar d (ω j s)| ≤ κ) ∧
        ∀ d (hd : d ∈ D'), SAARate.SharpLD.eta h xbar d (ω j s) = G d (ω j s) := by
      intro j
      have hP : ∀ᵐ x ∂P, (∀ d ∈ Metric.sphere (0 : E m) 1,
          |SAARate.SharpLD.eta h xbar d x| ≤ κ) ∧
          ∀ d (hd : d ∈ D'), SAARate.SharpLD.eta h xbar d x = G d x := by
        refine hBae.and ?_
        rw [ae_ball_iff hD'fin.countable]
        intro d hd
        exact ((hG d) (hD'D hd)).2.2.1
      rw [← hmap j] at hP
      exact ae_of_ae_map (hmeas j).aemeasurable hP
    have : ∀ᵐ s ∂Q, s ∈ goodS := ae_all_iff.mpr hj
    exact ae_iff.mp this
  set T := hD'fin.toFinset with hT
  have hK : ∀ᶠ N : ℕ in atTop, (T.card : ℝ) ≤ Real.exp (ε * N) :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hε)).eventually_ge_atTop _
  filter_upwards [hK, eventually_ge_atTop 1] with N hKN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set Ev := {s | SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ ≠ {xbar}}
  have hincl : Ev ∩ goodS ⊆ ⋃ d ∈ T,
      {s | ∑ j ∈ Finset.range N, G d (ω j s) ≤ N * (c / 2)} := by
    rintro s ⟨hsE, hsg⟩
    have hex : ∃ y ∈ Θ, y ≠ xbar ∧ saaObj h (fun j => ω j s) N y ≤
        saaObj h (fun j => ω j s) N xbar := by
      by_contra hcon
      push_neg at hcon
      apply hsE
      ext x
      constructor
      · rintro ⟨hxΘ, hxmin⟩
        by_contra hx
        exact absurd (hxmin xbar hA.mem) (not_le.mpr (hcon x hxΘ hx))
      · intro hx
        rw [mem_singleton_iff] at hx
        subst hx
        refine ⟨hA.mem, fun y hy => ?_⟩
        by_cases hyx : y = x
        · rw [hyx]
        · exact (hcon y hy hyx).le
    obtain ⟨y, hy, hyx, hle⟩ := hex
    have hr : 0 < ‖y - xbar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    set d := ‖y - xbar‖⁻¹ • (y - xbar) with hd
    have hdD : d ∈ D := ⟨y, hy, hyx, rfl⟩
    have hyeq : xbar + ‖y - xbar‖ • d = y := by
      rw [hd, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    simp only [saaObj] at hle
    have hle' : ∑ j ∈ Finset.range N, h y (ω j s) ≤ ∑ j ∈ Finset.range N, h xbar (ω j s) := by
      have hNi : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
      exact le_of_mul_le_mul_left hle hNi
    have hsum_le : ∑ j ∈ Finset.range N, SAARate.SharpLD.eta h xbar d (ω j s) ≤ 0 := by
      calc ∑ j ∈ Finset.range N, SAARate.SharpLD.eta h xbar d (ω j s)
          ≤ ∑ j ∈ Finset.range N, (h (xbar + ‖y - xbar‖ • d) (ω j s) - h xbar (ω j s)) /
              ‖y - xbar‖ :=
            Finset.sum_le_sum (fun j _ => dd_le (hconv _) xbar d hr)
        _ = (∑ j ∈ Finset.range N, h y (ω j s) - ∑ j ∈ Finset.range N, h xbar (ω j s)) /
              ‖y - xbar‖ := by
            rw [hyeq, ← Finset.sum_div, Finset.sum_sub_distrib]
        _ ≤ 0 := by
            have := div_le_div_of_nonneg_right (sub_nonpos.mpr hle') hr.le
            simpa using this
    have hdc := hcover hdD
    rw [mem_iUnion₂] at hdc
    obtain ⟨d', hd', hdd'⟩ := hdc
    rw [Metric.mem_ball, dist_eq_norm] at hdd'
    rw [mem_iUnion₂]
    refine ⟨d', hD'fin.mem_toFinset.mpr hd', ?_⟩
    simp only [mem_setOf_eq]
    have hstep : ∀ j ∈ Finset.range N, G d' (ω j s) ≤
        SAARate.SharpLD.eta h xbar d (ω j s) + c / 2 := by
      intro j _
      rw [← (hsg j).2 d' hd']
      have h1 : SAARate.SharpLD.eta h xbar d' (ω j s) ≤
          SAARate.SharpLD.eta h xbar d (ω j s) + κ * ‖d' - d‖ :=
        dd_lip (hconv (ω j s)) xbar (hsg j).1 d d'
      have h2 : κ * ‖d' - d‖ ≤ c / 2 := by
        rw [norm_sub_rev]
        calc κ * ‖d - d'‖ ≤ κ * (c / (2 * κ)) := by
              exact mul_le_mul_of_nonneg_left hdd'.le hκ.le
          _ = c / 2 := by field_simp
      linarith
    calc ∑ j ∈ Finset.range N, G d' (ω j s)
        ≤ ∑ j ∈ Finset.range N, (SAARate.SharpLD.eta h xbar d (ω j s) + c / 2) :=
          Finset.sum_le_sum hstep
      _ = ∑ j ∈ Finset.range N, SAARate.SharpLD.eta h xbar d (ω j s) + N * (c / 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ N * (c / 2) := by linarith
  calc Q Ev = Q (Ev ∩ goodS) := (measure_inter_conull hgood).symm
    _ ≤ Q (⋃ d ∈ T, {s | ∑ j ∈ Finset.range N, G d (ω j s) ≤ N * (c / 2)}) :=
        measure_mono hincl
    _ ≤ ∑ d ∈ T, Q {s | ∑ j ∈ Finset.range N, G d (ω j s) ≤ N * (c / 2)} :=
        measure_biUnion_finset_le T _
    _ ≤ ∑ d ∈ T, ENNReal.ofReal (Real.exp (-(c ^ 2 / (8 * κ ^ 2)) * N)) := by
        refine Finset.sum_le_sum (fun d hdT => ?_)
        have hdD : d ∈ D := hD'D (hD'fin.mem_toFinset.mp hdT)
        obtain ⟨hGm, hGb, _, hGmean⟩ := hG d hdD
        exact hoeff P Q ω hmeas hind hmap (G d) hGm hκ hc hGb hGmean N
    _ = ENNReal.ofReal (T.card * Real.exp (-(c ^ 2 / (8 * κ ^ 2)) * N)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (-(c ^ 2 / (8 * κ ^ 2) - ε) * N)) := by
        apply ENNReal.ofReal_le_ofReal
        have : Real.exp (-(c ^ 2 / (8 * κ ^ 2) - ε) * N) =
            Real.exp (ε * N) * Real.exp (-(c ^ 2 / (8 * κ ^ 2)) * N) := by
          rw [← Real.exp_add]; ring_nf
        rw [this]
        exact mul_le_mul_of_nonneg_right hKN (Real.exp_pos _).le
