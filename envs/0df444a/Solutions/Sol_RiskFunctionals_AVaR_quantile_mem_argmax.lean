-- Prove2me | solution 1 for RiskFunctionals.AVaR.quantile_mem_argmax
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:08:46.201901+00:00
-- url     : https://prove2.me/submissions/30ee6b0d-208d-4d71-bd7b-df6a06044716

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk
open RiskFunctionals.AVaR

open MeasureTheory Filter Topology

theorem g78h_quantile_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (p u : ℝ)
    (hp : 0 < p) (hfin : ∃ v : ℝ, p ≤ distributionFunction μ v) :
    quantileFunction μ p ≤ u ↔ p ≤ distributionFunction μ u := by
  have hF : ∀ v, distributionFunction μ v = ProbabilityTheory.cdf μ v := fun v =>
    (ProbabilityTheory.cdf_eq_real μ v).symm
  set S := {u : ℝ | p ≤ distributionFunction μ u} with hS
  have hne : S.Nonempty := hfin
  have hbdd : BddBelow S := by
    have h := (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds hp)
    obtain ⟨L, hL⟩ := Filter.eventually_atBot.1 h
    refine ⟨L, fun v hv => ?_⟩
    by_contra hlt
    have := hL v (le_of_lt (lt_of_not_ge hlt))
    have hv' : p ≤ distributionFunction μ v := hv
    rw [hF] at hv'
    linarith
  have hmono : Monotone (distributionFunction μ) := fun a b hab => by
    rw [hF, hF]; exact (ProbabilityTheory.cdf μ).mono hab
  constructor
  · intro hq
    have hQ : p ≤ distributionFunction μ (quantileFunction μ p) := by
      have hev : ∀ᶠ v in nhdsWithin (quantileFunction μ p) (Set.Ioi (quantileFunction μ p)),
          p ≤ ProbabilityTheory.cdf μ v := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        obtain ⟨w, hwS, hwv⟩ := exists_lt_of_csInf_lt hne hv
        have : p ≤ distributionFunction μ w := hwS
        rw [← hF]; exact this.trans (hmono hwv.le)
      have ht : Filter.Tendsto (ProbabilityTheory.cdf μ)
          (nhdsWithin (quantileFunction μ p) (Set.Ioi (quantileFunction μ p)))
          (nhds (ProbabilityTheory.cdf μ (quantileFunction μ p))) :=
        ((ProbabilityTheory.cdf μ).right_continuous _).tendsto.mono_left
          (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hF]
      exact ge_of_tendsto ht hev
    exact hQ.trans (hmono hq)
  · intro hu
    exact csInf_le hbdd hu

theorem g78h_alpha_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (α : ℝ) (hα₀ : 0 < α)
    (hα₁ : α ≤ 1) (hfin : ∃ u : ℝ, α ≤ distributionFunction (P.map Y) u) :
    alphaPlus (P.map Y) α =
        distributionFunction (P.map Y) (quantileFunction (P.map Y) α) ∧
    Tendsto (fun h : ℝ => distributionFunction (P.map Y) (quantileFunction (P.map Y) α - h))
        (𝓝[>] 0) (𝓝 (alphaMinus (P.map Y) α)) ∧
    alphaMinus (P.map Y) α ≤ α ∧ α ≤ alphaPlus (P.map Y) α ∧
    P.real {ω | Y ω ≤ quantileFunction (P.map Y) α} = alphaPlus (P.map Y) α ∧
    P.real {ω | Y ω < quantileFunction (P.map Y) α} = alphaMinus (P.map Y) α := by
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set μ := P.map Y with hμ
  set q := quantileFunction μ α with hq
  have hle : ∀ u, q ≤ u ↔ α ≤ distributionFunction μ u :=
    fun u => g78h_quantile_le_iff μ α u hα₀ hfin
  have hG : distributionFunction μ = ProbabilityTheory.cdf μ := by
    funext v; exact (ProbabilityTheory.cdf_eq_real μ v).symm
  have hmono : Monotone (distributionFunction μ) := by
    rw [hG]; exact (ProbabilityTheory.cdf μ).mono
  -- alphaPlus
  have hplus : alphaPlus μ α = distributionFunction μ q := by
    unfold alphaPlus
    have hset : {u : ℝ | α ≤ distributionFunction μ u} = Set.Ici q := by
      ext u; simp [hle u]
    rw [hset]
    refine IsLeast.csInf_eq ⟨⟨q, Set.mem_Ici.2 le_rfl, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hmono hu
  -- alphaMinus
  have hminus_set : {u : ℝ | distributionFunction μ u < α} = Set.Iio q := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_Iio]
    rw [← not_le, ← not_le, hle u]
  have hminus : alphaMinus μ α = Function.leftLim (distributionFunction μ) q := by
    unfold alphaMinus
    rw [hminus_set, hmono.leftLim_eq_sSup]
  have hIio : μ.real (Set.Iio q) = Function.leftLim (distributionFunction μ) q := by
    have h1 := (ProbabilityTheory.cdf μ).measure_Iio (ProbabilityTheory.tendsto_cdf_atBot μ) q
    rw [ProbabilityTheory.measure_cdf] at h1
    rw [measureReal_def, h1, hG, sub_zero, ENNReal.toReal_ofReal]
    have := (ProbabilityTheory.cdf μ).mono.leftLim_le (le_refl q)
    exact le_trans (ProbabilityTheory.cdf_nonneg μ (q - 1))
      ((ProbabilityTheory.cdf μ).mono.le_leftLim (by linarith : q - 1 < q))
  refine ⟨hplus, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hminus]
    have ht := hmono.tendsto_leftLim q
    refine ht.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun h : ℝ => q - h) (𝓝 0) (𝓝 (q - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Set.mem_Iio]
      have : (0 : ℝ) < h := hh
      linarith
  · unfold alphaMinus
    refine Real.sSup_le ?_ hα₀.le
    rintro _ ⟨u, hu, rfl⟩
    exact le_of_lt hu
  · rw [hplus]; exact (hle q).1 le_rfl
  · rw [hplus]
    show P.real (Y ⁻¹' Set.Iic q) = μ.real (Set.Iic q)
    rw [hμ, map_measureReal_apply hY measurableSet_Iic]
  · rw [hminus, ← hIio]
    show P.real (Y ⁻¹' Set.Iio q) = μ.real (Set.Iio q)
    rw [hμ, map_measureReal_apply hY measurableSet_Iio]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hfin : ∃ u : ℝ, α ≤ distributionFunction (P.map Y) u) :
    ∀ x : ℝ, x - (1 / α) * ∫ ω, -min (Y ω - x) 0 ∂P ≤
      quantileFunction (P.map Y) α
        - (1 / α) * ∫ ω, -min (Y ω - quantileFunction (P.map Y) α) 0 ∂P := by
  intro x
  obtain ⟨-, -, hmin, hplus, hle, hlt⟩ := g78h_alpha_bounds P Y hY α hα₀ hα₁ hfin
  set q := quantileFunction (P.map Y) α with hq
  have hPle : α ≤ P.real {ω | Y ω ≤ q} := by rw [hle]; exact hplus
  have hPlt : P.real {ω | Y ω < q} ≤ α := by rw [hlt]; exact hmin
  have hint : ∀ t : ℝ, Integrable (fun ω => -min (Y ω - t) 0) P := by
    intro t
    have : Integrable (fun ω => Y ω - t) P := hYi.sub (integrable_const t)
    exact (this.inf (integrable_const 0)).neg
  have hmeas1 : MeasurableSet {ω | Y ω ≤ q} := measurableSet_le hY measurable_const
  have hmeas2 : MeasurableSet {ω | Y ω < q} := measurableSet_lt hY measurable_const
  have hind1 : Integrable (Set.indicator {ω | Y ω ≤ q} (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hmeas1
  have hind2 : Integrable (Set.indicator {ω | Y ω < q} (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hmeas2
  rcases le_or_gt q x with hxq | hxq
  · have key : ∫ ω, -min (Y ω - q) 0 ∂P + (x - q) * P.real {ω | Y ω ≤ q} ≤
        ∫ ω, -min (Y ω - x) 0 ∂P := by
      rw [← integral_indicator_one hmeas1, ← integral_const_mul,
        ← integral_add (hint q) (hind1.const_mul _)]
      refine integral_mono ((hint q).add (hind1.const_mul _)) (hint x) (fun ω => ?_)
      simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
      split_ifs with h
      · have h1 : min (Y ω - q) 0 = Y ω - q := min_eq_left (by linarith)
        have h2 : min (Y ω - x) 0 = Y ω - x := min_eq_left (by linarith)
        rw [h1, h2]; linarith
      · have h1 : min (Y ω - q) 0 = 0 := min_eq_right (by push Not at h; linarith)
        rw [h1]
        have := min_le_right (Y ω - x) 0
        linarith
    have e : (1 / α) * ∫ ω, -min (Y ω - x) 0 ∂P ≥
        (1 / α) * ∫ ω, -min (Y ω - q) 0 ∂P + (1 / α) * ((x - q) * P.real {ω | Y ω ≤ q}) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left key (by positivity)
    have e2 : (x - q) ≤ (1 / α) * ((x - q) * P.real {ω | Y ω ≤ q}) := by
      rw [show (1 / α) * ((x - q) * P.real {ω | Y ω ≤ q}) =
        (x - q) * (P.real {ω | Y ω ≤ q} / α) by field_simp]
      have : 1 ≤ P.real {ω | Y ω ≤ q} / α := by rw [le_div_iff₀ hα₀]; linarith
      nlinarith
    linarith
  · have key : ∫ ω, -min (Y ω - q) 0 ∂P + (-(q - x)) * P.real {ω | Y ω < q} ≤
        ∫ ω, -min (Y ω - x) 0 ∂P := by
      rw [← integral_indicator_one hmeas2, ← integral_const_mul,
        ← integral_add (hint q) (hind2.const_mul _)]
      refine integral_mono ((hint q).add (hind2.const_mul _)) (hint x) (fun ω => ?_)
      simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
      split_ifs with h
      · have h1 : min (Y ω - q) 0 = Y ω - q := min_eq_left (by linarith)
        rw [h1]
        have := min_le_left (Y ω - x) 0
        linarith
      · have h1 : min (Y ω - q) 0 = 0 := min_eq_right (by push Not at h; linarith)
        have h2 : min (Y ω - x) 0 = 0 := min_eq_right (by push Not at h; linarith)
        rw [h1, h2]; simp
    have e : (1 / α) * ∫ ω, -min (Y ω - x) 0 ∂P ≥
        (1 / α) * ∫ ω, -min (Y ω - q) 0 ∂P + (1 / α) * ((-(q - x)) * P.real {ω | Y ω < q}) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left key (by positivity)
    have e2 : -(q - x) ≤ (1 / α) * ((-(q - x)) * P.real {ω | Y ω < q}) := by
      rw [show (1 / α) * ((-(q - x)) * P.real {ω | Y ω < q}) =
        (-(q - x)) * (P.real {ω | Y ω < q} / α) by field_simp]
      have : P.real {ω | Y ω < q} / α ≤ 1 := by rw [div_le_iff₀ hα₀]; linarith
      nlinarith
    linarith
