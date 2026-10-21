-- Prove2me | solution 1 for PuhaWardFluid.Limit.lemma_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:17:24.38454+00:00
-- url     : https://prove2.me/submissions/fc833ab7-2a34-4401-8cca-07be2a415bcb

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_FluidModel

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace PuhaWardFluid.Limit.L2iii

lemma tentv_bounds (a : ℝ) (n : ℕ) (z : ℝ≥0) :
    0 ≤ max 0 (1 - ((n : ℝ) + 1) * |(z : ℝ) - a|) ∧
      max 0 (1 - ((n : ℝ) + 1) * |(z : ℝ) - a|) ≤ 1 := by
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  have : 0 ≤ ((n : ℝ) + 1) * |(z : ℝ) - a| := by positivity
  linarith

/-- The tent function `z ↦ (1 − (n+1)|z − a|)^+`, a bounded continuous approximation of `1_{a}`. -/
noncomputable def tent (a : ℝ) (n : ℕ) : ℝ≥0 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => max 0 (1 - ((n : ℝ) + 1) * |(z : ℝ) - a|), by fun_prop⟩ 1 (by
      intro x y
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      have hx := tentv_bounds a n x
      have hy := tentv_bounds a n y
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])

lemma tent_apply (a : ℝ) (n : ℕ) (z : ℝ≥0) :
    tent a n z = max 0 (1 - ((n : ℝ) + 1) * |(z : ℝ) - a|) := rfl

lemma tent_bounds (a : ℝ) (n : ℕ) (z : ℝ≥0) : 0 ≤ tent a n z ∧ tent a n z ≤ 1 :=
  tentv_bounds a n z

lemma tent_abs_le (a : ℝ) (n : ℕ) (z : ℝ≥0) : |tent a n z| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [tent_bounds a n z]

lemma tent_self (a : ℝ) (n : ℕ) (z : ℝ≥0) (hz : (z : ℝ) = a) : tent a n z = 1 := by
  rw [tent_apply, hz]; simp

lemma tent_tendsto (a : ℝ) (z : ℝ≥0) (hz : (z : ℝ) ≠ a) :
    Tendsto (fun n => tent a n z) atTop (𝓝 0) := by
  have hpos : 0 < |(z : ℝ) - a| := abs_pos.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / |(z : ℝ) - a|)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [tent_apply]
  symm
  apply max_eq_left
  have h1 : 1 < (N : ℝ) * |(z : ℝ) - a| := by
    rw [div_lt_iff₀ hpos] at hN; linarith
  have h2 : (N : ℝ) ≤ (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  nlinarith

lemma cdf_props (g : ℝ → ℝ≥0) (hg : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1) :
    Monotone (cdf g) ∧ ∀ r, 0 ≤ cdf g r ∧ cdf g r ≤ 1 := by
  have hle : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≤ 1 := fun r =>
    (setLIntegral_le_lintegral _ _).trans hg
  have hfin : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≠ ⊤ := fun r =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hle r)
  refine ⟨fun a b hab => ?_, fun r => ⟨ENNReal.toReal_nonneg, ?_⟩⟩
  · unfold cdf
    exact ENNReal.toReal_mono (hfin b) (lintegral_mono_set (Set.Icc_subset_Icc le_rfl hab))
  · unfold cdf
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hle r)
    simpa using this

variable {H : ℝ≥0∞}

lemma lim_pair (μ : FiniteMeasure (Iv H)) (x0 : Iv H) :
    Tendsto (fun n => pair (fun x => tent ((x0 : ℝ≥0) : ℝ) n x.toNNReal) μ) atTop
      (𝓝 ((μ : Measure (Iv H)) {x0}).toReal) := by
  unfold pair
  simp only [Real.toNNReal_coe]
  have hlim := tendsto_integral_of_dominated_convergence (μ := (μ : Measure (Iv H)))
    (F := fun n (z : Iv H) => tent ((x0 : ℝ≥0) : ℝ) n (z : ℝ≥0))
    (f := ({x0} : Set (Iv H)).indicator (fun _ => (1 : ℝ)))
    (fun _ => 1)
    (fun n => ((tent _ n).continuous.comp continuous_subtype_val).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact tent_abs_le _ _ _)
    (Eventually.of_forall fun z => by
      by_cases hz : z = x0
      · subst hz
        simp only [Set.indicator_of_mem (Set.mem_singleton _)]
        exact tendsto_const_nhds.congr fun n => (tent_self _ _ _ rfl).symm
      · rw [Set.indicator_of_notMem (by simpa using hz)]
        apply tent_tendsto
        intro h
        exact hz (Subtype.ext (NNReal.coe_injective h)))
  rw [integral_indicator_const _ (measurableSet_singleton x0)] at hlim
  simpa [measureReal_def] using hlim

lemma lim_pair0 (μ0 : FiniteMeasure (Iv H)) (hnc : NoCharge μ0) (t : ℝ≥0) (a : ℝ)
    (G : ℝ → ℝ) (hGm : Monotone G) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1) :
    Tendsto (fun n => pair (fun x => tent a n (x.toNNReal + t) * (1 - G (x + t)) / (1 - G x)) μ0)
      atTop (𝓝 0) := by
  unfold pair
  simp only [Real.toNNReal_coe]
  have hGmeas : Measurable G := hGm.measurable
  have hcoe : Measurable (fun z : Iv H => ((z : ℝ≥0) : ℝ)) :=
    (NNReal.continuous_coe.comp continuous_subtype_val).measurable
  have hratio : ∀ r s : ℝ, r ≤ s → |(1 - G s) / (1 - G r)| ≤ 1 := by
    intro r s hrs
    rcases eq_or_ne (1 - G r) 0 with h0 | h0
    · simp [h0]
    · have hpos : 0 < 1 - G r := lt_of_le_of_ne (by linarith [(hG r).2]) h0.symm
      rw [abs_le, le_div_iff₀ hpos, div_le_iff₀ hpos]
      constructor <;> nlinarith [hGm hrs, (hG s).2, (hG s).1, (hG r).1]
  have hnull : ∀ᵐ (z : Iv H) ∂(μ0 : Measure (Iv H)), ((z : ℝ≥0) : ℝ) + t ≠ a := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    by_cases hex : ∃ z0 : Iv H, ((z0 : ℝ≥0) : ℝ) + t = a
    · obtain ⟨z0, hz0⟩ := hex
      refine measure_mono_null (t := ({z0} : Set (Iv H)))
        (fun (z : Iv H) (hz : ((z : ℝ≥0) : ℝ) + t = a) => ?_) (hnc z0)
      simp only [Set.mem_singleton_iff]
      apply Subtype.ext; apply NNReal.coe_injective
      linarith
    · push_neg at hex
      have : {z : Iv H | ((z : ℝ≥0) : ℝ) + t = a} = ∅ := by
        ext z; simp [hex z]
      rw [this]; simp
  have hlim := tendsto_integral_of_dominated_convergence (μ := (μ0 : Measure (Iv H)))
    (F := fun n (z : Iv H) => tent a n ((z : ℝ≥0) + t) * (1 - G (((z : ℝ≥0) : ℝ) + t)) /
      (1 - G ((z : ℝ≥0) : ℝ)))
    (f := fun _ => 0)
    (fun _ => 1)
    (fun n => by
      refine Measurable.aestronglyMeasurable ?_
      refine Measurable.div (Measurable.mul ?_ ?_) ?_
      · exact ((tent a n).continuous.comp
          ((continuous_subtype_val).add continuous_const)).measurable
      · exact measurable_const.sub (hGmeas.comp (hcoe.add measurable_const))
      · exact measurable_const.sub (hGmeas.comp hcoe))
    (integrable_const 1)
    (fun n => Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul]
      have h1 := tent_abs_le a n ((z : ℝ≥0) + t)
      have h2 := hratio ((z : ℝ≥0) : ℝ) (((z : ℝ≥0) : ℝ) + t) (by simp)
      have h3 : 0 ≤ |(1 - G (((z : ℝ≥0) : ℝ) + t)) / (1 - G ((z : ℝ≥0) : ℝ))| := abs_nonneg _
      nlinarith [abs_nonneg (tent a n ((z : ℝ≥0) + t))])
    (by
      filter_upwards [hnull] with z hz
      have h0 : Tendsto (fun n => tent a n ((z : ℝ≥0) + t)) atTop (𝓝 0) :=
        tent_tendsto a _ (by simpa using hz)
      have := (h0.mul_const (1 - G (((z : ℝ≥0) : ℝ) + t))).div_const (1 - G ((z : ℝ≥0) : ℝ))
      simpa using this)
  simpa using hlim

lemma extPath_eq (x : ℝ≥0 → ℝ) (hx0 : x 0 = 0) : extPath x = fun s => x s.toNNReal := by
  funext s
  unfold extPath
  split_ifs with h
  · rw [Real.toNNReal_of_nonpos h.le, hx0]
  · rfl

lemma lim_stj (Kp : ℝ≥0 → ℝ) (hK : Continuous Kp) (hK0 : Kp 0 = 0) (t : ℝ≥0) (a : ℝ)
    (G : ℝ → ℝ) (hGm : Monotone G) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1) :
    Tendsto (fun n => stieltjesInt Kp (fun u => tent a n (t - u.toNNReal) * (1 - G ((t : ℝ) - u))) t)
      atTop (𝓝 0) := by
  unfold stieltjesInt
  split_ifs with h
  · set m := h.stieltjesFunction.measure with hm
    have hcont : Continuous (extPath Kp) := by
      rw [extPath_eq Kp hK0]; exact hK.comp continuous_real_toNNReal
    have hsf : ∀ s, h.stieltjesFunction s = extPath Kp s := fun s => by
      rw [Monotone.stieltjesFunction_eq]
      exact (hcont.continuousAt.continuousWithinAt).rightLim_eq
    have hsfc : Continuous h.stieltjesFunction := by
      have : (h.stieltjesFunction : ℝ → ℝ) = extPath Kp := funext hsf
      rw [this]; exact hcont
    have hsing : ∀ u, m {u} = 0 := fun u => by
      rw [hm, StieltjesFunction.measure_singleton,
        (hsfc.continuousAt.continuousWithinAt).leftLim_eq]
      simp
    have : IsFiniteMeasure (m.restrict (Set.Icc 0 (t : ℝ))) := by
      constructor
      rw [Measure.restrict_apply_univ, hm, StieltjesFunction.measure_Icc]
      exact ENNReal.ofReal_lt_top
    have hGmeas : Measurable G := hGm.measurable
    have hlim := tendsto_integral_of_dominated_convergence
      (μ := m.restrict (Set.Icc 0 (t : ℝ)))
      (F := fun n (u : ℝ) => tent a n (t - u.toNNReal) * (1 - G ((t : ℝ) - u)))
      (f := fun _ => 0)
      (fun _ => 1)
      (fun n => by
        refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
        · exact ((tent a n).continuous.comp
            (continuous_const.sub continuous_real_toNNReal)).measurable
        · exact measurable_const.sub (hGmeas.comp (measurable_const.sub measurable_id)))
      (integrable_const 1)
      (fun n => Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := tent_abs_le a n (t - u.toNNReal)
        have h2 : |1 - G ((t : ℝ) - u)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [hG ((t : ℝ) - u)]
        nlinarith [abs_nonneg (tent a n (t - u.toNNReal)), abs_nonneg (1 - G ((t : ℝ) - u))])
      (by
        have hne : ∀ᵐ u ∂(m.restrict (Set.Icc 0 (t : ℝ))), u ≠ (t : ℝ) - a := by
          rw [ae_iff]
          simp only [ne_eq, not_not]
          rw [Measure.restrict_apply' measurableSet_Icc]
          exact measure_mono_null (fun u hu => by simpa using hu.1) (hsing ((t : ℝ) - a))
        filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with u hu hmem
        have hcoe : ((t - u.toNNReal : ℝ≥0) : ℝ) = (t : ℝ) - u := by
          rw [NNReal.coe_sub (by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hmem.1]; exact hmem.2),
            Real.coe_toNNReal _ hmem.1]
        have h0 : Tendsto (fun n => tent a n (t - u.toNNReal)) atTop (𝓝 0) :=
          tent_tendsto a _ (by rw [hcoe]; intro h'; apply hu; linarith)
        simpa using h0.mul_const (1 - G ((t : ℝ) - u)))
    simpa using hlim
  · exact tendsto_const_nhds

/-- The core argument: equation (46)/(47) with continuous integrator and atomless initial measure
forces the measure at time `t` to be atomless. -/
lemma core (μt μ0 : FiniteMeasure (Iv H)) (hnc : NoCharge μ0) (G : ℝ → ℝ) (hGm : Monotone G)
    (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1) (Kp : ℝ≥0 → ℝ) (hK : Continuous Kp) (hK0 : Kp 0 = 0)
    (t : ℝ≥0)
    (heq : ∀ f : ℝ≥0 →ᵇ ℝ, pair (fun x => f x.toNNReal) μt =
      pair (fun x => f (x.toNNReal + t) * (1 - G (x + t)) / (1 - G x)) μ0 +
        stieltjesInt Kp (fun u => f (t - u.toNNReal) * (1 - G ((t : ℝ) - u))) t) :
    NoCharge μt := by
  intro x0
  set a : ℝ := ((x0 : ℝ≥0) : ℝ)
  have h1 := lim_pair μt x0
  have h2 := (lim_pair0 μ0 hnc t a G hGm hG).add (lim_stj Kp hK hK0 t a G hGm hG)
  simp only [add_zero] at h2
  have h3 : ((μt : Measure (Iv H)) {x0}).toReal = 0 := by
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    exact (heq (tent a n)).symm
  rcases (ENNReal.toReal_eq_zero_iff _).1 h3 with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

end PuhaWardFluid.Limit.L2iii

open PuhaWardFluid.Limit PuhaWardFluid.Limit.L2iii

theorem solution {J : ℕ} (L : ClassLaws J) (E : ℝ≥0 → Fin J → ℝ) (y : ℝ≥0 → Xsp L)
    (hsol : IsFluidSol L E y) :
    ((∀ j, Continuous fun t => flK L y t j) → (∀ j, NoCharge (flNu L y 0 j)) →
        ∀ (t : ℝ≥0) j, NoCharge (flNu L y t j)) ∧
    (Continuous E → (∀ j, NoCharge (flEta L y 0 j)) →
        ∀ (t : ℝ≥0) j, NoCharge (flEta L y t j)) := by
  obtain ⟨hE, -, -, -, h46, h47⟩ := hsol
  refine ⟨fun hK hnc t j => ?_, fun hEc hnc t j => ?_⟩
  · have hs := cdf_props (L.gs j) (le_of_eq (L.gs_total j))
    refine core _ _ (hnc j) (L.Gs j) hs.1 hs.2 (fun s => flK L y s j) (hK j) ?_ t (h46 j · t)
    simp only [flK, flD, flDInt, NNReal.coe_zero, Set.Icc_self]
    rw [Measure.restrict_singleton]
    simp
  · have hs := cdf_props (L.gr j) (L.gr_total j)
    refine core _ _ (hnc j) (L.Gr j) hs.1 hs.2 (fun s => E s j)
      ((continuous_apply j).comp hEc) ?_ t (h47 j · t)
    have := hE.2.2
    simp [this]
