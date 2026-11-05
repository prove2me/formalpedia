-- Prove2me | solution 1 for ProbabilityTheory.charFun_natCast_poissonRandomMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:21:07.799498+00:00
-- url     : https://prove2.me/submissions/d9f523bd-8240-4185-8101-583702240eeb

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_ProbabilityTheory_map_prmPartialCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Complex ProbabilityTheory
open scoped ENNReal NNReal Topology
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E]
  {μ : Measure Ω} {A B : Set E} {ω : Ω}
private lemma measurable_prmPartialCount (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) (n : ℕ) :
    Measurable (prmPartialCount K X A n) :=
  Finset.measurable_sum _ fun k _ => measurable_thinnedCount (hK k) (hX k) hA

private lemma charFun_natCast_prmPartialCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (n : ℕ) (ξ : ℝ) :
    charFun (μ.map fun ω => (prmPartialCount K X A n ω : ℝ)) ξ
      = Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
          * (Complex.exp (↑ξ * I) - 1)) := by
  have hmeas := measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n
  have hcoe : ((∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal : ℝ≥0) : ℝ)
      = ∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal := by
    rw [NNReal.coe_sum]
    exact Finset.sum_congr rfl fun k _ => ENNReal.coe_toNNReal_eq_toReal _
  rw [show (fun ω => ((prmPartialCount K X A n ω : ℕ) : ℝ))
        = (Nat.cast : ℕ → ℝ) ∘ prmPartialCount K X A n from rfl,
    ← Measure.map_map measurable_from_top hmeas, map_prmPartialCount hd hA n,
    charFun_poissonMeasure_eq, hcoe]

private lemma tendsto_rate_prmPartialCount (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
      atTop (𝓝 (m A).toReal) := by
  have hsum : ∑' k, m (prmPiece m k ∩ A) = m A := tsum_measure_prmPiece_inter hA
  have hHS : HasSum (fun k => (m (prmPiece m k ∩ A)).toReal)
      (∑' k, (m (prmPiece m k ∩ A)).toReal) :=
    ENNReal.hasSum_toReal (by rw [hsum]; exact hfin.ne)
  have hval : (∑' k, (m (prmPiece m k ∩ A)).toReal) = (m A).toReal := by
    rw [← ENNReal.tsum_toReal_eq fun k => (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      measure_prmPiece_lt_top).ne, hsum]
  rw [hval] at hHS
  exact hHS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

private lemma tendsto_natCast_prmPartialCount (hA : MeasurableSet A) (ω : Ω)
    (hω : poissonRandomMeasure K X ω A < ⊤) :
    Tendsto (fun n => (prmPartialCount K X A n ω : ℝ)) atTop
      (𝓝 (poissonRandomMeasure K X ω A).toReal) := by
  have hHS : HasSum (fun k => (thinnedCount K X A k ω : ℝ≥0∞)) (poissonRandomMeasure K X ω A) := by
    rw [poissonRandomMeasure_apply hA]; exact ENNReal.summable.hasSum
  have hcast : ∀ n, ((prmPartialCount K X A n ω : ℕ) : ℝ≥0∞)
      = ∑ i ∈ Finset.range (n + 1), (thinnedCount K X A i ω : ℝ≥0∞) := by
    intro n; rw [prmPartialCount]; exact Nat.cast_sum _ _
  have hpart : Tendsto (fun n => ((prmPartialCount K X A n ω : ℕ) : ℝ≥0∞)) atTop
      (𝓝 (poissonRandomMeasure K X ω A)) := by
    simp_rw [hcast]
    exact hHS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim := (ENNReal.tendsto_toReal hω.ne).comp hpart
  simpa only [Function.comp_def, ENNReal.toReal_natCast] using hlim

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) (ξ : ℝ) :
    charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ
      = Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)) := by
  have hSn_meas : ∀ n, Measurable fun ω => (prmPartialCount K X A n ω : ℝ) := fun n =>
    measurable_from_top.comp
      (measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n)
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have hFmeas : ∀ n, Measurable
      fun ω => Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I) := fun n =>
    Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp (hSn_meas n)).const_mul (↑ξ)).mul_const I)
  have hbound : ∀ n, ∀ᵐ ω ∂μ,
      ‖Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := by
    intro n
    filter_upwards with ω
    have : ‖Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)‖ = 1 := by
      rw [show (↑ξ : ℂ) * ↑(prmPartialCount K X A n ω : ℝ) * I
          = ↑(ξ * (prmPartialCount K X A n ω : ℝ)) * I from by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    exact le_of_eq this
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun n => Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)) atTop
        (𝓝 (Complex.exp (↑ξ * ↑(poissonRandomMeasure K X ω A).toReal * I))) := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfin] with ω hω
    have hc : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * I) := by fun_prop
    exact (hc.tendsto _).comp (tendsto_natCast_prmPartialCount hA ω hω)
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1 : ℝ)) (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have key : ∀ n, ∫ ω, Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I) ∂μ
      = charFun (μ.map fun ω => (prmPartialCount K X A n ω : ℝ)) ξ := fun n => by
    rw [charFun_apply_real, integral_map (hSn_meas n).aemeasurable (by fun_prop)]
  have keyN : ∫ ω, Complex.exp (↑ξ * ↑(poissonRandomMeasure K X ω A).toReal * I) ∂μ
      = charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ := by
    rw [charFun_apply_real, integral_map hN_meas.aemeasurable (by fun_prop)]
  simp_rw [key, charFun_natCast_prmPartialCount hd hA] at hdct
  rw [keyN] at hdct
  have hrate : Tendsto
      (fun n => Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
        * (Complex.exp (↑ξ * I) - 1))) atTop
      (𝓝 (Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)))) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
      Complex.exp (↑r * (Complex.exp (↑ξ * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount hA hfin)
  exact tendsto_nhds_unique hdct hrate
