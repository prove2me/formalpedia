-- Prove2me | solution 1 for ProbabilityTheory.charFunDual_poissonRandomMeasureVec
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:21:02.963028+00:00
-- url     : https://prove2.me/submissions/04f13062-bdba-455f-8182-fc5c4ac3f1b7

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_ProbabilityTheory_charFunDual_prmPartialCountVec
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

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal) L
      = ∏ i, Complex.exp (↑(m (A i)).toReal * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  have mPn : ∀ n, Measurable fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ) := fun n =>
    measurable_pi_lambda _ fun i => measurable_from_top.comp
      (measurable_prmPartialCount hd.measurable_count hd.measurable_point (hA i) n)
  have mN : Measurable fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal :=
    measurable_pi_lambda _ fun i =>
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
        (hA i)).ennreal_toReal
  have hFmeas : ∀ n, Measurable fun ω =>
      Complex.exp (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I) := fun n =>
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (L.continuous.measurable.comp (mPn n))).mul_const I)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp
      (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := by
    intro n; filter_upwards with ω
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hae : ∀ᵐ ω ∂μ, ∀ i, poissonRandomMeasure K X ω (A i) < ⊤ := by
    rw [ae_all_iff]
    exact fun i => ae_poissonRandomMeasure_apply_lt_top hd (hA i) (hfin i)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Complex.exp
      (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I)) atTop
      (𝓝 (Complex.exp (↑(L fun i => (poissonRandomMeasure K X ω (A i)).toReal) * I))) := by
    filter_upwards [hae] with ω hω
    have hc : Continuous fun p : ι → ℝ => Complex.exp (↑(L p) * I) := by fun_prop
    exact (hc.tendsto _).comp
      (tendsto_pi_nhds.mpr fun i => tendsto_natCast_prmPartialCount (hA i) ω (hω i))
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1 : ℝ)) (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have key : ∀ n, ∫ ω, Complex.exp
        (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I) ∂μ
      = charFunDual (μ.map fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ)) L := fun n => by
    rw [charFunDual_apply, integral_map (mPn n).aemeasurable (by fun_prop)]
  have keyN : ∫ ω, Complex.exp
        (↑(L fun i => (poissonRandomMeasure K X ω (A i)).toReal) * I) ∂μ
      = charFunDual (μ.map fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal) L := by
    rw [charFunDual_apply, integral_map mN.aemeasurable (by fun_prop)]
  simp_rw [key, charFunDual_prmPartialCountVec hd hA hdisj] at hdct
  rw [keyN] at hdct
  have hrate : Tendsto (fun n => ∏ i,
      Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A i)).toReal)
        * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1))) atTop
      (𝓝 (∏ i, Complex.exp (↑(m (A i)).toReal * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)))) := by
    refine tendsto_finsetProd _ fun i _ => ?_
    exact ((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
        Complex.exp (↑r * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount (hA i) (hfin i))
  exact tendsto_nhds_unique hdct hrate
