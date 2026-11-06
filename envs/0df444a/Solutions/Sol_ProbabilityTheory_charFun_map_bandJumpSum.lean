-- Prove2me | solution 1 for ProbabilityTheory.charFun_map_bandJumpSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:34:25.759601+00:00
-- url     : https://prove2.me/submissions/b9dd78b8-c779-4689-bf3f-6a489a9b4fa1

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Theorems.Thm_ProbabilityTheory_ae_finite_support_pieceSum
import Theorems.Thm_ProbabilityTheory_charFun_partial_largeJumpSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}


private lemma ae_finite_support_pieceSum_largeBand [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {s t : ℝ} :
    ∀ᵐ ω ∂μ, {k | pieceSum K X
        ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω ≠ 0}.Finite := by
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t)
      (hν.measure_setOf_abs_ge_lt_top one_pos)
  exact ae_finite_support_pieceSum hd (measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)) hbandfin
    fun p hp => Set.indicator_of_notMem hp _

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => ∑' k,
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) *
          ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)
  have hbandFnmeas : Measurable ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2) :=
    measurable_snd.indicator hbandmeas
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t)
      (hν.measure_setOf_abs_ge_lt_top one_pos)
  have hgmeas : Measurable fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) := Complex.measurable_exp.comp ((Complex.measurable_ofReal.const_mul (↑ξ)).mul_const Complex.I)
  have hgcont : Continuous fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) := by fun_prop
  have hf'eq : (fun x : ℝ × ℝ =>
        Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1)
      = (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 := by
    funext x
    by_cases hx : x ∈ Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero,
        mul_zero, zero_mul, Complex.exp_zero, sub_self]
  have hbound2 : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖ ≤ 2 := fun x => by
    calc ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖
        ≤ ‖Complex.exp (↑ξ * ↑x.2 * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (↑ξ * ↑x.2 * Complex.I : ℂ) = ↑(ξ * x.2) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hintegrand_meas : Measurable fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 := (Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp measurable_snd).const_mul (↑ξ)).mul_const
        Complex.I)).sub measurable_const
  have hband_intOn : IntegrableOn (fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1) (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) (volume.prod ν) :=
    IntegrableOn.of_bound hbandfin hintegrand_meas.aestronglyMeasurable 2
      (Filter.Eventually.of_forall hbound2)
  have hf'_int : Integrable (fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) (volume.prod ν) := by
    rw [hf'eq]; exact (integrable_indicator_iff hbandmeas).mpr hband_intOn
  have hFpiece_hassum : HasSum (fun k => ∫ x in prmPiece (volume.prod ν) k,
        (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))
      (∫ x, (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν)) := by
    have h := hasSum_integral_iUnion (μ := volume.prod ν)
      (f := fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1)
      (fun k => measurableSet_prmPiece (m := volume.prod ν))
      (pairwise_disjoint_prmPiece (m := volume.prod ν))
      (by rw [iUnion_prmPiece]; exact hf'_int.integrableOn)
    rwa [iUnion_prmPiece, setIntegral_univ] at h
  have hfinal : (∫ x, (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))
      = ((t - s : ℝ) : ℂ) * ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν := by
    rw [hf'eq, integral_indicator hbandmeas,
      setIntegral_prod (fun z : ℝ × ℝ => Complex.exp (↑ξ * ↑z.2 * Complex.I) - 1) hband_intOn]
    dsimp only
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst), Complex.real_smul]
    refine congrArg (fun z => ((↑(t - s) : ℂ)) * z) ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [mul_comm (↑ξ : ℂ) (↑y : ℂ)]
  have hmeas_sum : Measurable fun ω => ∑' k, pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω :=
    Measurable.tsum fun k =>
      measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hbandFnmeas
  have hFmeas : ∀ n, Measurable fun ω => Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I) := fun n =>
    hgmeas.comp (Finset.measurable_sum _ fun k _ =>
      measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hbandFnmeas)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := fun n => by
    filter_upwards with ω
    rw [show (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
          * Complex.I : ℂ)
        = ↑(ξ * ∑ k ∈ Finset.range (n + 1),
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
          * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I)) atTop
      (𝓝 (Complex.exp (↑ξ * ↑(∑' k,
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I))) := by
    filter_upwards [ae_finite_support_pieceSum_largeBand hd hν (s := s) (t := t)] with ω hωfin
    have hsummable : Summable (fun k =>
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) :=
      summable_of_ne_finset_zero (s := hωfin.toFinset) fun k hk => by
        by_contra hne
        exact hk (hωfin.mem_toFinset.mpr hne)
    have htends : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) atTop
        (𝓝 (∑' k,
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)) :=
      hsummable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact (hgcont.tendsto _).comp htends
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  simp_rw [charFun_partial_largeJumpSum hd hbandFnmeas ξ] at hdct
  have hprodexp : ∀ n, ∏ k ∈ Finset.range (n + 1),
        Complex.exp (∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))
      = Complex.exp (∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
              (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν)) :=
    fun n => (Complex.exp_sum _ _).symm
  simp_rw [hprodexp] at hdct
  have hprodlim : Tendsto (fun n => Complex.exp (∑ k ∈ Finset.range (n + 1), ∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))) atTop
      (𝓝 (Complex.exp (∫ x, (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν)))) :=
    (Complex.continuous_exp.tendsto _).comp
      (hFpiece_hassum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have hval := tendsto_nhds_unique hdct hprodlim
  rw [charFun_apply_real, integral_map hmeas_sum.aemeasurable (by fun_prop), hval, hfinal]
