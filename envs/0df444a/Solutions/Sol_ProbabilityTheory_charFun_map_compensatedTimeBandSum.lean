-- Prove2me | solution 1 for ProbabilityTheory.charFun_map_compensatedTimeBandSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:52:32.677681+00:00
-- url     : https://prove2.me/submissions/f729b334-ffc3-4e1c-9dd3-95836ce12905

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Theorems.Thm_ProbabilityTheory_charFun_partial_compensatedBandSum
import Theorems.Thm_ProbabilityTheory_ae_finite_support_pieceSum
import Theorems.Thm_ProbabilityTheory_integrable_bandFun
import Theorems.Thm_ProbabilityTheory_measurable_bandFun
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure ℝ} [SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1) 1) (hAfin : ν A < ⊤)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (compensatedPoissonSum K X
        ((Set.Ioc s t ×ˢ A).indicator fun p => p.2) ((volume : Measure ℝ).prod ν))) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in A,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  set f : ℝ × ℝ → ℝ := (Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2 with hf_def
  have hbandFnmeas : Measurable f := measurable_bandFun hA s t
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ A) < ⊤ := volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t) hAfin
  have hf1 : Integrable f (volume.prod ν) := integrable_bandFun hA hAsub hAfin s t
  have hf2 : MemLp f 2 (volume.prod ν) := memLp_two_bandFun hA hAsub hAfin s t
  have hgmeas : Measurable fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) := Complex.measurable_exp.comp ((Complex.measurable_ofReal.const_mul (↑ξ)).mul_const Complex.I)
  have hgcont : Continuous fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) := by fun_prop
  have hg'eq : (fun x : ℝ × ℝ =>
        Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
      = (Set.Ioc s t ×ˢ A).indicator
          fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I := by
    funext x
    by_cases hx : x ∈ Set.Ioc s t ×ˢ A
    · rw [hf_def]; simp only [Set.indicator_of_mem hx]
    · rw [hf_def]; simp [Set.indicator_of_notMem hx]
  have hbound2 : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖ ≤ 2 := fun x => by
    calc ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖
        ≤ ‖Complex.exp (↑ξ * ↑x.2 * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (↑ξ * ↑x.2 * Complex.I : ℂ) = ↑(ξ * x.2) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hintegrand_meas : Measurable fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I := by
    have h1 : Measurable fun q : ℝ × ℝ => (↑ξ * ↑q.2 * Complex.I : ℂ) :=
      ((Complex.measurable_ofReal.comp measurable_snd).const_mul (↑ξ)).mul_const Complex.I
    exact ((Complex.measurable_exp.comp h1).sub measurable_const).sub h1
  have hband_intOn : IntegrableOn (fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I)
      (Set.Ioc s t ×ˢ A) (volume.prod ν) := by
    refine IntegrableOn.of_bound hbandfin hintegrand_meas.aestronglyMeasurable (2 + |ξ|) ?_
    refine (ae_restrict_mem hbandmeas).mono fun q hq => ?_
    obtain ⟨h1, h2⟩ := hAsub hq.2
    have habs : |q.2| ≤ 1 := abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩
    have hlin : ‖(↑ξ * ↑q.2 * Complex.I : ℂ)‖ ≤ |ξ| := by
      rw [show (↑ξ * ↑q.2 * Complex.I : ℂ) = ↑(ξ * q.2) * Complex.I from by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc |ξ| * |q.2| ≤ |ξ| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
        _ = |ξ| := mul_one _
    calc ‖Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I‖
        ≤ ‖Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1‖ + ‖(↑ξ * ↑q.2 * Complex.I : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 2 + |ξ| := add_le_add (hbound2 q) hlin
  have hg_int : Integrable (fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I) (volume.prod ν) := by
    rw [hg'eq]; exact (integrable_indicator_iff hbandmeas).mpr hband_intOn
  have hGHasSum : HasSum (fun k => ∫ x in prmPiece (volume.prod ν) k,
        (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I) ∂(volume.prod ν))
      (∫ x, (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
        ∂(volume.prod ν)) := by
    have h := hasSum_integral_iUnion (μ := volume.prod ν)
      (f := fun x : ℝ × ℝ =>
        Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
      (fun k => measurableSet_prmPiece (m := volume.prod ν))
      (pairwise_disjoint_prmPiece (m := volume.prod ν))
      (by rw [iUnion_prmPiece]; exact hg_int.integrableOn)
    rwa [iUnion_prmPiece, setIntegral_univ] at h
  have hfinal : (∫ x, (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
        ∂(volume.prod ν))
      = ((t - s : ℝ) : ℂ)
          * ∫ x in A, (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν := by
    rw [hg'eq, integral_indicator hbandmeas, setIntegral_prod _ hband_intOn]
    dsimp only
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst), Complex.real_smul]
    refine congrArg (fun z => ((↑(t - s) : ℂ)) * z) ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    simp only [mul_comm (↑ξ : ℂ) (↑y : ℂ)]
  have hmeas_sum : AEStronglyMeasurable (compensatedPoissonSum K X f (volume.prod ν)) μ :=
    (memLp_two_compensatedPoissonSum hd hbandFnmeas hf1 hf2).aestronglyMeasurable
  have hFmeas : ∀ n, Measurable fun ω => Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I) := fun n =>
    hgmeas.comp (Finset.measurable_sum _ fun k _ =>
      measurable_compensatedPieceSum hd hbandFnmeas)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I)‖
        ≤ (fun _ : Ω => (1 : ℝ)) ω := fun n => by
    filter_upwards with ω
    rw [show (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I : ℂ)
        = ↑(ξ * ∑ k ∈ Finset.range (n + 1),
          compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I)) atTop
      (𝓝 (Complex.exp (↑ξ * ↑(compensatedPoissonSum K X f (volume.prod ν) ω) * Complex.I))) := by
    filter_upwards [ae_finite_support_pieceSum hd hbandmeas hbandfin (g := f)
      (fun p hp => by rw [hf_def]; exact Set.indicator_of_notMem hp _)] with ω hωfin
    have hsummablePiece : Summable (fun k => pieceSum K X f k ω) :=
      summable_of_ne_finset_zero (s := hωfin.toFinset) fun k hk => by
        by_contra hne
        exact hk (hωfin.mem_toFinset.mpr hne)
    have hsummableC : Summable (fun k => ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) := by
      have h := hasSum_integral_iUnion (μ := volume.prod ν) (f := f)
        (fun k => measurableSet_prmPiece (m := volume.prod ν))
        (pairwise_disjoint_prmPiece (m := volume.prod ν))
        (by rw [iUnion_prmPiece]; exact hf1.integrableOn)
      exact h.summable
    have hsummableComp : Summable (fun k => compensatedPieceSum K X f (volume.prod ν) k ω) :=
      (hsummablePiece.hasSum.sub hsummableC.hasSum).summable
    have htends : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), compensatedPieceSum K X f (volume.prod ν) k ω)
        atTop (𝓝 (compensatedPoissonSum K X f (volume.prod ν) ω)) :=
      hsummableComp.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact (hgcont.tendsto _).comp htends
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  simp_rw [charFun_partial_compensatedBandSum hd hbandFnmeas hf1 ξ] at hdct
  have hprodexp : ∀ n, ∏ k ∈ Finset.range (n + 1),
        Complex.exp (∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I) ∂(volume.prod ν))
      = Complex.exp (∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)) :=
    fun n => (Complex.exp_sum _ _).symm
  simp_rw [hprodexp] at hdct
  have hprodlim : Tendsto (fun n => Complex.exp (∑ k ∈ Finset.range (n + 1), ∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
            ∂(volume.prod ν))) atTop
      (𝓝 (Complex.exp (∫ x,
        (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
          ∂(volume.prod ν)))) :=
    (Complex.continuous_exp.tendsto _).comp
      (hGHasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have hval := tendsto_nhds_unique hdct hprodlim
  rw [charFun_apply_real, integral_map hmeas_sum.aemeasurable (by fun_prop), hval, hfinal]
