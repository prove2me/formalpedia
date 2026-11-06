-- Prove2me | solution 1 for ProbabilityTheory.charFun_map_smallJumpBandIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:33:18.984505+00:00
-- url     : https://prove2.me/submissions/67c32557-7b88-4e60-829f-bf5ec6b00c4c

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Theorems.Thm_ProbabilityTheory_norm_charFun_map_sub_le
import Theorems.Thm_ProbabilityTheory_tendsto_setIntegral_annulus
import Theorems.Thm_ProbabilityTheory_charFun_map_compensatedTimeBandSum
import Theorems.Thm_ProbabilityTheory_eLpNorm_sq_bandFun
import Theorems.Thm_ProbabilityTheory_integrable_bandFun
import Theorems.Thm_ProbabilityTheory_measurable_bandFun
import Theorems.Thm_ProbabilityTheory_eLpNorm_smallJumpBand_sub_bandFun_aux
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => (compensatedPoissonIntegral hd
        ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))) ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  set V : Lp ℝ 2 μ := compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2)) with hV
  have hA_meas : ∀ n : ℕ, MeasurableSet (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}) :=
    fun n => measurableSet_Ioo.inter (measurableSet_le measurable_const continuous_abs.measurable)
  have hA_sub : ∀ n : ℕ, Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|} ⊆ Set.Ioo (-1) 1 :=
    fun n => Set.inter_subset_left
  have hA_fin : ∀ n : ℕ, ν (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}) < ⊤ := fun n => (measure_mono Set.inter_subset_right).trans_lt
      (hν.measure_setOf_abs_ge_lt_top (by positivity))
  have hslice_eq : ∀ n : ℕ, Set.Ioo (-1:ℝ) 1 \ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})
        = Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹} := by
    intro n
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_le]
    exact ⟨fun ⟨hxo, h⟩ => ⟨hxo, h hxo⟩, fun ⟨hxo, h⟩ => ⟨hxo, fun _ => h⟩⟩
  have hTrunc_ae : ∀ n : ℕ, (fun ω => (compensatedPoissonIntegral hd ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) ω)
      =ᵐ[μ] compensatedPoissonSum K X
        ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator fun p => p.2)
        ((volume : Measure ℝ).prod ν) := fun n =>
    compensatedPoissonIntegral_eq_sum hd (measurable_bandFun (hA_meas n) s t)
      (integrable_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t)
      (memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t)
  have hcharTrunc : ∀ n : ℕ, charFun (μ.map (fun ω => (compensatedPoissonIntegral hd ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ)
          * ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
          (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν) := by
    intro n
    rw [Measure.map_congr (hTrunc_ae n),
      charFun_map_compensatedTimeBandSum hd (hA_meas n) (hA_sub n) (hA_fin n) hst ξ]
  have hRHS : Tendsto (fun n : ℕ => Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
          (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν)) atTop
      (𝓝 (Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1:ℝ) 1,
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν))) :=
    (Complex.continuous_exp.tendsto _).comp
      ((tendsto_setIntegral_annulus hν ξ).const_mul ((t - s : ℝ) : ℂ))
  have hdist : ∀ n : ℕ, eLpNorm (V - compensatedPoissonIntegral hd ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) 2 μ
      = eLpNorm ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \
          (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}))).indicator fun p : ℝ × ℝ => p.2) 2
          (volume.prod ν) := by
    intro n
    rw [hV]
    exact eLpNorm_smallJumpBand_sub_bandFun_aux hd hν s t (hA_meas n) (hA_sub n) (hA_fin n)
  have htend_r : Tendsto (fun n : ℕ => (eLpNorm (V - compensatedPoissonIntegral hd
          ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
            ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
              fun p => p.2))) 2 μ).toReal) atTop (𝓝 0) := by
    have hsq : ∀ n : ℕ, ((eLpNorm (V - compensatedPoissonIntegral hd
            ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
              ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                fun p => p.2))) 2 μ).toReal) ^ 2
        = (t - s) * (∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹},
            ENNReal.ofReal (x ^ 2) ∂ν).toReal := by
      intro n
      rw [← ENNReal.toReal_pow, hdist n,
        eLpNorm_sq_bandFun (measurableSet_Ioo.diff (hA_meas n)) s t, hslice_eq n,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
    have hJ : Tendsto (fun n : ℕ => (∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹}, ENNReal.ofReal (x ^ 2) ∂ν).toReal) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (ENNReal.tendsto_toReal (by simp)).comp (tendsto_lintegral_slice_sq hν)
    have hr2 : Tendsto (fun n : ℕ => ((eLpNorm (V - compensatedPoissonIntegral hd
            ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
              ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                fun p => p.2))) 2 μ).toReal) ^ 2) atTop (𝓝 0) := by
      simp_rw [hsq]; simpa using hJ.const_mul (t - s)
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hr2
    rw [Real.sqrt_zero] at hsqrt
    exact hsqrt.congr fun n => Real.sqrt_sq ENNReal.toReal_nonneg
  have hbnd : ∀ n : ℕ, ∫ ω, |V ω - (compensatedPoissonIntegral hd
          ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
            ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
              fun p => p.2))) ω| ∂μ
      ≤ (eLpNorm (V
          - compensatedPoissonIntegral hd
            ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
              ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                fun p => p.2))) 2 μ).toReal := by
    intro n
    set Hn := V - compensatedPoissonIntegral hd
        ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2)) with hHn
    calc ∫ ω, |V ω - (compensatedPoissonIntegral hd
              ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
                ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                  fun p => p.2))) ω| ∂μ
        = ∫ ω, ‖Hn ω‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hHn ▸ Lp.coeFn_sub V
            (compensatedPoissonIntegral hd
              ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
                ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                  fun p => p.2)))] with ω hω
          rw [Real.norm_eq_abs, hω]; rfl
      _ = (eLpNorm Hn 1 μ).toReal := by
          rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable Hn),
            ← eLpNorm_one_eq_lintegral_enorm]
      _ ≤ (eLpNorm Hn 2 μ).toReal :=
          ENNReal.toReal_mono (Lp.eLpNorm_ne_top Hn)
            (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable Hn))
  have hint0 : Tendsto (fun n : ℕ => ∫ ω, |V ω - (compensatedPoissonIntegral hd
          ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
            ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
              fun p => p.2))) ω| ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hbnd htend_r
  have hLHS : Tendsto (fun n : ℕ => charFun (μ.map (fun ω => (compensatedPoissonIntegral hd ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) ω)) ξ) atTop
      (𝓝 (charFun (μ.map (fun ω => V ω)) ξ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hint0.const_mul |ξ|)
    rw [norm_sub_rev]
    exact norm_charFun_map_sub_le
      (Lp.aestronglyMeasurable V).aemeasurable
      (Lp.aestronglyMeasurable _).aemeasurable
      (((Lp.memLp V).integrable (by norm_num)).sub
        ((Lp.memLp _).integrable (by norm_num))) ξ
  exact tendsto_nhds_unique (hLHS.congr fun n => hcharTrunc n) hRHS