-- Prove2me | solution 1 for OAI.YauCounterexamples.nonempty_compactMetricAtlas
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:35:59.719329+00:00
-- url     : https://prove2.me/submissions/3a90dda7-d418-450c-9c0d-11458d94d220

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffPartialIteratedFDeriv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
namespace YauCounterexamples
section SmoothFamily
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiff_partial_iteratedFDeriv (f : A → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (f p.1) p.2) := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.uncurry_def, ContinuousLinearEquiv.coe_coe] using!
      ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff.comp hf)
  | succ n ih =>
    have hh : ContDiff ℝ ∞ (fun z : (A × E) × E => iteratedFDeriv ℝ n (f z.1.1) z.2) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd : ContDiff ℝ ∞ (fun z : A × E => fderiv ℝ (iteratedFDeriv ℝ n (f z.1)) z.2) :=
      hh.fderiv contDiff_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ContinuousLinearEquiv.coe_coe] using!
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.toContinuousLinearEquiv.contDiff.comp hd)

end SmoothFamily
section CompactFamily
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendsto_schwartz_of_common_support
    (f : ℝ → 𝓢(E, F)) (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (K : Set E) (hK : IsCompact K) (hsupp : ∀ r, tsupport (f r) ⊆ K)
    (hzero : f 0 = 0) : Tendsto f (𝓝 0) (𝓝 0) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  have hc : Continuous (fun p : ℝ × K => ‖(p.2 : E)‖ ^ k *
      ‖iteratedFDeriv ℝ n (f p.1) (p.2 : E)‖) := by
    exact ((continuous_subtype_val.comp continuous_snd).norm.pow k).mul
      (((contDiff_partial_iteratedFDeriv (fun r x => f r x) hf n).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).norm)
  have hu := Continuous.tendstoUniformly
    (fun r (x : K) => ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖) hc 0
  have he : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ x : K,
      ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖ < ε / 2 := by
    have hu' := (Metric.tendstoUniformly_iff.mp hu) (ε / 2) (by positivity)
    filter_upwards [hu'] with r hr
    intro x
    simpa [hzero, dist_comm, Real.dist_eq, abs_of_nonneg (by positivity :
      0 ≤ ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖)] using hr x
  filter_upwards [he] with r hr
  simp only [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (f r) (by positivity) ?_)
    (half_lt_self hε)
  intro x
  by_cases hx : x ∈ K
  · exact (hr ⟨x, hx⟩).le
  · have hz : iteratedFDeriv ℝ n (f r) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx (hsupp r (tsupport_iteratedFDeriv_subset n h))
    simp only [hz, norm_zero, mul_zero]
    positivity

end CompactFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma rescaledCoefficient_tendsto (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) :
    Tendsto (rescaledCoefficient f χ hf hχ hχc p) (𝓝 0) (𝓝 0) := by
  apply tendsto_schwartz_of_common_support _ ?_ (tsupport χ) hχc ?_ ?_
  · change ContDiff ℝ ∞ (fun z : ℝ × E => χ z.2 * (f (p + z.1 • z.2) - f p))
    exact (hχ.comp contDiff_snd).mul
      ((hf.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))).sub contDiff_const)
  · intro r
    exact tsupport_mul_subset_left
  · ext x
    simp [rescaledCoefficient]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnisotropicConstant
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform ContDiff
variable {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma anisotropic_inverse_hasTemperateGrowth (L : E ≃L[ℝ] G) {α : ℝ} (hα : 0 < α) :
    (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp
    ((inverse_quadratic_hasTemperateGrowth (E := G) hα).comp L.toContinuousLinearMap.hasTemperateGrowth)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropicResolventSymbol_hasTemperateGrowth (L : E ≃L[ℝ] G)
    (α : ℝ) (hα : 1 ≤ α) :
    (anisotropicResolventSymbol L α hα : E → ℂ).HasTemperateGrowth := by
  change (fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2))).HasTemperateGrowth
  have hi := anisotropic_inverse_hasTemperateGrowth L (lt_of_lt_of_le zero_lt_one hα)
  have hp : (fun x : E => Complex.ofReal (1 + ‖x‖ ^ 2)).HasTemperateGrowth := by fun_prop
  simpa only [div_eq_mul_inv, Complex.ofReal_mul] using! hp.mul hi

lemma anisotropicSobolevResolvent_distribution (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s + 2) (anisotropicSobolevResolvent L s α hα u) =
      fourierMultiplierCLM F (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹))
        (fourierSobolevDistribution E F s u) := by
  have hi := anisotropic_inverse_hasTemperateGrowth L (lt_of_lt_of_le zero_lt_one hα)
  change fourierSobolevDistribution E F (s + 2)
    (sobolevBoundedMultiplier (s + 2) (anisotropicResolventSymbol L α hα) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _ (anisotropicResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq, TemperedDistribution.fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (anisotropicResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) hi]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(s + 2) / 2)) *
      Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2)) =
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)) * Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv (1 + ‖x‖ ^ 2), ← mul_assoc]
  congr 1
  conv_lhs => arg 2; rw [← Real.rpow_one (1 + ‖x‖ ^ 2)]
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

theorem anisotropicSobolevResolvent_equation (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierMultiplierCLM F (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2))
      (fourierSobolevDistribution E F (s + 2) (anisotropicSobolevResolvent L s α hα u)) =
      fourierSobolevDistribution E F s u := by
  have hi := anisotropic_inverse_hasTemperateGrowth L (lt_of_lt_of_le zero_lt_one hα)
  have hq : (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2)).HasTemperateGrowth := by
    exact Complex.hasTemperateGrowth_ofReal.comp
      ((Function.HasTemperateGrowth.const α).add
        ((Function.hasTemperateGrowth_norm_sq (H := G)).comp
          L.toContinuousLinearMap.hasTemperateGrowth))
  rw [anisotropicSobolevResolvent_distribution,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hi hq]
  have hmul : (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)) *
      (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2)) = fun _ => 1 := by
    ext x
    rw [Pi.mul_apply, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
  rw [hmul, TemperedDistribution.fourierMultiplierCLM_const, one_smul]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropicHalfResolventSymbol_hasTemperateGrowth (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) :
    (anisotropicHalfResolventSymbol L α hα : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => Complex.ofReal
    ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2))).HasTemperateGrowth
  simp only [div_eq_mul_inv]
  exact Complex.hasTemperateGrowth_ofReal.comp
    ((by fun_prop : (fun x : E => (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)).HasTemperateGrowth).mul
      ((inverse_quadratic_hasTemperateGrowth (E := G) (lt_of_lt_of_le zero_lt_one hα)).comp L.toContinuousLinearMap.hasTemperateGrowth))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_anisotropicHalfResolventSymbol_le (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicHalfResolventSymbol L α hα‖ ≤ (anisotropicConstant L * (Real.sqrt α)⁻¹) := by
  apply (BoundedContinuousFunction.norm_le (show 0 ≤ anisotropicConstant L * (Real.sqrt α)⁻¹ from mul_nonneg (le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2))) (by positivity))).mpr
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2))‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact anisotropic_half_scalar_bound L α hα x

omit [CompleteSpace F] in
lemma norm_anisotropicHalfSobolevResolvent_le (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicHalfSobolevResolvent (F := F) L s α hα‖ ≤ (anisotropicConstant L * (Real.sqrt α)⁻¹) :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_anisotropicHalfResolventSymbol_le L α hα)

lemma anisotropicHalfSobolevResolvent_distribution (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s + 1) (anisotropicHalfSobolevResolvent L s α hα u) =
      fourierMultiplierCLM F (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)) (fourierSobolevDistribution E F s u) := by
  have hi : (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp
      ((inverse_quadratic_hasTemperateGrowth (E := G) (lt_of_lt_of_le zero_lt_one hα)).comp L.toContinuousLinearMap.hasTemperateGrowth)
  change fourierSobolevDistribution E F (s + 1)
      (sobolevBoundedMultiplier (s + 1) (anisotropicHalfResolventSymbol L α hα) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _ (anisotropicHalfResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.fourierMultiplierCLM_apply, fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    TemperedDistribution.fourierMultiplierCLM_apply,
    fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (anisotropicHalfResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) hi]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(s + 1) / 2)) *
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2)) =
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)) * Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) (α + ‖L x‖ ^ 2),
    ← mul_assoc, ← Real.rpow_add (by positivity)]
  congr 2
  ring

lemma anisotropicSobolevResolvent_half_bound (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (anisotropicSobolevResolvent L s α hα u)‖ ≤
      (anisotropicConstant L * (Real.sqrt α)⁻¹) * ‖u‖ := by
  have heq : sobolevInclusion (s + 2) (s + 1) (by linarith) (anisotropicSobolevResolvent L s α hα u) =
      anisotropicHalfSobolevResolvent L s α hα u := by
    apply fourierSobolevDistribution_injective (s + 1)
    rw [sobolevInclusion_distribution, anisotropicSobolevResolvent_distribution,
      anisotropicHalfSobolevResolvent_distribution]
  rw [heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_anisotropicHalfSobolevResolvent_le L s α hα) (norm_nonneg u))

end YauCounterexamples

open Set Filter
open scoped SchwartzMap ContDiff Topology

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_AnisotropicCompositionSmall
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
section Neumann
variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma neumannCorrectedInverse_bound (R : Y →L[𝕜] X) (P : X →L[𝕜] Y)
    (h : ‖R ∘L P‖ < 1) (C : ℝ) (hR : ‖R‖ ≤ C) (hq : C * ‖P‖ ≤ 1 / 2) (f : Y) :
    ‖neumannCorrectedInverse R P h f‖ ≤ 2 * C * ‖f‖ := by
  have hC := (norm_nonneg R).trans hR
  let u := neumannCorrectedInverse R P h f
  have hu : ‖u‖ ≤ C * (‖f‖ + ‖P‖ * ‖u‖) := by
    conv_lhs => rw [show u = R (f + P u) from neumannCorrectedInverse_fixed R P h f]
    exact (R.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hR (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add le_rfl (P.le_opNorm u))) hC))
  have hp := mul_le_mul_of_nonneg_right hq (norm_nonneg u)
  dsimp only [u] at hu hp
  nlinarith

lemma neumannCorrectedInverse_lower_bound (R : Y →L[𝕜] X) (P : X →L[𝕜] Y)
    (h : ‖R ∘L P‖ < 1) (C H : ℝ) (hR : ‖R‖ ≤ C) (hq : C * ‖P‖ ≤ 1 / 2)
    (J : X →L[𝕜] Z) (hJ : ‖J ∘L R‖ ≤ H) (f : Y) :
    ‖J (neumannCorrectedInverse R P h f)‖ ≤ 2 * H * ‖f‖ := by
  have hH := (norm_nonneg (J ∘L R)).trans hJ
  let u := neumannCorrectedInverse R P h f
  have hu := neumannCorrectedInverse_bound R P h C hR hq f
  have hpu : ‖P u‖ ≤ ‖f‖ := by
    have h := (P.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg P))
    have hq' := mul_le_mul_of_nonneg_right hq (norm_nonneg f)
    nlinarith
  calc
    ‖J u‖ = ‖(J ∘L R) (f + P u)‖ := by
      congr 1
      exact congrArg J (neumannCorrectedInverse_fixed R P h f)
    _ ≤ ‖J ∘L R‖ * ‖f + P u‖ := (J ∘L R).le_opNorm _
    _ ≤ H * (‖f‖ + ‖P u‖) := mul_le_mul hJ (norm_add_le _ _) (norm_nonneg _) hH
    _ ≤ H * (‖f‖ + ‖f‖) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hpu) hH
    _ = _ := by ring
end Neumann

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rescaledCoefficient_sobolev_tendsto (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (s : ℝ) :
    Filter.Tendsto (fun r => schwartzToSobolev s (rescaledCoefficient f χ hf hχ hχc p r))
      (𝓝 0) (𝓝 0) := by
  simpa only [map_zero, Function.comp_def] using! (schwartzToSobolev s).continuous.continuousAt.tendsto.comp
    (rescaledCoefficient_tendsto f χ hf hχ hχc p)

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

lemma localEllipticInverse_equation (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) (f : FourierSobolevSpace E ℂ s) :
    fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2))
      (fourierSobolevDistribution E ℂ (s + 2) (localEllipticInverse L s α hα P hP f)) -
      fourierSobolevDistribution E ℂ s (P (localEllipticInverse L s α hα P hP f)) =
      fourierSobolevDistribution E ℂ s f := by
  have he : localEllipticInverse L s α hα P hP f =
      anisotropicSobolevResolvent L s α hα (f + P (localEllipticInverse L s α hα P hP f)) :=
    neumannCorrectedInverse_fixed (𝕜 := ℂ)
      (X := FourierSobolevSpace E ℂ (s + 2)) (Y := FourierSobolevSpace E ℂ s)
      (anisotropicSobolevResolvent L s α hα) P (anisotropic_composition_small L s α hα P hP) f
  conv_lhs => lhs; arg 2; rw [he]
  rw [anisotropicSobolevResolvent_equation, map_add, add_sub_cancel_right]

lemma norm_localEllipticInverse_le (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) :
    ‖localEllipticInverse L s α hα P hP‖ ≤ 2 * anisotropicConstant L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have : 0 ≤ anisotropicConstant L := le_trans zero_le_one (le_max_left _ _)
    positivity)
  intro f
  exact neumannCorrectedInverse_bound _ _ _ _ (norm_anisotropicSobolevResolvent_le L s α hα) hP f

lemma localEllipticInverse_half_bound (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) (f : FourierSobolevSpace E ℂ s) :
    ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (localEllipticInverse L s α hα P hP f)‖ ≤
      2 * (anisotropicConstant L * (Real.sqrt α)⁻¹) * ‖f‖ := by
  apply neumannCorrectedInverse_lower_bound _ _ _ _ _
    (norm_anisotropicSobolevResolvent_le L s α hα) hP
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have : 0 ≤ anisotropicConstant L := le_trans zero_le_one (le_max_left _ _)
    positivity)
  intro u
  exact anisotropicSobolevResolvent_half_bound L s α hα u

lemma eventually_localEllipticInverse_small (L : E ≃L[ℝ] G) (s : ℝ)
    (P : ℝ → FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : Tendsto P (𝓝 0) (𝓝 0)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), anisotropicConstant L * ‖P r‖ ≤ 1 / 2 := by
  have h : Tendsto (fun r => anisotropicConstant L * ‖P r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hP.norm
  exact (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).mono
    (fun _ hh => hh.le)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_QuadraticInnerSpace
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
namespace YauCounterexamples

namespace QuadraticInnerSpace
variable {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : A.PosDef)

lemma norm_sq (x : QuadraticInnerSpace A hA) : ‖x‖ ^ 2 = x ⬝ᵥ (A *ᵥ x) := by
  rw [← real_inner_self_eq_norm_sq]
  change (A *ᵥ x) ⬝ᵥ x = _
  exact dotProduct_comm _ _

end QuadraticInnerSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)

lemma quadraticNormEquiv_apply (x : E) (i : ι) :
    quadraticNormEquiv b A hA x i = ⟪b i, x⟫_ℝ := by
  classical
  change b.dualBasis.equivFun ((InnerProductSpace.toDual ℝ E x).toLinearMap) i = _
  rw [Module.Basis.dualBasis_equivFun]
  change ⟪x, b i⟫_ℝ = ⟪b i, x⟫_ℝ
  exact real_inner_comm (b i) x

lemma quadraticNormEquiv_norm_sq (x : E) :
    ‖quadraticNormEquiv b A hA x‖ ^ 2 =
      ∑ i, ∑ j, A i j * ⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ := by
  rw [QuadraticInnerSpace.norm_sq]
  simp only [dotProduct, Matrix.mulVec, quadraticNormEquiv_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end YauCounterexamples

open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousSobolevFirstDerivative
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolevSecondDerivative_distribution (s : ℝ) (v w : E)
    (u : FourierSobolevSpace E ℂ s) :
    fourierSobolevDistribution E ℂ (s - 2) (sobolevSecondDerivative s v w u) =
      ∂_{v} (∂_{w} (fourierSobolevDistribution E ℂ s u)) := by
  have hh : s - 2 = (s - 1) - 1 := by ring
  rw [hh]
  exact (sobolevDerivative_distribution (s - 1) v _).trans
    (congrArg (fun f : 𝓢'(E, ℂ) => ∂_{v} f) (sobolevDerivative_distribution s w u))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

lemma fourierMultiplier_add {f g : E → ℂ}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) (T : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (f + g) T = fourierMultiplierCLM ℂ f T + fourierMultiplierCLM ℂ g T := by
  simp only [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_add hf hg, _root_.add_apply,
    FourierTransform.fourierInv_add]

lemma secondDerivative_fourier (v w : E) (T : 𝓢'(E, ℂ)) :
    ∂_{v} (∂_{w} T) = -((2 * Real.pi : ℝ) ^ 2 : ℂ) •
      fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ)) T := by
  simp_rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM, map_smul, smul_smul]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr 1
  · push_cast
    ring_nf
    simp
  · congr 2
    ext x
    simp only [Pi.mul_apply, Complex.ofReal_mul, real_inner_comm]
    ring

omit [MeasurableSpace E] [BorelSpace E] in
lemma physicalQuadraticEquiv_norm_sq (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (x : E) :
    ‖physicalQuadraticEquiv b A hA x‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ∑ i, ∑ j, A i j * ⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ := by
  change ‖quadraticNormEquiv b A hA ((2 * Real.pi) • x)‖ ^ 2 = _
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow,
    quadraticNormEquiv_norm_sq]

lemma principal_fourierMultiplier (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (T : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖physicalQuadraticEquiv b A hA x‖ ^ 2)) T =
      - ∑ i, ∑ j, (A i j : ℂ) • (∂_{b i} (∂_{b j} T)) := by
  simp_rw [physicalQuadraticEquiv_norm_sq, Complex.ofReal_mul, Complex.ofReal_sum]
  simp only [Complex.ofReal_mul]
  have hh (i j : ι) : (fun x : E => (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ *
      Complex.ofReal ⟪b j, x⟫_ℝ).HasTemperateGrowth := by fun_prop
  have hsum : (fun x : E => ∑ i, ∑ j, (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ *
      Complex.ofReal ⟪b j, x⟫_ℝ).HasTemperateGrowth := by fun_prop
  rw [show (fun x : E => Complex.ofReal ((2 * Real.pi) ^ 2) *
      ∑ i, ∑ j, (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ * Complex.ofReal ⟪b j, x⟫_ℝ) =
      Complex.ofReal ((2 * Real.pi) ^ 2) • (fun x : E => ∑ i, ∑ j,
      (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ * Complex.ofReal ⟪b j, x⟫_ℝ) from rfl,
    TemperedDistribution.fourierMultiplierCLM_smul hsum,
    _root_.smul_apply]
  simp_rw [TemperedDistribution.fourierMultiplierCLM_sum ℂ (fun i _ =>
    Function.HasTemperateGrowth.sum fun j _ => hh i j),
    TemperedDistribution.fourierMultiplierCLM_sum ℂ (fun j _ => hh _ j),
    _root_.sum_apply, Finset.smul_sum, secondDerivative_fourier, smul_smul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun x : E => (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ *
      Complex.ofReal ⟪b j, x⟫_ℝ) = (A i j : ℂ) •
      (fun x : E => Complex.ofReal (⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ)) by
        ext x; simp; ring,
    TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop),
    _root_.smul_apply, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

lemma elliptic_fourierMultiplier (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (α : ℝ) (T : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (α + ‖physicalQuadraticEquiv b A hA x‖ ^ 2)) T =
      (α : ℂ) • T - ∑ i, ∑ j, (A i j : ℂ) • (∂_{b i} (∂_{b j} T)) := by
  rw [show (fun x : E => Complex.ofReal (α + ‖physicalQuadraticEquiv b A hA x‖ ^ 2)) =
      (fun _ => (α : ℂ)) + (fun x : E => Complex.ofReal (‖physicalQuadraticEquiv b A hA x‖ ^ 2)) by
        ext x; simp,
    fourierMultiplier_add (by fun_prop) (by
      exact Complex.hasTemperateGrowth_ofReal.comp
        ((Function.hasTemperateGrowth_norm_sq (H := QuadraticInnerSpace A hA)).comp (physicalQuadraticEquiv b A hA).toContinuousLinearMap.hasTemperateGrowth)),
    TemperedDistribution.fourierMultiplierCLM_const, _root_.smul_apply,
    ContinuousLinearMap.id_apply, principal_fourierMultiplier, sub_eq_add_neg]

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fourierSobolevDistribution_congr (s t : ℝ) (h : s = t) :
    fourierSobolevDistribution E ℂ s = fourierSobolevDistribution E ℂ t := by
  subst t
  rfl

lemma frozenSobolevOperator_distribution {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (s α : ℝ) (u : FourierSobolevSpace E ℂ (s + 2)) :
    fourierSobolevDistribution E ℂ s (frozenSobolevOperator b A s α u) =
      fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal
        (α + ‖physicalQuadraticEquiv b A hA x‖ ^ 2))
        (fourierSobolevDistribution E ℂ (s + 2) u) := by
  rw [elliptic_fourierMultiplier]
  simp only [frozenSobolevOperator, _root_.sub_apply,
    _root_.smul_apply, _root_.sum_apply, map_sub, map_smul, map_sum,
    sobolevInclusion_distribution]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he : fourierSobolevDistribution E ℂ (s + 2 - 2) =
      fourierSobolevDistribution E ℂ s := fourierSobolevDistribution_congr (s + 2 - 2) s (by ring)
  rw [← he]
  exact sobolevSecondDerivative_distribution (s + 2) (b i) (b j) u

lemma localEllipticInverse_sobolev_equation {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant (physicalQuadraticEquiv b A hA) * ‖P‖ ≤ 1 / 2)
    (f : FourierSobolevSpace E ℂ s) :
    frozenSobolevOperator b A s α
      (localEllipticInverse (physicalQuadraticEquiv b A hA) s α hα P hP f) -
      P (localEllipticInverse (physicalQuadraticEquiv b A hA) s α hα P hP f) = f := by
  apply fourierSobolevDistribution_injective s
  rw [map_sub, frozenSobolevOperator_distribution b A hA]
  exact localEllipticInverse_equation _ s α hα P hP f

lemma frozenSobolevOperator_representative {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (s α : ℝ)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 2))
    (u : FourierSobolevSpace E ℂ (s + 2)) (x : E) :
    sobolevRepresentative hs (frozenSobolevOperator b A s α u) x =
      (α : ℂ) * sobolevRepresentative ht u x - ∑ i, ∑ j, (A i j : ℂ) *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i) := by
  simp only [frozenSobolevOperator, _root_.sub_apply,
    _root_.smul_apply, _root_.sum_apply, map_sub, map_smul, map_sum,
    sobolevInclusion_representative _ _ _ ht hs, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hh := sobolevSecondDerivative_representative
    (s := s + 2) (by simpa only [show s + 2 - 2 = s by ring] using hs) ht u (b i) (b j) x
  rw [sobolevRepresentative_congr (s + 2 - 2) s (by ring) _ hs] at hh
  exact hh


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RescaledDifferentialPerturbation
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scaledLowerCoefficient_tendsto (k : ℕ) (hk : k ≠ 0) (f χ : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) :
    Tendsto (scaledLowerCoefficient k f χ hf hχ hχc p) (𝓝 0) (𝓝 0) := by
  apply tendsto_schwartz_of_common_support _ ?_ (tsupport χ) hχc ?_ ?_
  · change ContDiff ℝ ∞ (fun z : ℝ × E => χ z.2 * ((z.1 : ℂ) ^ k * f (p + z.1 • z.2)))
    exact (hχ.comp contDiff_snd).mul
      (((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow k).mul
        (hf.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))))
  · intro r
    exact tsupport_mul_subset_left
  · ext x
    simp [scaledLowerCoefficient, hk]

lemma scaledLowerCoefficient_sobolev_tendsto (k : ℕ) (hk : k ≠ 0) (f χ : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (s : ℝ) :
    Tendsto (fun r => schwartzToSobolev s (scaledLowerCoefficient k f χ hf hχ hχc p r))
      (𝓝 0) (𝓝 0) := by
  simpa only [map_zero, Function.comp_def] using! (schwartzToSobolev s).continuous.continuousAt.tendsto.comp
    (scaledLowerCoefficient_tendsto k hk f χ hf hχ hχc p)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma coefficientPerturbation_tendsto {ι : Type*} [Fintype ι] (b : ι → E) {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s)
    (a : ℝ → ι → ι → FourierSobolevSpace E ℂ s)
    (c : ℝ → ι → FourierSobolevSpace E ℂ s)
    (ha : ∀ i j, Tendsto (fun r => a r i j) (𝓝 0) (𝓝 0))
    (hc : ∀ i, Tendsto (fun r => c r i) (𝓝 0) (𝓝 0)) :
    Tendsto (fun r => coefficientPerturbation b hs (a r) (c r)) (𝓝 0) (𝓝 0) := by
  have hmul {a : ℝ → FourierSobolevSpace E ℂ s} (ha : Tendsto a (𝓝 0) (𝓝 0))
      (D : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s) :
      Tendsto (fun r => (sobolevProduct hs (a r)) ∘L D) (𝓝 0) (𝓝 0) := by
    have hcomp : Continuous (fun B : FourierSobolevSpace E ℂ s →L[ℂ]
        FourierSobolevSpace E ℂ s => B ∘L D) := by fun_prop
    simpa only [map_zero, ContinuousLinearMap.zero_comp, Function.comp_def] using!
      hcomp.continuousAt.tendsto.comp ((sobolevProduct hs).continuous.continuousAt.tendsto.comp ha)
  simpa only [coefficientPerturbation, Finset.sum_const_zero, add_zero] using!
    (tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hmul (ha i j) _))).add
      (tendsto_finsetSum Finset.univ (fun i _ => hmul (hc i) _))


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]
variable (b : Module.Basis ι ℝ E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)

lemma rescaledDifferentialPerturbation_tendsto :
    Tendsto (rescaledDifferentialPerturbation b a c ha hc χ hχ hχc p hs) (𝓝 0) (𝓝 0) := by
  apply coefficientPerturbation_tendsto
  · intro i j
    exact rescaledCoefficient_sobolev_tendsto _ _ _ _ _ _ _
  · intro i
    exact scaledLowerCoefficient_sobolev_tendsto 1 (by norm_num) _ _ _ _ _ _ _

lemma rescaledDifferentialPerturbation_representative (r : ℝ)
    (ht : Module.finrank ℝ E < 2 * (s + 2)) (u : FourierSobolevSpace E ℂ (s + 2)) (x : E)
    (hχx : χ x = 1) :
    sobolevRepresentative hs (rescaledDifferentialPerturbation b a c ha hc χ hχ hχc p hs r u) x =
      (∑ i, ∑ j, ((a i j (p + r • x) : ℂ) - (a i j p : ℂ)) *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i)) +
      (r : ℂ) * ∑ i, (c i (p + r • x) : ℂ) *
        fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
  rw [rescaledDifferentialPerturbation, coefficientPerturbation_representative _ hs ht]
  simp only [sobolevRepresentative_schwartz, SchwartzMap.toBoundedContinuousFunction_apply]
  change (∑ i, ∑ j, (χ x * ((a i j (p + r • x) : ℂ) - (a i j p : ℂ))) * _) +
    ∑ i, (χ x * ((r : ℂ) ^ 1 * (c i (p + r • x) : ℂ))) * _ = _
  simp only [hχx, one_mul, pow_one, mul_assoc, ← Finset.mul_sum]

include ha hc hχ hχc in

theorem exists_rescaled_local_inverse (hA : Matrix.PosDef (fun i j => a i j p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r| < ε → ∀ α : ℝ, 1 ≤ α →
      ∃ R : FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2),
        ‖R‖ ≤ 2 * @anisotropicConstant E (QuadraticInnerSpace (fun i j => a i j p) hA) _ _
          (QuadraticInnerSpace.instNormedAddCommGroup _ hA)
          (QuadraticInnerSpace.instInnerProductSpaceReal _ hA)
          (physicalQuadraticEquiv b (fun i j => a i j p) hA) ∧
        (∀ f, ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (R f)‖ ≤
          2 * (@anisotropicConstant E (QuadraticInnerSpace (fun i j => a i j p) hA) _ _
          (QuadraticInnerSpace.instNormedAddCommGroup _ hA)
          (QuadraticInnerSpace.instInnerProductSpaceReal _ hA)
          (physicalQuadraticEquiv b (fun i j => a i j p) hA) *
            (Real.sqrt α)⁻¹) * ‖f‖) ∧
        (∀ (ht : Module.finrank ℝ E < 2 * (s + 2)) (f : FourierSobolevSpace E ℂ s)
            (x : E), χ x = 1 →
          (α : ℂ) * sobolevRepresentative ht (R f) x -
            (∑ i, ∑ j, (a i j (p + r • x) : ℂ) *
              fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ) y (b j)) x (b i)) -
            (r : ℂ) * ∑ i, (c i (p + r • x) : ℂ) *
              fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ) x (b i) =
          sobolevRepresentative hs f x) := by
  let A : Matrix ι ι ℝ := fun i j => a i j p
  let L := physicalQuadraticEquiv b A hA
  let P := rescaledDifferentialPerturbation b a c ha hc χ hχ hχc p hs
  have hev := eventually_localEllipticInverse_small L s P
    (rescaledDifferentialPerturbation_tendsto b a c ha hc χ hχ hχc p hs)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun r hr α hα => ?_⟩
  have hP : anisotropicConstant L * ‖P r‖ ≤ 1 / 2 := he (by simpa [Real.dist_eq] using hr)
  let R := localEllipticInverse L s α hα (P r) hP
  refine ⟨R, norm_localEllipticInverse_le _ _ _ _ _ _,
    fun f => localEllipticInverse_half_bound _ _ _ _ _ _ f, ?_⟩
  intro ht f x hχx
  have hh := congrArg (fun u : FourierSobolevSpace E ℂ s => sobolevRepresentative hs u x)
    (localEllipticInverse_sobolev_equation b A hA s α hα (P r) hP f)
  rw [map_sub, BoundedContinuousFunction.sub_apply, frozenSobolevOperator_representative b A s α hs ht,
    rescaledDifferentialPerturbation_representative b a c ha hc χ hχ hχc p hs r ht _ x hχx] at hh
  change (α : ℂ) * sobolevRepresentative ht (R f) x -
      (∑ i, ∑ j, (a i j p : ℂ) * _) -
      ((∑ i, ∑ j, ((a i j (p + r • x) : ℂ) - (a i j p : ℂ)) * _) + _) = _ at hh
  simp only [sub_mul, Finset.sum_sub_distrib] at hh
  linear_combination hh




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ExistsFinitePatchPartition
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff
namespace YauCounterexamples
section PatchCutoffs
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_finite_patch_partition (U : M → Set M) (hU : ∀ p, IsOpen (U p))
    (hp : ∀ p, p ∈ U p) :
    ∃ t : Finset M, ∃ ρ : SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ,
      ρ.IsSubordinate (fun i => U (i : M)) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (by intro x _; exact mem_iUnion_of_mem x (hp x))
  refine ⟨t, ?_⟩
  apply SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ
    (fun i : t => U (i : M)) (fun i => hU (i : M))
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion_of_mem ⟨p, hp⟩ hpx

theorem exists_patch_buffer {U : Set M} (hU : IsOpen U) {η : M → ℂ}
    (hs : tsupport η ⊆ U) :
    ∃ χ : M → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ ∧
      tsupport χ ⊆ U ∧ χ =ᶠ[𝓝ˢ (tsupport η)] 1 := by
  obtain ⟨v, hv, hηv, hvc⟩ := normal_exists_closure_subset (isClosed_tsupport η) hU hs
  obtain ⟨f, hf1, hf0, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, E)) (n := ⊤) (isClosed_tsupport η)
    (t := v) (by simpa only [hv.interior_eq] using hηv)
  refine ⟨fun x => (f x : ℂ), Complex.ofRealCLM.contMDiff.comp f.contMDiff, ?_, ?_⟩
  · apply (closure_mono (show support (fun x => (f x : ℂ)) ⊆ v from ?_)).trans hvc
    intro x hx
    by_contra h
    exact hx (by simp [hf0 x h])
  · filter_upwards [hf1] with x hx
    simp only [hx, Complex.ofReal_one, Pi.one_apply]

end PatchCutoffs

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFirstCoefficient (g : SmoothMetric E M) (p : M) (j : CoordIndex E)
    {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (metricFirstCoefficient g p j) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  exact ((hd.mul ha).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold ContDiff Matrix.Norms.Elementwise
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_smooth_metric_coefficients_at (g : SmoothMetric E M) (p : M) :
    ∃ (a : CoordIndex E → CoordIndex E → E → ℝ) (c : CoordIndex E → E → ℝ),
      (∀ i j, ContDiff ℝ ∞ (a i j)) ∧ (∀ i, ContDiff ℝ ∞ (c i)) ∧
      Matrix.PosDef (fun i j => a i j ((chartAt E p) p)) ∧
      ∃ δ : ℝ, 0 < δ ∧ Metric.ball ((chartAt E p) p) δ ⊆ (chartAt E p).target ∧
        (∀ y ∈ Metric.ball ((chartAt E p) p) δ,
          (∀ i j, a i j y = (metricCoefficients g p y)⁻¹ i j) ∧
          (∀ i, c i y = metricFirstCoefficient g p i y)) := by
  let φ : E → Matrix (CoordIndex E) (CoordIndex E) ℝ × (CoordIndex E → ℝ) :=
    fun y => ((metricCoefficients g p y)⁻¹, fun i => metricFirstCoefficient g p i y)
  have hp : (chartAt E p) p ∈ (chartAt E p).target :=
    (chartAt E p).map_source (mem_chart_source E p)
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        contDiffOn_metricInverse g p i j))
    · exact contDiffOn_pi.mpr (fun i y hy =>
        (contDiffAt_metricFirstCoefficient g p i hy).contDiffWithinAt)
  obtain ⟨ψ, hψ, he⟩ := smooth_extension_near_compact (isCompact_singleton)
    (chartAt E p).open_target (singleton_subset_iff.mpr hp) hφ
  have he' : φ =ᶠ[𝓝 ((chartAt E p) p)] ψ :=
    he.filter_mono (nhds_le_nhdsSet (mem_singleton _))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp
    (he'.and ((chartAt E p).open_target.mem_nhds hp))
  refine ⟨fun i j y => (ψ y).1 i j, fun i y => (ψ y).2 i,
    fun i j => contDiff_pi.mp (contDiff_pi.mp hψ.fst i) j,
    fun i => contDiff_pi.mp hψ.snd i, ?_, δ, hδ, ?_, ?_⟩
  · have h0 := congrArg Prod.fst he'.self_of_nhds
    change Matrix.PosDef ((ψ ((chartAt E p) p)).1)
    rw [← h0]
    exact (metricCoefficients_posDef g p hp).inv
  · intro y hy
    exact (hd hy).2
  · intro y hy
    have hh := (hd hy).1
    exact ⟨fun i j => congrFun (congrFun (congrArg Prod.fst hh.symm) i) j,
      fun i => congrFun (congrArg Prod.snd hh.symm) i⟩


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ExistsMetricPatchInverse
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_metric_patch_inverse (g : SmoothMetric E M) (p : M)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      Metric.closedBall ((chartAt E p) p) r ⊆ (chartAt E p).target ∧
      ∀ α : ℝ, 1 ≤ α →
        ∃ R : FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2),
          ‖R‖ ≤ C ∧
          (∀ f, ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (R f)‖ ≤
            C * (Real.sqrt α)⁻¹ * ‖f‖) ∧
          (∀ (ht : Module.finrank ℝ E < 2 * (s + 2))
              (f : FourierSobolevSpace E ℂ s) (x : E), ‖x‖ ≤ 1 →
              (α : ℂ) * sobolevRepresentative ht (R f) x -
              (∑ i, ∑ j, ((metricCoefficients g p ((chartAt E p) p + r • x))⁻¹ i j : ℂ) *
                fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ)
                  y (Module.finBasis ℝ E j)) x (Module.finBasis ℝ E i)) -
              (r : ℂ) * ∑ i, (metricFirstCoefficient g p i ((chartAt E p) p + r • x) : ℂ) *
                fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ) x (Module.finBasis ℝ E i) =
              sobolevRepresentative hs f x) := by
  obtain ⟨a, c, ha, hc, hA, δ, hδ, hd, hcoeff⟩ := exists_smooth_metric_coefficients_at g p
  let A : Matrix (CoordIndex E) (CoordIndex E) ℝ := fun i j => a i j ((chartAt E p) p)
  let L := physicalQuadraticEquiv (Module.finBasis ℝ E) A hA
  obtain ⟨ε, hε, he⟩ := exists_rescaled_local_inverse (Module.finBasis ℝ E) a c ha hc
    (complexUnitBump E) (contDiff_complexUnitBump E) (hasCompactSupport_complexUnitBump E)
    ((chartAt E p) p) hs hA
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrδ : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  let C := 2 * anisotropicConstant L
  have hC : 0 < C := by
    dsimp [C, anisotropicConstant]
    positivity
  refine ⟨r, C, hr, hC, ?_, fun α hα => ?_⟩
  · exact (Metric.closedBall_subset_ball hrδ).trans hd
  · obtain ⟨R, hR, hR1, hRe⟩ := he r (by simpa only [abs_of_pos hr] using hrε) α hα
    refine ⟨R, hR, ?_, ?_⟩
    · intro f
      simpa only [C, mul_assoc] using hR1 f
    · intro ht f x hx
      have hdist : (chartAt E p) p + r • x ∈ Metric.ball ((chartAt E p) p) δ := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos hr]
        exact (mul_le_of_le_one_right hr.le hx).trans_lt hrδ
      obtain ⟨hae, hce⟩ := hcoeff _ hdist
      have hh := hRe ht f x (complexUnitBump_eq_one E hx)
      simpa only [hae, hce] using hh
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_LocalMetricInverse
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem nonempty_localMetricInverse (g : SmoothMetric E M) (p : M)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) : Nonempty (LocalMetricInverse g p s hs) := by
  obtain ⟨r, C, hr, hC, ht, hR⟩ := exists_metric_patch_inverse g p hs
  choose R hRnorm hRhalf hReq using hR
  exact ⟨⟨r, hr, C, hC, ht, R, hRnorm, hRhalf, hReq⟩⟩

lemma isOpen_metricInversePatch {g : SmoothMetric E M} {p : M} {s : ℝ}
    {hs : Module.finrank ℝ E < 2 * s} (D : LocalMetricInverse g p s hs) :
    IsOpen (metricInversePatch D) :=
  (chartAt E p).isOpen_inter_preimage Metric.isOpen_ball

lemma mem_metricInversePatch {g : SmoothMetric E M} {p : M} {s : ℝ}
    {hs : Module.finrank ℝ E < 2 * s} (D : LocalMetricInverse g p s hs) :
    p ∈ metricInversePatch D :=
  ⟨mem_chart_source E p, Metric.mem_ball_self (half_pos D.radius_pos)⟩

theorem exists_compact_metric_patches [T2Space M] [CompactSpace M]
    (g : SmoothMetric E M) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    ∃ (t : Finset M) (D : ∀ i : t, LocalMetricInverse g (i : M) s hs)
      (η χ ψ : t → M → ℂ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i)) ∧
      (∀ x, ∑ i, η i x = 1) ∧
      (∀ i, tsupport (η i) ⊆ metricInversePatch (D i)) ∧
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ metricInversePatch (D i)) ∧
      (∀ i, χ i =ᶠ[𝓝ˢ (tsupport (η i))] 1) ∧
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ metricInversePatch (D i)) ∧
      (∀ i, ψ i =ᶠ[𝓝ˢ (tsupport (χ i))] 1) := by
  classical
  let D : ∀ p : M, LocalMetricInverse g p s hs := fun p =>
    (nonempty_localMetricInverse g p hs).some
  obtain ⟨t, ρ, hρ⟩ := exists_finite_patch_partition (E := E)
    (fun p => metricInversePatch (D p)) (fun p => isOpen_metricInversePatch (D p))
    (fun p => mem_metricInversePatch (D p))
  let η : t → M → ℂ := fun i x => (ρ i x : ℂ)
  have hηm (i : t) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i) :=
    Complex.ofRealCLM.contMDiff.comp (ρ i).contMDiff
  have hηs (i : t) : tsupport (η i) ⊆ metricInversePatch (D (i : M)) := by
    apply (closure_mono (show support (η i) ⊆ support (ρ i) from ?_)).trans (hρ i)
    intro x hx
    exact fun hh => hx (by simp [η, hh])
  choose χ hχm hχs hχη using fun (i : t) => exists_patch_buffer (E := E)
    (isOpen_metricInversePatch (D (i : M))) (hηs i)
  choose ψ hψm hψs hψχ using fun (i : t) => exists_patch_buffer (E := E)
    (isOpen_metricInversePatch (D (i : M))) (hχs i)
  refine ⟨t, fun i => D (i : M), η, χ, ψ, hηm, ?_, hηs, hχm, hχs, hχη,
    hψm, hψs, hψχ⟩
  intro x
  change ∑ i : t, (ρ i x : ℂ) = 1
  rw [← Complex.ofReal_sum]
  exact_mod_cast (by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x))
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem nonempty_compactMetricAtlas_oai (g : SmoothMetric E M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))) :
    Nonempty (CompactMetricAtlas g k hs) := by
  obtain ⟨t, D, η, χ, ψ, hηm, hηone, hηs, hχm, hχs, hχη, hψm, hψs, hψχ⟩ :=
    exists_compact_metric_patches g hs
  exact ⟨⟨t, D, η, χ, ψ, hηm, hηone, hηs, hχm, hχs, hχη, hψm, hψs, hψχ⟩⟩


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.nonempty_compactMetricAtlas_oai.{u_1, u_2} := @OAI.YauCounterexamples.nonempty_compactMetricAtlas_oai.{u_1, u_2}
