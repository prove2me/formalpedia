-- Prove2me | solution 1 for OAI.YauCounterexamples.three_wave_background_chart_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:37:37.495568+00:00
-- url     : https://prove2.me/submissions/0f659920-29bd-4493-a8ea-18bbfe378d05

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_global_residual_rapid_decay
import Theorems.Thm_OAI_YauCounterexamples_three_wave_lift_jets

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearPowerDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_smooth (p : E) (L : F →ₗᵢ[ℝ] E) : ContDiff ℝ ∞ (roundChart p L) :=
  contDiff_stereoInvFunAux.comp L.contDiff


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped ContDiff InnerProductSpace Topology




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
variable {n : ℕ}

section Planar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma planarLinear_apply (a b x : E) :
    planarLinear a b x = (inner ℝ a x : ℂ) + Complex.I * (inner ℝ b x : ℂ) := by
  rfl
end Planar



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ProductSphereFstContraction
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma complexIdentityPlanar (z : ℂ) : planarLinear (1:ℂ) Complex.I z = z := by
  apply Complex.ext <;> simp [planarLinear_apply,Complex.inner,Complex.mul_re,Complex.mul_im]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProductSphereFstPower
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_smooth (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_fstPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_smooth (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_sndPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma geometric_complex_product_jet_bound
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith
lemma complex_power_envelope_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : E) (h n : ℕ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,norm_one,one_mul,le_refl]
    | succ j => simp only [pow_zero,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,
        Nat.cast_zero,zero_mul,zero_pow (by omega : j+1 ≠ 0),mul_zero,le_refl]
  | succ n ih =>
    intro j hj
    have hb := geometric_complex_product_jet_bound (hf.pow n) hf x j
      (pow_nonneg hA _) hA (mul_nonneg (Nat.cast_nonneg _) hC) hC
      (fun k hk => ih k (hk.trans hj)) (fun k hk => hfj k (hk.trans hj))
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_power_weighted_jets {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
        C*(n:ℝ)^j*(Real.exp ((n:ℝ)*φ x)+‖f x‖^n) := by
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ K) hf.contDiffOn h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := Real.exp (-B)
  have hr : 0 < r := Real.exp_pos _
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n x hx j hj
  let A := max ‖f x‖ (Real.exp (φ x))
  have hA : 0 ≤ A := (norm_nonneg _).trans (le_max_left _ _)
  have hrA : r ≤ A := by
    have hlow : -B ≤ φ x := by
      have hh := (neg_abs_le (φ x)).trans' (neg_le_neg (hB x hx))
      simpa only [Real.norm_eq_abs] using hh
    exact (Real.exp_le_exp.mpr hlow).trans (le_max_right _ _)
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k f x‖ ≤ A*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using
        (le_max_left ‖f x‖ (Real.exp (φ x)))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk x hx
        _ = r*(D/r) := by field_simp
        _ ≤ A*T^k := mul_le_mul hrA ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) hA
  have hp := complex_power_envelope_jet_bound hf x h n hA hT0 hraw j hj
  have hreal : ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
      A^n*((n:ℝ)*T)^j := by
    calc
      _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ :=
        ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
          (hf.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
      _ ≤ 1*(A^n*((n:ℝ)*T)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
        hp (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hAn : A^n ≤ Real.exp ((n:ℝ)*φ x)+‖f x‖^n := by
    by_cases he : ‖f x‖ ≤ Real.exp (φ x)
    · dsimp [A]
      rw [max_eq_right he,←Real.exp_nat_mul]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    · dsimp [A]
      rw [max_eq_left (le_of_not_ge he)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have he : A^n*((n:ℝ)*T)^j = T^j*(n:ℝ)^j*A^n := by rw [mul_pow]; ring
  rw [he] at hreal
  exact hreal.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    hAn (pow_nonneg hA _) (by positivity))

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_TransverseZeroKernel
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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_add {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y + v y) x =
      laplaceBeltrami g u x + laplaceBeltrami g v x := by
  have h := congrArg Complex.re (complexLaplaceBeltrami_add
    (Complex.ofRealCLM.contMDiff.comp hu) (Complex.ofRealCLM.contMDiff.comp hv) g x)
  simpa only [complexLaplaceBeltrami, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Function.comp_def, Complex.ofRealCLM_apply, Pi.sub_apply] using h

end

open Set Filter Function Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProductFrequencyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace'
local instance threeModelContinuousSMul'_re8701e_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_re8701e_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
lemma threeComplexPower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℂ) ∞ (threeComplexPower a b k) := by
  let L : ThreeAmbient →L[ℝ] ℂ := (planarLinear a b).comp (WithLp.fstL 2 ℝ (Euclidean 3) ℂ)
  let R : ThreeAmbient →L[ℝ] ℂ := WithLp.sndL 2 ℝ (Euclidean 3) ℂ
  have hh : ContDiff ℝ ∞ (fun x : ThreeAmbient => (L x)^k*(R x)^k) :=
    (L.contDiff.pow k).mul (R.contDiff.pow k)
  have hc := hh.contMDiff.comp (I:=𝓘(ℝ,ThreeModel)) threeImmersion_smooth
  exact hc
lemma threePower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threePower a b k) :=
  Complex.reCLM.contMDiff.comp (threeComplexPower_smooth a b k)
attribute [local instance] OAI.YauCounterexamples.sphereN_dimension_fact
lemma threeComplexPower_chart (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    threeComplexPower a b k ∘ (chartAt ThreeModel p).symm =
      fun z => productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
        productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z := by
  funext y
  have hh := congrFun (three_chart_symm p) y
  have h₁ := congrArg (fun q : ThreeAmbient => q.fst) hh
  have h₂ := congrArg (fun q : ThreeAmbient => q.snd) hh
  change (((chartAt ThreeModel p).symm y).1:Euclidean 3) =
    roundChart (p.1:Euclidean 3) (sphereFrame p.1) y.fst at h₁
  change (((chartAt ThreeModel p).symm y).2:ℂ) =
    roundChart (p.2:ℂ) (unitSphereFrame (n:=1) p.2) y.snd at h₂
  simp only [Function.comp_apply,threeComplexPower,h₁,h₂]
  simp only [productSphere_fstPower,productSphere_sndPower,Function.comp_apply]
  rw [complexIdentityPlanar]
  rfl
end


section
open Set Filter
open scoped Topology

lemma productFrequency_nonneg (k : ℕ) : 0 ≤ productFrequency k := by
  unfold productFrequency
  positivity
lemma productWaveFrequency_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ) ≤ productWaveFrequency k ∧ productWaveFrequency k ≤ 2*(k:ℝ) := by
  have hp : (1:ℝ)≤k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  have hs0 := Real.sqrt_nonneg (productFrequency k+1)
  dsimp [productFrequency] at hs hs0 ⊢
  unfold productWaveFrequency productFrequency
  constructor <;> nlinarith [sq_nonneg ((k:ℝ)-1)]
end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeFirstNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
attribute [local instance] OAI.YauCounterexamples.threeFirstNormedSpace
local instance threeFirstContinuousSMul_re8701e_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.sphereFirst_dimension_fact
lemma threeComplexPower_chart_smooth (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeComplexPower_chart]
  exact (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma productAxis_coord (i : Fin 3) (x : Euclidean 3) : inner ℝ (productAxis i) x = x i := by
  simp [productAxis,EuclideanSpace.inner_single_left]
lemma productA_re (x : Euclidean 3) : (productA x).re=x 0 := by simp [productA,planarLinear,productAxis_coord]
lemma productA_im (x : Euclidean 3) : (productA x).im=x 1 := by simp [productA,planarLinear,productAxis_coord]
lemma productB_re (x : Euclidean 3) : (productB x).re=x 0 := by simp [productB,planarLinear,productAxis_coord]
lemma productB_im (x : Euclidean 3) : (productB x).im=x 2 := by simp [productB,planarLinear,productAxis_coord]
lemma threeCoupled_eq (r : ℝ) (k : ℕ) : threeCoupled r k =
    fun p => threePower (productAxis 0) (productAxis 1) k p+r^k*threePower (productAxis 0) (productAxis 2) k p := by
  funext p
  simp only [threeCoupled,threeCoupledComplex,add_mul,mul_assoc,Complex.add_re,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul,threePower,threeComplexPower,productA,productB]
attribute [local instance] OAI.YauCounterexamples.threeCoupledNormedSpace
local instance threeCoupledContinuousSMul_re8701e_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_smooth (r : ℝ) (k : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeCoupled r k) := by
  rw [threeCoupled_eq]
  exact (threePower_smooth _ _ _).add (contMDiff_const.mul (threePower_smooth _ _ _))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ThreeNoncancelNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
lemma productSphere_norm_sq (p : Sphere 2) : (p:Euclidean 3) 0^2+(p:Euclidean 3) 1^2+(p:Euclidean 3) 2^2=1 := by
  have hn : ‖(p:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (p:Euclidean 3)
  simpa [hn,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,add_assoc] using hh.symm

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeGlobalRadius_lower (p : ThreeManifold) : (1/200:ℝ) ≤ threeGlobalRadius p := by
  have ha := Complex.normSq_eq_norm_sq (productA p.1)
  have hb := Complex.normSq_eq_norm_sq (productB p.1)
  simp only [Complex.normSq_apply,productA_re,productA_im,productB_re,productB_im] at ha hb
  have hs := productSphere_norm_sq p.1
  by_contra hn
  have hn : threeGlobalRadius p < 1/200 := lt_of_not_ge hn
  have hA := (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  have hB := (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  dsimp [threeCouplingRadius] at hB
  have hB' : ‖productB p.1‖<1/2 := by linarith
  have hA' : ‖productA p.1‖<1/2 := by linarith
  nlinarith [norm_nonneg (productA p.1), norm_nonneg (productB p.1),sq_nonneg ((p.1:Euclidean 3) 0)]
lemma threeGlobalRadius_pos (p : ThreeManifold) : 0<threeGlobalRadius p :=
  lt_of_lt_of_le (by norm_num) (threeGlobalRadius_lower p)
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

lemma real_smooth_add_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f+h) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖+‖iteratedFDeriv ℝ j h x‖ := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  rw [iteratedFDeriv_add_apply (hf.of_le hj).contDiffAt (hh.of_le hj).contDiffAt]
  exact norm_add_le _ _

end


section
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

lemma real_power_variable_weighted_jets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C > 0, ∀ k : ℕ, 1≤k → ∀ x ∈ K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^k).re) x‖ ≤
        C*(k:ℝ)^j*(Real.exp (productWaveFrequency k*φ x)+‖f x‖^k) := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  obtain ⟨C,hC,hjet⟩ := real_power_weighted_jets hf hK (fun _ => -2*D)
    continuousOn_const h
  refine ⟨C,hC,?_⟩
  intro k hk x hx j hj
  have hp : (0:ℝ)≤k := Nat.cast_nonneg _
  have hν := productWaveFrequency_bounds hk
  have hν0 : 0≤productWaveFrequency k := hp.trans hν.1
  have hm : -D≤φ x := by
    have hb := hB x hx
    rw [Real.norm_eq_abs] at hb
    exact (neg_le_neg (le_max_left B 0)).trans ((neg_le_neg hb).trans (neg_abs_le _))
  have he : Real.exp ((k:ℝ)*(-2*D))≤Real.exp (productWaveFrequency k*φ x) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = (2*(k:ℝ))*(-D) := by ring
      _ ≤ productWaveFrequency k*(-D) := mul_le_mul_of_nonpos_right hν.2 (neg_nonpos.mpr hD)
      _ ≤ _ := mul_le_mul_of_nonneg_left hm hν0
  exact (hjet k x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add he le_rfl) (by positivity))

lemma threeWeight_pos (φ : ThreeManifold → ℝ) (k : ℕ) (p : ThreeManifold) :
    0<threeWeight φ k p := add_pos_of_pos_of_nonneg (Real.exp_pos _)
      (pow_nonneg (threeGlobalRadius_pos p).le _)

lemma threeCoupled_split_powers (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    threeCoupled r k p =
      ((threeComplexPower (productAxis 0) (productAxis 1) 1 p)^k).re+
      (((r:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p)^k).re := by
  simp only [threeCoupled,threeCoupledComplex,threeComplexPower,pow_one,mul_pow,
    Complex.add_re,add_mul,productA,productB,mul_assoc]

attribute [local instance] OAI.YauCounterexamples.threeWeightedNormedSpace
local instance threeWeightedContinuousSMul_re8701e_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem threeCoupled_weighted_chart_jets {φ : ThreeManifold → ℝ}
    (hφ : Continuous φ) (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h : ℕ) :
    ∃ C>0, ∀ k : ℕ, 1≤k → ∀ x ∈ K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (threeCoupled threeCouplingRadius k ∘
        (chartAt ThreeModel p).symm) x‖ ≤ C*(k:ℝ)^j*
          threeWeight φ k ((chartAt ThreeModel p).symm x) := by
  let a := threeComplexPower (productAxis 0) (productAxis 1) 1 ∘ (chartAt ThreeModel p).symm
  let b := fun x => (threeCouplingRadius:ℂ)*
    (threeComplexPower (productAxis 0) (productAxis 2) 1 ∘ (chartAt ThreeModel p).symm) x
  have ha : ContDiff ℝ ∞ a := threeComplexPower_chart_smooth _ _ _ _
  have hb : ContDiff ℝ ∞ b := contDiff_const.mul (threeComplexPower_chart_smooth _ _ _ _)
  have hc : ContinuousOn (φ ∘ (chartAt ThreeModel p).symm) K :=
    (hφ.comp (three_chart_symm_continuous p)).continuousOn
  obtain ⟨A,hA,haj⟩ := real_power_variable_weighted_jets ha hK _ hc h
  obtain ⟨B,hB,hbj⟩ := real_power_variable_weighted_jets hb hK _ hc h
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro k hk x hx j hj
  have he : threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm =
      (fun y => (a y^k).re)+(fun y => (b y^k).re) := by
    funext y
    exact threeCoupled_split_powers _ _ _
  have han : ‖a x‖≤threeGlobalRadius ((chartAt ThreeModel p).symm x) := by
    dsimp [a,threeComplexPower]
    simp only [pow_one,norm_mul,Circle.norm_coe,mul_one]
    exact le_max_left _ _
  have hbn : ‖b x‖≤threeGlobalRadius ((chartAt ThreeModel p).symm x) := by
    dsimp [b,threeComplexPower]
    simp only [pow_one,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0<threeCouplingRadius by norm_num [threeCouplingRadius])]
    exact le_max_right _ _
  have hja := (haj k hk x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) han k)) (by positivity))
  have hjb := (hbj k hk x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hbn k)) (by positivity))
  rw [he]
  exact (real_smooth_add_jet_bound (Complex.reCLM.contDiff.comp (ha.pow k))
    (Complex.reCLM.contDiff.comp (hb.pow k)) j x).trans
    (calc
      _ ≤ A*(k:ℝ)^j*threeWeight φ k ((chartAt ThreeModel p).symm x)+
          B*(k:ℝ)^j*threeWeight φ k ((chartAt ThreeModel p).symm x) := add_le_add hja hjb
      _ = _ := by ring)
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
attribute [local instance] OAI.YauCounterexamples.threeLiftNormedSpace
local instance threeLiftContinuousSMul_re8701e_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeWaveLift_smooth {u : NormalWaveSpace → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeWaveLift u) :=
  contMDiff_manifoldChartPush _ (hu.comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
attribute [local instance] OAI.YauCounterexamples.threeGlobalResidualNormedSpace
local instance threeGlobalResidualContinuousSMul_re8701e_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_chart_pullback_smooth {f : ThreeManifold → ℝ}
    (hf : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ f) (p : ThreeManifold) :
    ContDiff ℝ ∞ (f ∘ (chartAt ThreeModel p).symm) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact contDiffAt_inChart hf p (by rw [three_chart_target]; trivial)
lemma threeWeight_ge_exp (φ : ThreeManifold → ℝ) (k : ℕ) (p : ThreeManifold) :
    Real.exp (productWaveFrequency k*φ p) ≤ threeWeight φ k p :=
  le_add_of_nonneg_right (pow_nonneg (threeGlobalRadius_pos p).le _)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

attribute [local instance] OAI.YauCounterexamples.threeAssemblyNormedSpace
local instance threeAssemblyContinuousSMul_re8701e_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
theorem three_wave_background_chart_bounds_oai
    (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set (ThreeManifold)} (hF : IsClosed F)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    {φ : ThreeManifold → ℝ} (hφ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ φ)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ q∈F, threeGlobalLog q+δ ≤ φ q)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K)
    (r : ℝ) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
    ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ closedBall 0 r →
      (∀ y : NormalWaveSpace, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp (productWaveFrequency n*φ (threeNormalInv y)) ∧
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
          productFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
          Real.exp (productWaveFrequency n*φ (threeNormalInv y))) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius n+threeWaveLift u) ∘
          (chartAt ThreeModel p).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*threeWeight φ n ((chartAt ThreeModel p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (threeCoupled threeCouplingRadius n+threeWaveLift u) q+
          productFrequency n*(threeCoupled threeCouplingRadius n+threeWaveLift u) q) ∘
          (chartAt ThreeModel p).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*threeWeight φ n ((chartAt ThreeModel p).symm y) := by
  obtain ⟨C₁,hC₁,hback⟩ := threeCoupled_weighted_chart_jets hφ.continuous p hK m
  obtain ⟨N,hN,hres⟩ := threeCoupled_global_residual_rapid_decay g hF hext hφ.continuous hδ hgap p hK m D
  obtain ⟨T,hT,htransfer⟩ := three_wave_lift_jets g p hK r m
  let C := C₁+1+T*C₀
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast ((le_max_right N 1).trans hn)
  have hn0 : (0:ℝ)<n := zero_lt_one.trans_le hn1
  have hnD : 0 < (n:ℝ)^D := pow_pos hn0 _
  have hn4 : (1:ℝ)≤(n:ℝ)^4 := one_le_pow₀ hn1
  intro u hu hc hs hj y hy j hjm
  let W := threeWeight φ n ((chartAt ThreeModel p).symm y)
  have hW : 0 < W := threeWeight_pos φ n _
  have hE := threeWeight_ge_exp φ n ((chartAt ThreeModel p).symm y)
  let B := fun j q => C₀*(n:ℝ)^(j+4)*Real.exp (productWaveFrequency n*φ q)
  let R := fun q => C₀*((n:ℝ)^(D+1))⁻¹*Real.exp (productWaveFrequency n*φ q)
  have hlift := htransfer u hu hc hs B (fun j q => by dsimp [B]; positivity)
    R (fun q => by dsimp [R]; positivity) (productFrequency n)
    (fun x j hjm i hij => (hj x i (hij.trans hjm)).1.trans (by
      dsimp [B]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega : i+4≤j+4)) hC₀.le)
        (Real.exp_pos _).le))
    (fun x j hjm => (hj x j hjm).2) y hy j hjm
  have hback' := hback n (by exact_mod_cast hn1) y hy j hjm
  have hres' := hres n ((le_max_left _ _).trans hn) y hy j hjm
  have hsmooth := threeWaveLift_smooth hu hc
  have hsum : ((threeCoupled threeCouplingRadius n+threeWaveLift u) ∘
      (chartAt ThreeModel p).symm)=
      (threeCoupled threeCouplingRadius n ∘ (chartAt ThreeModel p).symm)+
      (threeWaveLift u ∘ (chartAt ThreeModel p).symm) := rfl
  have hroundsm := threeCoupled_smooth threeCouplingRadius n
  constructor
  · rw [hsum]
    apply (real_smooth_add_jet_bound (three_chart_pullback_smooth hroundsm p)
      (three_chart_pullback_smooth hsmooth p) j y).trans
    apply (add_le_add hback' hlift.1).trans
    have hnj : (n:ℝ)^j ≤ (n:ℝ)^(j+4) := pow_le_pow_right₀ hn1 (by omega)
    calc
      _ ≤ C₁*(n:ℝ)^(j+4)*W+T*(C₀*(n:ℝ)^(j+4)*W) :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnj hC₁.le) hW.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) hT.le)
      _ ≤ C*(n:ℝ)^(j+4)*W := by dsimp [C]; nlinarith [mul_nonneg (pow_nonneg hn0.le (j+4)) hW.le]
  · let R₁ := fun q => laplaceBeltrami g (threeCoupled threeCouplingRadius n) q+
      productFrequency n*threeCoupled threeCouplingRadius n q
    let R₂ := fun q => laplaceBeltrami g (threeWaveLift u) q+
      productFrequency n*threeWaveLift u q
    have hR₁ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ R₁ :=
      (contMDiff_laplaceBeltrami hroundsm g).add (contMDiff_const.mul hroundsm)
    have hR₂ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ R₂ :=
      (contMDiff_laplaceBeltrami hsmooth g).add (contMDiff_const.mul hsmooth)
    have he : ((fun q => laplaceBeltrami g
        (threeCoupled threeCouplingRadius n+threeWaveLift u) q+
        productFrequency n*(threeCoupled threeCouplingRadius n+threeWaveLift u) q) ∘
        (chartAt ThreeModel p).symm)=
        (R₁ ∘ (chartAt ThreeModel p).symm)+(R₂ ∘ (chartAt ThreeModel p).symm) := by
      funext x
      have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
        le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
      have hadd := laplaceBeltrami_add (hroundsm.of_le h2) (hsmooth.of_le h2) g
        ((chartAt ThreeModel p).symm x)
      dsimp only [Function.comp_apply,Pi.add_apply,R₁,R₂]
      change laplaceBeltrami g (fun y => threeCoupled threeCouplingRadius n y+threeWaveLift u y)
        ((chartAt ThreeModel p).symm x) + _ = _
      rw [hadd]
      ring
    rw [he]
    apply (real_smooth_add_jet_bound (three_chart_pullback_smooth hR₁ p)
      (three_chart_pullback_smooth hR₂ p) j y).trans
    apply (add_le_add hres' hlift.2).trans
    have hinv : ((n:ℝ)^(D+1))⁻¹ ≤ ((n:ℝ)^D)⁻¹ :=
      inv_anti₀ hnD (pow_le_pow_right₀ hn1 (by omega))
    calc
      _ ≤ ((n:ℝ)^D)⁻¹*W+T*(C₀*((n:ℝ)^D)⁻¹*W) :=
        add_le_add (mul_le_mul_of_nonneg_left hE (by positivity))
          (mul_le_mul_of_nonneg_left (mul_le_mul
            (mul_le_mul_of_nonneg_left hinv hC₀.le) hE
            (Real.exp_pos _).le (by positivity)) hT.le)
      _ = (1+T*C₀)/(n:ℝ)^D*W := by rw [div_eq_mul_inv]; ring
      _ ≤ C*(n:ℝ)^4/(n:ℝ)^D*W := by
        apply mul_le_mul_of_nonneg_right _ hW.le
        apply div_le_div_of_nonneg_right _ hnD.le
        calc
          1+T*C₀ ≤ C := by dsimp [C]; linarith
          _ ≤ C*(n:ℝ)^4 := le_mul_of_one_le_right (by dsimp [C]; positivity) hn4

end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_wave_background_chart_bounds_oai := @OAI.YauCounterexamples.three_wave_background_chart_bounds_oai
