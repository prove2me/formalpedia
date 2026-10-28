-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_supported_separating_tensor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:31:12.537646+00:00
-- url     : https://prove2.me/submissions/c1cfa5c6-191b-4bc3-8e32-b5ea988ac6db

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BundleRankOne
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma contMDiffAt_bundleRankOne (g : SmoothMetric E M)
    {V : ∀ x : M, TangentSpace 𝓘(ℝ,E) x} {p : M}
    (hv : ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun x => TotalSpace.mk' E x (V x)) p) :
    ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (bundleRankOne g V x)) p := by
  rw [contMDiffAt_section p] at hv ⊢
  have hg := (contMDiffAt_localMetricFlat g p).clm_apply hv
  have hs : ContDiff ℝ ∞ (fun z : (E →L[ℝ] ℝ) × E => z.1.smulRight z.2) :=
    contDiff_fst.smulRight contDiff_snd
  have hprod := hg.prodMk hv
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hprod
  have hh := hs.contMDiff.contMDiffAt.comp p hprod
  apply hh.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ p)] with x hx
  simp only [Function.comp_def,hom_trivializationAt_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hx hx]
  ext w
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    bundleRankOne,ContinuousLinearMap.smulRight_apply,map_smul,
    localMetricFlat_pairing g p x hx,
    Trivialization.symm_apply_apply_mk _ hx,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply]

omit [FiniteDimensional ℝ E] in
lemma contMDiff_bundleId :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,E) x))) := by
  intro p
  rw [contMDiffAt_section p]
  apply (contMDiffAt_const (c := ContinuousLinearMap.id ℝ E)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ p)] with x hx
  simp only [hom_trivializationAt_apply,ContinuousLinearMap.inCoordinates_eq hx hx]
  ext w
  simp

lemma contMDiffAt_bundleTransverse (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) {p : M}
    (hp : metricGradient g u p ≠ 0) :
    ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (bundleTransverse g u x)) p := by
  have hv := contMDiff_metricGradient g hu
  have hq := (g.contMDiff p).clm_bundle_apply₂ (hv p) (hv p)
  rw [contMDiffAt_totalSpace] at hq
  exact (contMDiff_bundleId p).sub_section
    ((hq.2.inv₀ (by simpa using (g.pos p _ hp).ne')).smul_section (contMDiffAt_bundleRankOne g (hv p)))

theorem supportedPinningTensor_smooth (g : SmoothMetric E M) {u v χ : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) {A : Set M}
    (hA : IsOpen A) (hs : tsupport χ ⊆ A) (hn : ∀ x ∈ A, metricGradient g u x ≠ 0) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (supportedPinningTensor g u v χ x)) := by
  apply ContMDiffOn.smul_section_of_tsupport (hχ.contMDiffOn) hA hs
  intro x hx
  have hP := contMDiffAt_bundleTransverse g hu (hn x hx)
  have hp := hP.clm_bundle_apply (contMDiff_metricGradient g hv x)
  have hq := (g.contMDiff x).clm_bundle_apply₂ hp hp
  rw [contMDiffAt_totalSpace] at hq
  exact ((contMDiffAt_bundleRankOne g hp).sub_section
    ((hq.2.div_const 2).smul_section hP)).contMDiffWithinAt
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearTransverse
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma bilinearTransverse_apply (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) :
    bilinearTransverse G a b = b - ((G a a)⁻¹ * G a b) • a := by
  simp [bilinearTransverse,smul_smul]
lemma bilinearTransverse_kernel (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E} (ha : G a a ≠ 0) :
    bilinearTransverse G a a = 0 := by
  simp [bilinearTransverse_apply,inv_mul_cancel₀ ha]
lemma bilinearTransverse_orthogonal (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E}
    (ha : G a a ≠ 0) (b : E) : G a (bilinearTransverse G a b) = 0 := by
  rw [bilinearTransverse_apply,map_sub,map_smul,smul_eq_mul]
  field_simp
  ring
lemma bilinearTransverse_pair (G : E →L[ℝ] E →L[ℝ] ℝ)
    {a : E} (ha : G a a ≠ 0) (b : E) :
    G b (bilinearTransverse G a b) =
      G (bilinearTransverse G a b) (bilinearTransverse G a b) := by
  conv_rhs => lhs; rw [bilinearTransverse_apply]
  simp only [map_sub,map_smul,sub_apply,smul_apply,
    smul_eq_mul,bilinearTransverse_orthogonal G ha b,mul_zero,sub_zero]
lemma bilinearTransverse_trace [FiniteDimensional ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E} (ha : G a a ≠ 0) :
    LinearMap.trace ℝ E (bilinearTransverse G a).toLinearMap =
      (Module.finrank ℝ E : ℝ) - 1 := by
  change LinearMap.trace ℝ E ((LinearMap.id : E →ₗ[ℝ] E) -
    (G a a)⁻¹ • (G a).toLinearMap.smulRight a) = _
  rw [map_sub,map_smul,LinearMap.trace_id,LinearMap.trace_smulRight,smul_eq_mul]
  change (Module.finrank ℝ E : ℝ) - (G a a)⁻¹ * G a a = _
  rw [inv_mul_cancel₀ ha]
lemma bilinearPinning_kernel (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) {a : E} (ha : G a a ≠ 0) (b : E) :
    bilinearPinning G a b a = 0 := by
  simp only [bilinearPinning,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [hs,bilinearTransverse_orthogonal G ha,bilinearTransverse_kernel G ha]
  simp
lemma bilinearPinning_trace [FiniteDimensional ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ) {a : E} (ha : G a a ≠ 0)
    (b : E) (hd : Module.finrank ℝ E = 3) :
    LinearMap.trace ℝ E (bilinearPinning G a b).toLinearMap = 0 := by
  change LinearMap.trace ℝ E ((G (bilinearTransverse G a b)).toLinearMap.smulRight _ -
    (G _ _ / 2) • (bilinearTransverse G a).toLinearMap) = _
  rw [map_sub,map_smul,LinearMap.trace_smulRight,bilinearTransverse_trace G ha,hd]
  norm_num
lemma bilinearPinning_quadratic (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) {a : E} (ha : G a a ≠ 0) (b : E) :
    G b (bilinearPinning G a b b) =
      (G (bilinearTransverse G a b) (bilinearTransverse G a b))^2 / 2 := by
  simp only [bilinearPinning,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,map_sub,map_smul,smul_eq_mul]
  rw [hs (bilinearTransverse G a b) b,bilinearTransverse_pair G ha]
  ring
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_SupportedPinningTensor
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma supportedPinningTensor_eq (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M) :
    supportedPinningTensor g u v χ x =
      χ x • bilinearPinning (E := E) (g.inner x) (metricGradient g u x) (metricGradient g v x) := rfl

lemma supportedPinningTensor_kernel (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hn : χ x ≠ 0 → metricGradient g u x ≠ 0) :
    supportedPinningTensor g u v χ x (metricGradient g u x) = 0 := by
  rw [supportedPinningTensor_eq]
  by_cases hχ : χ x = 0
  · simp only [hχ, zero_smul]
    rfl
  have ha := (g.pos x _ (hn hχ)).ne'
  change χ x • (bilinearPinning (E := E) _ _ _ _) = 0
  erw [bilinearPinning_kernel (E := E) _ (g.symm x) ha,smul_zero]

lemma supportedPinningTensor_trace (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hn : χ x ≠ 0 → metricGradient g u x ≠ 0) (hd : Module.finrank ℝ E = 3) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,E) x)
      (supportedPinningTensor g u v χ x).toLinearMap = 0 := by
  rw [supportedPinningTensor_eq]
  by_cases hχ : χ x = 0
  · simp only [hχ, zero_smul]
    change LinearMap.trace ℝ E (0 : E →ₗ[ℝ] E) = 0
    exact map_zero _
  have ha := (g.pos x _ (hn hχ)).ne'
  change LinearMap.trace ℝ _ (χ x • (bilinearPinning (E := E) _ _ _).toLinearMap) = 0
  erw [map_smul,bilinearPinning_trace (E := E) _ ha _ hd,smul_zero]

lemma supportedPinningTensor_quadratic (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hn : χ x ≠ 0 → metricGradient g u x ≠ 0) :
    g.inner x (metricGradient g v x) (supportedPinningTensor g u v χ x (metricGradient g v x)) =
      χ x / 2 * (g.inner x (bundleTransverse g u x (metricGradient g v x))
        (bundleTransverse g u x (metricGradient g v x)))^2 := by
  rw [supportedPinningTensor_eq]
  by_cases hχ : χ x = 0
  · simp only [hχ, zero_smul, zero_div, zero_mul]
    change (g.inner x (metricGradient g v x)) 0 = 0
    exact map_zero _
  have ha := (g.pos x _ (hn hχ)).ne'
  change (show E →L[ℝ] ℝ from g.inner x (metricGradient g v x))
      (χ x • bilinearPinning (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
        (metricGradient g u x) (metricGradient g v x) (show E from metricGradient g v x)) = _
  erw [map_smul, smul_eq_mul]
  have he := bilinearPinning_quadratic (E := E)
    (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x) (g.symm x) ha (metricGradient g v x)
  change g.inner x (metricGradient g v x)
    (bilinearPinning (E := E) (g.inner x) (metricGradient g u x) (metricGradient g v x)
      (metricGradient g v x)) = _ at he
  calc
    _ = χ x * ((g.inner x (bundleTransverse g u x (metricGradient g v x))
      (bundleTransverse g u x (metricGradient g v x)))^2 / 2) :=
        congrArg (fun r : ℝ => χ x * r) he
    _ = _ := by ring

lemma supportedPinningTensor_quadratic_pos (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hχ : 0 < χ x) (hn : metricGradient g u x ≠ 0)
    (hp : bundleTransverse g u x (metricGradient g v x) ≠ 0) :
    0 < g.inner x (metricGradient g v x)
      (supportedPinningTensor g u v χ x (metricGradient g v x)) := by
  rw [supportedPinningTensor_quadratic g u v χ x (fun _ => hn)]
  exact mul_pos (div_pos hχ (by norm_num)) (sq_pos_of_pos (g.pos x _ hp))
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ExistsSupportedPinningBump
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [CompactSpace M]

lemma exists_supported_pinning_bump {A : Set M} (hA : IsOpen A) {x : M} (hx : x ∈ A) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧
      tsupport χ ⊆ A ∧ (∀ y, 0 ≤ χ y) ∧ χ x = 1 := by
  obtain ⟨V,hV,hxV,hVA⟩ := normal_exists_closure_subset isClosed_singleton hA
    (singleton_subset_iff.mpr hx)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ,E)) (n := ⊤) isClosed_singleton (t := V)
    (by simpa only [hV.interior_eq] using hxV)
  refine ⟨χ,χ.contMDiff,?_,fun y => (hχb y).1,?_⟩
  · apply (closure_mono (show Function.support (fun y => χ y) ⊆ V from ?_)).trans hVA
    intro y hy
    by_contra hn
    exact hy (hχ0 y hn)
  · exact hχ1.self_of_nhdsSet x (mem_singleton x)

theorem exists_supported_separating_tensor_oai [MeasurableSpace M] [OpensMeasurableSpace M]
    (μ : Measure M) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) {A : Set M}
    (hA : IsOpen A) (hn : ∀ x ∈ A, metricGradient g u x ≠ 0)
    {x : M} (hx : x ∈ A) (hp : bundleTransverse g u x (metricGradient g v x) ≠ 0)
    (hd : Module.finrank ℝ E = 3) :
    ∃ χ : M → ℝ, tsupport χ ⊆ A ∧
      ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
        (fun y => TotalSpace.mk' (E →L[ℝ] E) y (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,E) y)
        (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
      0 < ∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  obtain ⟨χ,hχ,hs,hχp,hχx⟩ := exists_supported_pinning_bump (E := E) hA hx
  have hnp (y : M) (hy : χ y ≠ 0) : metricGradient g u y ≠ 0 :=
    hn y (hs (subset_closure hy))
  have hK := supportedPinningTensor_smooth g hu hv hχ hA hs hn
  have hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun y => g.inner y (metricGradient g v y)
      (supportedPinningTensor g u v χ y (metricGradient g v y))) := by
    intro y
    have hh := (g.contMDiff y).clm_bundle_apply₂ (contMDiff_metricGradient g hv y)
      ((hK y).clm_bundle_apply (contMDiff_metricGradient g hv y))
    rw [contMDiffAt_totalSpace] at hh
    exact hh.2
  refine ⟨χ,hs,hK,fun y => supportedPinningTensor_trace g u v χ y (hnp y) hd,
    fun y => supportedPinningTensor_kernel g u v χ y (hnp y),?_⟩
  have hnonneg : 0 ≤ (fun y => g.inner y (metricGradient g v y)
      (supportedPinningTensor g u v χ y (metricGradient g v y))) := by
    intro y
    change 0 ≤ g.inner y (metricGradient g v y)
      (supportedPinningTensor g u v χ y (metricGradient g v y))
    rw [supportedPinningTensor_quadratic g u v χ y (hnp y)]
    exact mul_nonneg (div_nonneg (hχp y) (by norm_num)) (sq_nonneg _)
  exact hq.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) hnonneg
    (supportedPinningTensor_quadratic_pos g u v χ x (by rw [hχx]; norm_num)
      (hn x hx) hp).ne'
end YauCounterexamples

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.exists_supported_separating_tensor_oai.{u_1, u_2} := @OAI.YauCounterexamples.exists_supported_separating_tensor_oai.{u_1, u_2}
