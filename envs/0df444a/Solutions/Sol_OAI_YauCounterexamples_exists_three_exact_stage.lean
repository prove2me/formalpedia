-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_exact_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:13:54.236888+00:00
-- url     : https://prove2.me/submissions/54fcdfcc-246d-48e0-adbe-b9b078a4091c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_global_cutoff_raw_controls
import Theorems.Thm_OAI_YauCounterexamples_cutoff_exactification_in_smooth_neighborhood
import Theorems.Thm_OAI_YauCounterexamples_exists_three_scalar_producer
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas
import Theorems.Thm_OAI_YauCounterexamples_three_annular_projection_uniform
import Theorems.Thm_OAI_YauCounterexamples_three_clean_conjugating_margin
import Theorems.Thm_OAI_YauCounterexamples_three_cutoff_control_bounds
import Theorems.Thm_OAI_YauCounterexamples_three_wave_exterior_germ
import Theorems.Thm_OAI_YauCounterexamples_three_wave_residual_support

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ReciprocalIteratedDerivativeBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

lemma geometric_product_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
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

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SmoothExtension
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

lemma smooth_extension_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ∃ F : E → F, ContDiff ℝ ∞ F ∧ f =ᶠ[𝓝 x] F := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hx) hf
  exact ⟨F,hF,he.filter_mono (nhds_le_nhdsSet (mem_singleton x))⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace YauCounterexamples.SignTests

theorem oppositeSet_pos_mul {X M : Type*} (D : Set X) (a b : X → M)
    (f q : M → ℝ) (hq : ∀ y, 0 < q y) :
    oppositeSet D a b (fun y => q y * f y) = oppositeSet D a b f := by
  ext x
  simp only [oppositeSet, mem_ofPred_eq]
  have h : (q (a x) * f (a x)) * (q (b x) * f (b x)) =
      (q (a x) * q (b x)) * (f (a x) * f (b x)) := by ring
  rw [h, mul_neg_iff]
  simp [not_lt.mpr (mul_pos (hq (a x)) (hq (b x))).le,
    mul_pos (hq (a x)) (hq (b x))]

theorem signCertificate_pos_mul {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (f q : (ι → ℝ) → ℝ)
    (hq : ∀ x, 0 < q x) :
    signCertificate P d (fun x => q x * f x) = signCertificate P d f := by
  unfold signCertificate signMass
  simp_rw [oppositeSet_pos_mul _ _ _ f q hq]

end YauCounterexamples.SignTests
end

open Set Function MeasureTheory
open scoped ENNReal
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma geometric_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hx hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hO hx hg
  have hb := geometric_product_jet_bound hf' hg' x h hF hG hR hS
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj => (hge.iteratedFDeriv ℝ j).self_of_nhds ▸ hgj j hj)
  change ‖iteratedFDeriv ℝ h (f*g) x‖ ≤ _
  rw [(hfe.mul hge).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hb


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
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_AnnularRelativeMargin
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}

lemma coordinateGradientPair_congr_nhds_cutoff {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] (g : SmoothMetric E M)
    {f h : M → ℝ} {p : M} (he : f =ᶠ[𝓝 p] h) :
    coordinateGradientPair g f f p=coordinateGradientPair g h h p := by
  let c := chartAt E p
  have hp := c.map_source (mem_chart_source E p)
  have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [c.left_inv (mem_chart_source E p)] using (c.continuousAt_symm hp).tendsto
  have hd := (he.comp_tendsto ht).fderiv_eq (𝕜:=ℝ)
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ (f ∘ c.symm) (c p) _ *
    fderiv ℝ (f ∘ c.symm) (c p) _) = _
  rw [hd]


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CutoffExactificationSmoothNeighborhood
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma constant_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  intro j hj
  have hh := geometric_product_jet_bound_on hO hx hf hg j hF hG zero_le_one zero_le_one
    (fun k hk => by simpa only [one_pow,mul_one] using hfj k (hk.trans hj))
    (fun k hk => by simpa only [one_pow,mul_one] using hgj k (hk.trans hj))
  calc
    _ ≤ F*G*(1+1)^j := hh
    _ ≤ F*G*2^h := mul_le_mul_of_nonneg_left
      (by norm_num only [one_add_one_eq_two]; exact pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hF hG)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma raw_jets_of_near_one {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y-1) x‖ ≤ ε) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ 1+ε := by
  intro j hj
  by_cases hj0 : j=0
  · subst j
    simp only [norm_iteratedFDeriv_zero] at hJ ⊢
    have hv := hJ 0 (Nat.zero_le h)
    simp only [norm_iteratedFDeriv_zero] at hv
    rw [Real.norm_eq_abs] at hv ⊢
    apply (sq_le_sq₀ (abs_nonneg _) (add_nonneg zero_le_one hε)).mp
    rw [sq_abs]
    have hbound := (sq_le_sq₀ (abs_nonneg (f x-1)) hε).mpr hv
    rw [sq_abs] at hbound
    have hupper := (abs_le.mp hv).2
    nlinarith
  · have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    have hb := hJ j hj
    rw [fun_iteratedFDeriv_sub_apply ((hf.contDiffAt (hO.mem_nhds hx)).of_le hle)
      contDiffAt_const,iteratedFDeriv_const_of_ne hj0,Pi.zero_apply,sub_zero] at hb
    linarith

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
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CutoffFactorCompactRaw
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
theorem cutoffFactor_compact_raw (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (m : ℕ) :
    ∃ C > 0, ∀ (v : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      ∀ y ∈ K, ∀ ε : ℝ, 0 ≤ ε →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E p).symm) y‖ ≤ ε) →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j
        ((fun x => cutoffFactor χ v x-1) ∘ (chartAt E p).symm) y‖ ≤ C*ε := by
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hχ' : ContDiffOn ℝ ∞ (χ ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart hχ p hy).contDiffWithinAt
  obtain ⟨A,hA,hAj⟩ := compact_raw_jet_bound hO hK hKt hχ' m
  refine ⟨2^m*A,by positivity,?_⟩
  intro v hv y hy ε hε hvJ j hj
  have hv' : ContDiffOn ℝ ∞ ((fun x => v x-1) ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart (hv.sub contMDiff_const) p hy).contDiffWithinAt
  have hp := constant_product_jet_bound_on hO (hKt hy) hχ' hv' m
    (zero_le_one.trans hA) hε (fun k hk => hAj k hk y hy) hvJ j hj
  simpa only [Function.comp_def,cutoffFactor,add_sub_cancel_left] using hp

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
open Filter
open scoped Topology

lemma inverseFrequency_zero : Tendsto inverseFrequency atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma inverseFrequency_pow_zero (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun n => inverseFrequency n ^ m) atTop (𝓝 0) := by
  simpa only [zero_pow hm] using inverseFrequency_zero.pow m

end

section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace'
local instance threeModelContinuousSMul'_re867e0_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_re867e0_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
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
end


open Set Filter Function Manifold
open scoped Topology ContDiff

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
lemma threeCoupled_eq (r : ℝ) (k : ℕ) : threeCoupled r k =
    fun p => threePower (productAxis 0) (productAxis 1) k p+r^k*threePower (productAxis 0) (productAxis 2) k p := by
  funext p
  simp only [threeCoupled,threeCoupledComplex,add_mul,mul_assoc,Complex.add_re,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul,threePower,threeComplexPower,productA,productB]
attribute [local instance] OAI.YauCounterexamples.threeCoupledNormedSpace
local instance threeCoupledContinuousSMul_re867e0_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_smooth (r : ℝ) (k : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeCoupled r k) := by
  rw [threeCoupled_eq]
  exact (threePower_smooth _ _ _).add (contMDiff_const.mul (threePower_smooth _ _ _))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_InverseFrequencyWeightedZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace
namespace YauCounterexamples

lemma inverseFrequency_weighted_zero (L C : ℝ) (h : ℕ) :
    Tendsto (fun n => (L*inverseFrequency n^(h+3))*(1+C)*(n:ℝ)^h) atTop (𝓝 0) := by
  have he : (fun n => L*(1+C)*inverseFrequency n^3) =ᶠ[atTop]
      (fun n => (L*inverseFrequency n^(h+3))*(1+C)*(n:ℝ)^h) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    symm
    calc
      _ = L*(1+C)*inverseFrequency n^3*((n:ℝ)⁻¹^h*(n:ℝ)^h) := by
        simp only [inverseFrequency,pow_add]; ring
      _ = _ := by rw [← mul_pow,inv_mul_cancel₀ hn0,one_pow,mul_one]
  apply Tendsto.congr' he
  simpa using (inverseFrequency_pow_zero 3 (by omega)).const_mul (L*(1+C))

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
local instance threeLiftContinuousSMul_re867e0_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeWaveLift_smooth {u : NormalWaveSpace → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeWaveLift u) :=
  contMDiff_manifoldChartPush _ (hu.comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _)
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
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
lemma threeNormalInv_isOpenMap : IsOpenMap threeNormalInv := by
  intro U hU
  change IsOpen (((chartAt ThreeModel threeProfileCenter).symm ∘ threeNormalEquiv) '' U)
  rw [image_comp]
  exact (chartAt ThreeModel threeProfileCenter).isOpen_image_symm_of_subset_target
    (threeNormalEquiv.toHomeomorph.isOpenMap U hU) (by rw [three_chart_target]; exact subset_univ _)
lemma threeNormalInv_closedBall_closed (r : ℝ) : IsClosed (threeNormalInv '' closedBall 0 r) :=
  ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalInv_continuous).isClosed
lemma exists_three_radial_cutoff {a b : ℝ} (hab : a<b) :
    ∃ χ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ χ ∧
      (∀ q, χ q∈Icc (0:ℝ) 1) ∧
      (∀ q∈threeNormalInv '' closedBall 0 a, χ q=1) ∧
      (∀ q∉threeNormalInv '' ball 0 b, χ q=0) := by
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,ThreeModel)) (n:=(⊤:ℕ∞)) (s:=threeNormalInv '' closedBall 0 a)
    (t:=threeNormalInv '' ball 0 b) (threeNormalInv_closedBall_closed a) (by
      rw [(threeNormalInv_isOpenMap _ isOpen_ball).interior_eq]
      exact image_mono (closedBall_subset_ball hab))
  exact ⟨χ,χ.contMDiff,hχrange,fun q hq => hχ1.self_of_nhdsSet q hq,hχ0⟩
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma three_coordinateGradientPair_pos_derivative_ne (g : SmoothMetric E M) (u : M → ℝ)
    (x : M) (hp : 0 < coordinateGradientPair g u u x) :
    fderiv ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0 := by
  intro hz
  simp [coordinateGradientPair,hz] at hp

lemma three_regular_quotient_at_zero (g : SmoothMetric E M) {u w : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w)
    (hw0 : ∀ x, w x ≠ 0) (x : M) (hxu : u x=0)
    (hp : 0 < coordinateGradientPair g u u x) :
    fderiv ℝ ((fun q => u q/w q) ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0 := by
  let c := chartAt E x
  have hxt : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hc : c.symm (c x)=x := c.left_inv (mem_chart_source E x)
  have hdu := (contDiffAt_inChart hu x hxt).differentiableAt (by simp)
  have hdw := (contDiffAt_inChart hw x hxt).differentiableAt (by simp)
  have hne : (w ∘ c.symm) (c x) ≠ 0 := by
    simpa only [Function.comp_apply,hc] using hw0 x
  have he := fderiv_fun_mul hdu (hdw.inv hne)
  change fderiv ℝ (fun y => (u ∘ c.symm) y/(w ∘ c.symm) y) (c x) ≠ 0
  simp only [div_eq_mul_inv]
  have he' : fderiv ℝ (fun y => (u ∘ c.symm) y*((w ∘ c.symm) y)⁻¹) (c x) =
      (u ∘ c.symm) (c x) • fderiv ℝ (w ∘ c.symm)⁻¹ (c x)+
      ((w ∘ c.symm) (c x))⁻¹ • fderiv ℝ (u ∘ c.symm) (c x) := he
  rw [he']
  simp only [Function.comp_apply,hc,hxu,zero_smul,zero_add]
  exact smul_ne_zero (inv_ne_zero (hw0 x)) (three_coordinateGradientPair_pos_derivative_ne g u x hp)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeAnnulus_not_inner {c d e : ℝ} (hcd : c<d) {q : ThreeManifold}
    (hq : q∈ThreeAnnulus d e) : q∉threeNormalInv '' closedBall 0 c := by
  intro h
  apply hq.2
  exact image_mono (closedBall_subset_ball hcd) h
lemma threeAnnulus_clean {d e R : ℝ} (heR : e≤R) (hc : ThreeCleanBall R)
    {q : ThreeManifold} (hq : q∈ThreeAnnulus d e) :
    1/2≤‖productA q.1‖ ∧ ‖productA q.1‖≤3/4 := by
  obtain ⟨y,hy,rfl⟩ := hq.1
  exact hc y (closedBall_subset_closedBall heR hy)
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

lemma three_cutoff_raw_bounded_by_near_one
    (χ v : ThreeManifold → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ χ)
    (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v)
    (t : CoordinateTest ThreeModel ThreeManifold) (h : ℕ) {B D η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B) (hDB : D ≤ B)
    (hctrl : ∀ y ∈ t.compactSet, ∀ k ≤ h,
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘
        (chartAt ThreeModel t.center).symm) y‖ ≤ D*η) :
    ∀ y ∈ t.compactSet, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (cutoffFactor χ v ∘ (chartAt ThreeModel t.center).symm) y‖ ≤ 1+B := by
  intro y hy j hj
  have hw : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (cutoffFactor χ v) :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hnear (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘ (chartAt ThreeModel t.center).symm) y‖ ≤ B :=
    (hctrl y hy k hk).trans ((mul_le_mul_of_nonneg_right hDB hη0).trans
      (by simpa using mul_le_mul_of_nonneg_left hη1 hB))
  exact raw_jets_of_near_one (chartAt ThreeModel t.center).open_target (t.inTarget hy)
    (fun y hy => (contDiffAt_inChart hw t.center hy).contDiffWithinAt) h hB hnear j hj

theorem exists_three_exact_stage_oai :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
      ∀ V : Set (SmoothMetric ThreeModel ThreeManifold), IsSmoothNeighborhood g V →
    ∃ e : ℝ, b<e ∧ e<R/2 ∧ ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I⊆closedBall 0 a ∧
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
    ∀ᶠ n : ℕ in atTop, ∃ ĝ∈V, ∃ u : ThreeManifold → ℝ,
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ q, -laplaceBeltrami ĝ u q=productFrequency n*u q) ∧
      (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt ThreeModel q).symm) (chartAt ThreeModel q q)≠0) ∧
      (∀ q∉threeNormalInv '' closedBall 0 e,
        (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=threeCoupled threeCouplingRadius n q) ∧
      ENNReal.ofReal (A*productWaveFrequency n)<SignTests.signCertificate
        (fun j : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo j.val)
        (fun j => ε/(productWaveFrequency n*ℓ j.val))
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv) := by
  classical
  obtain ⟨R,hR,hclean,N,hN,h0N,hproduce⟩ := exists_three_scalar_producer
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR F hF hFa hext A V hV
  let c := (b+R/2)/2
  let d := (c+R/2)/2
  let e := (d+R/2)/2
  have hac : a < c := by dsimp [c]; linarith
  have hcd : c<d := by dsimp [d,c]; linarith
  have hde : d<e := by dsimp [e,d,c]; linarith
  have heR : e<R/2 := by dsimp [e,d,c]; linarith
  have hbe : b<e := by dsimp [e,d,c]; linarith
  have hFc : F⊆threeNormalInv '' closedBall 0 c :=
    hFa.trans (image_mono (closedBall_subset_closedBall hac.le))
  obtain ⟨χ,hχ,hχrange,hχd,hχe⟩ := exists_three_radial_cutoff hde
  obtain ⟨tests,h,δ,hδ,hreal⟩ := cutoff_exactification_in_smooth_neighborhood
    threeModel_finrank g V hV χ hχ
  have hs0 : Module.finrank ℝ ThreeModel<2*(2*(2:ℝ)) := by norm_num [threeModel_finrank]
  let atlas := Classical.choice (nonempty_compactMetricAtlas g 2 hs0)
  let i₀ : CoordIndex ThreeModel := ⟨0,by simp [threeModel_finrank]⟩
  obtain ⟨G,hG,hglobal⟩ := atlas.global_cutoff_raw_controls i₀ χ hχ
  choose D hD hDJ using fun z : CoordinateTest ThreeModel ThreeManifold =>
    cutoffFactor_compact_raw χ hχ z.center z.isCompact z.inTarget (h+1)
  let B := 1+∑ z∈tests.toFinset, D z
  have hB : 0<B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun z _ => (hD z).le))
  have hDB (z : CoordinateTest ThreeModel ThreeManifold) (hz : z∈tests) : D z≤B := by
    have hh := Finset.single_le_sum (fun z (_ : z∈tests.toFinset) => (hD z).le)
      (List.mem_toFinset.mpr hz)
    change D z≤1+_
    linarith
  obtain ⟨C,hC,hproj⟩ := three_annular_projection_uniform g hcd
    (heR.le.trans (by linarith : R/2≤R)) hclean hFc hext tests h (show 0≤1+B by linarith)
  obtain ⟨I,hIa,partition,hpart,ℓ,hℓ,ε,hε,hscalar⟩ := hproduce g hg a b ha hab hbR F hF hFa hext A
  obtain ⟨L,hL,hpacket⟩ := hscalar (tests++atlas.coveringRawTests i₀) (h+2) (h+3)
  let η (n : ℕ) := L*inverseFrequency n^(h+3)
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa [η] using (inverseFrequency_pow_zero (h+3) (by omega)).const_mul L
  have hGη : Tendsto (fun n => G*η n) atTop (𝓝 0) := by simpa using hη.const_mul G
  have hrate := inverseFrequency_weighted_zero L C h
  refine ⟨e,hbe,heR,I,hIa,partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  filter_upwards [hpacket,eventually_ge_atTop (2:ℕ),hη.eventually (gt_mem_nhds hδ),
    hη.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<1/32 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<1/4096 by norm_num)),
    hrate.eventually (gt_mem_nhds hδ)] with n hp hn hηδ hηhalf hGl hGgrad hηrate
  obtain ⟨u,hu,huc,hus,hreg,hβ,hz,hpos,hweighted,hβs,hzs,v,hv,hvp,hve,hsmall,hraw,hscore⟩ := hp
  have husc : tsupport u⊆closedBall 0 c := hus.trans ball_subset_closedBall
  let U := threeCoupled threeCouplingRadius n+threeWaveLift u
  let β := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) U
  let z := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) U
  let w := cutoffFactor χ v
  have hU : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ U :=
    (threeCoupled_smooth _ _).add (threeWaveLift_smooth hu huc)
  have hw : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hη0 : 0≤η n := mul_nonneg hL.le (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _)
  have hη1 : η n≤1 := by linarith
  have hvhalf (q : ThreeManifold) : |v q-1|≤1/2 := (hsmall q).2.2.trans hηhalf.le
  have hΛ : 1≤productFrequency n := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    unfold productFrequency; nlinarith
  have hctrl := hglobal β v hβ hv (η n) hη0 hη1
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).2.2)
  obtain ⟨hwb,hwG,hsmallw⟩ := three_cutoff_control_bounds g β χ v hχrange
    hηhalf (fun q => (hsmall q).2.2) hGl hGgrad hΛ hctrl
  have hwl (q) : 1/2≤w q := (hwb q).1
  have hwu (q) : w q≤2 := (hwb q).2
  have hwp (q) : 0<w q := by linarith [hwl q]
  let O := threeNormalInv '' ball 0 d
  let Fout := (threeNormalInv '' closedBall 0 e)ᶜ
  have hO : IsOpen O := threeNormalInv_isOpenMap _ isOpen_ball
  have hFo : IsOpen Fout := (threeNormalInv_closedBall_closed e).isOpen_compl
  have hann {q : ThreeManifold} (hq : q∉O∪Fout) : q∈ThreeAnnulus d e := by
    exact ⟨by simpa only [Fout,mem_compl_iff,not_not] using (not_or.mp hq).2,(not_or.mp hq).1⟩
  have hres := three_wave_residual_support g hF hFc hext hu huc husc hn
  have hcoeffout (q : ThreeManifold) (hq : q∈Fout) : β q=1 ∧ z q=1 := by
    have hnres : q∉tsupport (fun q => laplaceBeltrami g U q+productFrequency n*U q) :=
      fun hh => hq (image_mono (closedBall_subset_closedBall (hcd.trans hde).le) (hres hh))
    exact ⟨sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => β q-1) (fun hh => hnres (hβs hh))),
      sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => z q-1) (fun hh => hnres (hzs hh)))⟩
  have hmargin (q : ThreeManifold) (hq : q∉O∪Fout) :
      U q^2*coordinateGradientPair g w w q<w q^2*coordinateGradientPair g U U q := by
    have hannq := hann hq
    have hnot := threeAnnulus_not_inner hcd hannq
    have he := three_wave_exterior_germ huc husc n hnot
    change (threeCoupled threeCouplingRadius n+threeWaveLift u) q^2*_<_
    rw [he.eq_of_nhds,coordinateGradientPair_congr_nhds_cutoff g he]
    exact three_clean_conjugating_margin g q (hext q (fun hf => hnot (hFc hf))) n (by omega)
      (threeAnnulus_clean (heR.le.trans (by linarith : R/2≤R)) hclean hannq).1
      (threeAnnulus_clean (heR.le.trans (by linarith : R/2≤R)) hclean hannq).2 w (hwl q) (hwG q)
  have hwJ (t : CoordinateTest ThreeModel ThreeManifold) (ht : t∈tests)
      (y : ThreeModel) (hy : y∈t.compactSet) (j : ℕ) (hj : j≤h+1) :
      ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel t.center).symm) y‖≤1+B := by
    apply three_cutoff_raw_bounded_by_near_one χ v hχ hv t (h+1) hη0 hη1 hB.le (hDB t ht)
      (fun y hy => hDJ t v hv y hy (η n) hη0
        (fun k hk => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy k (by omega)).2.2)) y hy j hj
  obtain ⟨ĝ,hĝ,f,hf,hfe,hfU,hfZ,hfsgn,hfout⟩ := hreal β z U v (productFrequency n) O Fout
    hβ hz hU hv hΛ (fun q => (hpos q).1) hχrange hvhalf
    (fun q => (hsmall q).2.1.trans hηhalf.le) hweighted hve hO hFo
    (fun q hq => hχd q (image_mono ball_subset_closedBall hq))
    (fun q hq => hχe q (fun hh => hq (image_mono ball_subset_closedBall hh)))
    hcoeffout hsmallw hmargin
    (η n) C (n:ℝ) hη0 hηδ.le hC.le (by exact_mod_cast (show 1≤n by omega)) hηrate
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).2.1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j hj).2.2)
    (fun t ht y hy hout i j k hk => hproj w hw hwl hwu hwJ hwG huc husc n (by omega)
      t ht y hy (hann hout) i j k hk)
  refine ⟨ĝ,hĝ,f,hf,hfe,?_,?_,?_⟩
  · intro q hq
    have hUq := (hfZ q).mp hq
    have he : f=fun q => U q/w q := funext hfU
    rw [he]
    exact three_regular_quotient_at_zero g hU hw (fun q => (hwp q).ne') q hUq (hreg q hUq)
  · intro q hq
    refine ⟨(hfout q hq).1,(hfout q hq).2.trans ?_⟩
    exact (three_wave_exterior_germ huc husc n (fun hh =>
      hq (image_mono (closedBall_subset_closedBall (hcd.trans hde).le) hh))).eq_of_nhds
  · have he : ((f ∘ threeNormalInv) ∘ normalWaveEquiv)=fun y =>
        (w (threeNormalInv (normalWaveEquiv y)))⁻¹*(((U ∘ threeNormalInv) ∘ normalWaveEquiv) y) := by
      funext y
      simp only [Function.comp_apply,hfU,div_eq_mul_inv]
      exact mul_comm _ _
    rw [he,SignTests.signCertificate_pos_mul _ _ _ _ (fun y => inv_pos.mpr (hwp _))]
    exact hscore

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_exact_stage_oai := @OAI.YauCounterexamples.exists_three_exact_stage_oai
