-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_spherical_exact_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:29:11.787598+00:00
-- url     : https://prove2.me/submissions/5e7e6e7a-a55c-4fc2-a9b8-36c13d89a40c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_global_cutoff_raw_controls
import Theorems.Thm_OAI_YauCounterexamples_cutoff_exactification_in_smooth_neighborhood
import Theorems.Thm_OAI_YauCounterexamples_exists_spherical_scalar_producer
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas
import Theorems.Thm_OAI_YauCounterexamples_spherical_annular_projection_uniform
import Theorems.Thm_OAI_YauCounterexamples_spherical_cutoff_control_bounds
import Theorems.Thm_OAI_YauCounterexamples_spherical_exterior_conjugating_margin
import Theorems.Thm_OAI_YauCounterexamples_spherical_wave_residual_support

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_smooth (a b : Euclidean (d+1)) (k : ℕ) :
    ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (roundPower a b k) := by
  have hc : ContDiff ℝ ∞ (fun x : Euclidean (d+1) => (planarLinear a b x)^k) :=
    (planarLinear a b).contDiff.pow k
  exact (Complex.reCLM.contDiff.comp hc).contMDiff.comp contMDiff_coe_sphere


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
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


open Set Filter Function Manifold
open scoped Topology ContDiff

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
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalWaveLift_smooth {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalWaveLift u) :=
  contMDiff_manifoldChartPush sourcePole hu hc (by rw [sphere_chart_target]; exact subset_univ _)

lemma sphericalWaveLift_tsupport {u : Euclidean 3 → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r}) :
    tsupport (sphericalWaveLift u) ⊆ {q | sphericalRadius sourceAxisOne sourceAxisTwo q < r} := by
  intro q hq
  obtain ⟨y,hy,rfl⟩ := manifoldChartPush_tsupport sourcePole hc
    (by rw [sphere_chart_target]; exact subset_univ _) hq
  exact hs hy


end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ExistsSphericalRadialCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

theorem exists_spherical_radial_cutoff {a b : ℝ} (hab : a < b) :
    ∃ χ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ χ ∧
      (∀ q, χ q ∈ Icc (0:ℝ) 1) ∧
      (∀ q, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ a → χ q=1) ∧
      (∀ q, b ≤ sphericalRadius sourceAxisOne sourceAxisTwo q → χ q=0) := by
  let f := sphericalRadius sourceAxisOne sourceAxisTwo
  have hf : Continuous f := sphericalRadius_continuous _ _
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,Euclidean 3)) (n := (⊤ : ℕ∞))
    (s := {q : Sphere 3 | f q ≤ a}) (t := {q : Sphere 3 | f q < b})
    (isClosed_le hf continuous_const) (by
      rw [(isOpen_lt hf continuous_const).interior_eq]
      exact fun q hq => lt_of_le_of_lt hq hab)
  exact ⟨χ,χ.contMDiff,hχrange,fun q hq => hχ1.self_of_nhdsSet q hq,
    fun q hq => hχ0 q (not_lt.mpr hq)⟩

lemma spherical_wave_exterior_germ {u : Euclidean 3 → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r})
    (n : ℕ) {q : Sphere 3} (hq : r ≤ sphericalRadius sourceAxisOne sourceAxisTwo q) :
    (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) =ᶠ[𝓝 q]
      roundPower sourceAxisOne sourceAxisTwo n := by
  have hz : q ∉ tsupport (sphericalWaveLift u) := fun hq' =>
    (not_lt_of_ge hq) (sphericalWaveLift_tsupport hc hs hq')
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with x hx
  simp only [Pi.add_apply,hx,Pi.zero_apply,add_zero]

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_pos_derivative_ne (g : SmoothMetric E M) (u : M → ℝ)
    (x : M) (hp : 0 < coordinateGradientPair g u u x) :
    fderiv ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0 := by
  intro hz
  simp [coordinateGradientPair,hz] at hp

lemma regular_quotient_at_zero (g : SmoothMetric E M) {u w : M → ℝ}
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
  exact smul_ne_zero (inv_ne_zero (hw0 x)) (coordinateGradientPair_pos_derivative_ne g u x hp)

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

lemma cutoff_raw_bounded_by_near_one
    (χ v : Sphere 3 → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ χ)
    (hv : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v)
    (t : CoordinateTest (Euclidean 3) (Sphere 3)) (h : ℕ) {B D η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B) (hDB : D ≤ B)
    (hctrl : ∀ y ∈ t.compactSet, ∀ k ≤ h,
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘
        (chartAt (Euclidean 3) t.center).symm) y‖ ≤ D*η) :
    ∀ y ∈ t.compactSet, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (cutoffFactor χ v ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ 1+B := by
  intro y hy j hj
  have hw : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (cutoffFactor χ v) :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hnear (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ B :=
    (hctrl y hy k hk).trans ((mul_le_mul_of_nonneg_right hDB hη0).trans
      (by simpa using mul_le_mul_of_nonneg_left hη1 hB))
  exact raw_jets_of_near_one (chartAt (Euclidean 3) t.center).open_target (t.inTarget hy)
    (fun y hy => (contDiffAt_inChart hw t.center hy).contDiffWithinAt) h hB hnear j hj

theorem exists_spherical_exact_stage_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r a b : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r)
    (hra : r < a) (hab : a < b) (hb : b < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g N) :
    ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ᶠ n : ℕ in atTop, ∃ ĝ ∈ N, ∃ u : Sphere 3 → ℝ,
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ q, -laplaceBeltrami ĝ u q=sphereFrequency n*u q) ∧
      (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm) (chartAt (Euclidean 3) q q) ≠ 0) ∧
      (∀ q, b < sphericalRadius sourceAxisOne sourceAxisTwo q →
        (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=roundPower sourceAxisOne sourceAxisTwo n q) ∧
      ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
        (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val)
        (fun j => ε/((n:ℝ)*ℓ j.val))
        ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) := by
  classical
  have hr0 : 0 < r := by linarith
  have hr : r < 3/10 := hra.trans (hab.trans hb)
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b < 1 := by linarith
  have hb2 : b^2 < 1 := by nlinarith
  have hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r :=
    fun q hq => (hFt q hq).le.trans (hts.le.trans hsr.le)
  obtain ⟨χ,hχ,hχrange,hχa,hχb⟩ := exists_spherical_radial_cutoff hab
  obtain ⟨tests,h,δ,hδ,hreal⟩ := cutoff_exactification_in_smooth_neighborhood
    (by simp [Euclidean]) g N hN χ hχ
  have hs0 : Module.finrank ℝ (Euclidean 3) < 2*(2*(2:ℝ)) := by norm_num [Euclidean]
  let atlas := Classical.choice (nonempty_compactMetricAtlas g 2 hs0)
  let i₀ : CoordIndex (Euclidean 3) := ⟨0,by simp [Euclidean]⟩
  obtain ⟨G,hG,hglobal⟩ := atlas.global_cutoff_raw_controls i₀ χ hχ
  choose D hD hDJ using fun z : CoordinateTest (Euclidean 3) (Sphere 3) =>
    cutoffFactor_compact_raw χ hχ z.center z.isCompact z.inTarget (h+1)
  let B := 1+∑ z ∈ tests.toFinset, D z
  have hB : 0 < B := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun z _ => (hD z).le))
  have hDB (z : CoordinateTest (Euclidean 3) (Sphere 3)) (hz : z ∈ tests) : D z ≤ B := by
    have hh := Finset.single_le_sum (fun z (_ : z ∈ tests.toFinset) => (hD z).le)
      (List.mem_toFinset.mpr hz)
    change D z ≤ 1+_
    linarith
  obtain ⟨C,hC,hproj⟩ := spherical_annular_projection_uniform g₀ g hg₀ hr0 hra hab.le hb1
    hFr hext tests h (show 0 ≤ 1+B by linarith)
  obtain ⟨partition,hpart,ℓ,hℓ,ε,hε,hscalar⟩ := exists_spherical_scalar_producer
    g₀ hg₀ g hg ht hts hsr hr hF hFt hext hmetric A
  obtain ⟨L,hL,hpacket⟩ := hscalar (tests++atlas.coveringRawTests i₀) (h+2) (h+3)
  let η (n : ℕ) := L*inverseFrequency n^(h+3)
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa [η] using (inverseFrequency_pow_zero (h+3) (by omega)).const_mul L
  have hGη : Tendsto (fun n => G*η n) atTop (𝓝 0) := by simpa using hη.const_mul G
  have hrate := inverseFrequency_weighted_zero L C h
  refine ⟨partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  filter_upwards [hpacket,eventually_ge_atTop (2:ℕ),hη.eventually (gt_mem_nhds hδ),
    hη.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<1/32 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<(1-b^2)/16 by positivity)),
    hrate.eventually (gt_mem_nhds hδ)] with n hp hn hηδ hηhalf hGl hGgrad hηrate
  obtain ⟨u,hu,huc,hus,hreg,hβ,hz,hpos,hweighted,hβs,hzs,v,hv,hvp,hve,hsmall,hraw,hscore⟩ := hp
  let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
  let β := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) U
  let z := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) U
  let w := cutoffFactor χ v
  have hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U :=
    (roundPower_smooth _ _ _).add (sphericalWaveLift_smooth hu huc)
  have hw : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hη0 : 0 ≤ η n := mul_nonneg hL.le (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _)
  have hη1 : η n ≤ 1 := by linarith
  have hvhalf (q : Sphere 3) : |v q-1| ≤ 1/2 := (hsmall q).2.2.trans hηhalf.le
  have hΛ : 1 ≤ sphereFrequency n := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    unfold sphereFrequency; nlinarith
  have hctrl := hglobal β v hβ hv (η n) hη0 hη1
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).2.2)
  obtain ⟨hwb,hwG,hsmallw⟩ := spherical_cutoff_control_bounds g β χ v hχrange
    hηhalf (fun q => (hsmall q).2.2) hGl hGgrad hb0 hΛ hctrl
  have hwl (q) : 1/2 ≤ w q := (hwb q).1
  have hwu (q) : w q ≤ 2 := (hwb q).2
  have hwp (q) : 0 < w q := by linarith [hwl q]
  let O := {q : Sphere 3 | sphericalRadius sourceAxisOne sourceAxisTwo q < a}
  let Fout := {q : Sphere 3 | b < sphericalRadius sourceAxisOne sourceAxisTwo q}
  have hO : IsOpen O := isOpen_lt (sphericalRadius_continuous _ _) continuous_const
  have hFo : IsOpen Fout := isOpen_lt continuous_const (sphericalRadius_continuous _ _)
  have hann {q : Sphere 3} (hq : q ∉ O ∪ Fout) :
      a ≤ sphericalRadius sourceAxisOne sourceAxisTwo q ∧ sphericalRadius sourceAxisOne sourceAxisTwo q ≤ b := by
    simpa only [O,Fout,mem_union,mem_ofPred_eq,not_or,not_lt] using hq
  have hres := spherical_wave_residual_support g g₀ hg₀ hF hFr hext hu huc hus hn
  have hcoeffout (q : Sphere 3) (hq : q ∈ Fout) : β q=1 ∧ z q=1 := by
    have hnres : q ∉ tsupport (fun q => laplaceBeltrami g U q+sphereFrequency n*U q) :=
      fun hh => (not_le_of_gt (hra.trans hab |>.trans hq)) (hres hh)
    exact ⟨sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => β q-1) (fun hh => hnres (hβs hh))),
      sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => z q-1) (fun hh => hnres (hzs hh)))⟩
  have hmargin (q : Sphere 3) (hq : q ∉ O ∪ Fout) :
      U q^2*coordinateGradientPair g w w q < w q^2*coordinateGradientPair g U U q := by
    obtain ⟨hqa,hqb⟩ := hann hq
    exact spherical_exterior_conjugating_margin g₀ hg₀ g hr0 hra hb0 hb2 hFr hext huc hus
      n (by omega) w hwl hwG q hqa hqb
  have hwJ (t : CoordinateTest (Euclidean 3) (Sphere 3)) (ht : t ∈ tests)
      (y : Euclidean 3) (hy : y ∈ t.compactSet) (j : ℕ) (hj : j ≤ h+1) :
      ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ 1+B := by
    apply cutoff_raw_bounded_by_near_one χ v hχ hv t (h+1) hη0 hη1 hB.le (hDB t ht)
      (fun y hy => hDJ t v hv y hy (η n) hη0
        (fun k hk => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy k (by omega)).2.2)) y hy j hj
  obtain ⟨ĝ,hĝ,f,hf,hfe,hfU,hfZ,hfsgn,hfout⟩ := hreal β z U v (sphereFrequency n) O Fout
    hβ hz hU hv hΛ (fun q => (hpos q).1) hχrange hvhalf
    (fun q => (hsmall q).2.1.trans hηhalf.le) hweighted hve hO hFo
    (fun q hq => hχa q hq.le) (fun q hq => hχb q hq.le) hcoeffout hsmallw hmargin
    (η n) C (n:ℝ) hη0 hηδ.le hC.le (by exact_mod_cast (show 1≤n by omega)) hηrate
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).2.1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j hj).2.2)
    (fun t ht y hy hout i j k hk => hproj w hw hwl hwu hwJ hwG huc hus n (by omega)
      t ht y hy (hann hout).1 (hann hout).2 i j k hk)
  refine ⟨ĝ,hĝ,f,hf,hfe,?_,?_,?_⟩
  · intro q hq
    have hUq := (hfZ q).mp hq
    have he : f = fun q => U q/w q := funext hfU
    rw [he]
    exact regular_quotient_at_zero g hU hw (fun q => (hwp q).ne') q hUq (hreg q hUq)
  · intro q hq
    exact ⟨(hfout q hq).1,(hfout q hq).2.trans
      (spherical_wave_exterior_germ huc hus n ((hra.trans hab).le.trans hq.le)).eq_of_nhds⟩
  · have he : ((f ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)=
        fun y => (w ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)))⁻¹*
          (((U ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) y) := by
      funext y
      simp only [Function.comp_apply,hfU,div_eq_mul_inv]
      exact mul_comm _ _
    rw [he,SignTests.signCertificate_pos_mul _ _ _ _ (fun y => inv_pos.mpr (hwp _))]
    exact hscore

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_spherical_exact_stage_oai := @OAI.YauCounterexamples.exists_spherical_exact_stage_oai
