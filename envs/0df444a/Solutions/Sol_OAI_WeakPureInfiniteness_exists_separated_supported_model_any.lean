-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.exists_separated_supported_model_any
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:32.560088+00:00
-- url     : https://prove2.me/submissions/e7e217d9-e0b6-4d70-8030-ef46ff7fdc7b

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W005
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_uniform_reducing_model

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_AlgebraicTensorSpan
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u v

section TensorSpan

variable {A : Type u} {B C : Type v} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma tensorKernelIdeal_eq_closure_span (q : B →⋆ₙₐ[ℂ] C) :
    (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A B)) =
      closure (Submodule.span ℂ {z | ∃ a : A, ∃ b : B, q b = 0 ∧ z = spatialElementary a b} :
        Set (SpatialAmbient A B)) := by
  apply closure_adjoin_eq_closure_span
  · rintro _ ⟨a,b,hb,rfl⟩ _ ⟨c,d,hd,rfl⟩
    exact ⟨a*c,b*d,by rw [map_mul,hb,zero_mul], (spatialElementary_mul a c b d).symm⟩
  · rintro _ ⟨a,b,hb,rfl⟩
    exact ⟨star a,star b,by rw [map_star,hb,star_zero], (spatialElementary_star a b).symm⟩

end TensorSpan

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ApproximateCut
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section Ordered

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_sub_mul_of_pos_contraction (x y : A) (hy : 0 ≤ y) (hyn : ‖y‖ ≤ 1) :
    ‖x - x * y‖ ≤ ‖x‖ := by
  have hy' : 0 ≤ (y : Unitization ℂ A) := Unitization.inr_nonneg_iff.mpr hy
  have hyp : (y : Unitization ℂ A) ≤ 1 :=
    (norm_le_one_iff_of_nonneg _ hy').mp (by simpa only [Unitization.norm_inr] using hyn)
  have hn : ‖(1 : Unitization ℂ A) - y‖ ≤ 1 :=
    (norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hyp)).mpr (by simpa using hy')
  calc
    ‖x - x * y‖ = ‖(x : Unitization ℂ A) * (1 - y)‖ := by
      rw [mul_sub, mul_one, ← Unitization.inr_mul, ← Unitization.inr_sub, Unitization.norm_inr]
    _ ≤ ‖(x : Unitization ℂ A)‖ * ‖(1 : Unitization ℂ A) - y‖ := norm_mul_le _ _
    _ ≤ ‖(x : Unitization ℂ A)‖ * 1 := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = ‖x‖ := by rw [mul_one,Unitization.norm_inr]

end Ordered

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Clipping
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma continuous_clipFunction : Continuous clipFunction := by
  apply Continuous.inv₀
  · exact continuous_const.max Real.continuous_sqrt
  · intro t
    have : 0 < max (1 : ℝ) (Real.sqrt t) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact ne_of_gt this

lemma clipFunction_nonneg (t : ℝ) : 0 ≤ clipFunction t := by
  unfold clipFunction
  positivity

lemma clipFunction_le_one (t : ℝ) : clipFunction t ≤ 1 := by
  unfold clipFunction
  exact inv_le_one_of_one_le₀ (le_max_left _ _)

lemma star_mul_function_square (v : B) (f : ℝ → ℝ) (hf : Continuous f) :
    star (v*cfc f (star v*v))*(v*cfc f (star v*v))=
      cfc (fun t => f t*t*f t) (star v*v) := by
  have ha : IsSelfAdjoint (star v*v) := (star_mul_self_nonneg v).isSelfAdjoint
  rw [star_mul, (cfc_predicate f (star v*v)).star_eq]
  calc
    (cfc f (star v*v)*star v)*(v*cfc f (star v*v)) =
        (cfc f (star v*v)*(star v*v))*cfc f (star v*v) := by noncomm_ring
    _ = (cfc f (star v*v)*cfc (fun t : ℝ => t) (star v*v))*cfc f (star v*v) := by
      rw [cfc_id' ℝ (star v*v)]
    _ = cfc (fun t => f t*t*f t) (star v*v) := by
      rw [← cfc_mul f (fun t : ℝ => t) (star v*v) hf.continuousOn continuous_id.continuousOn,
        ← cfc_mul (fun t : ℝ => f t*t) f (star v*v) (hf.mul continuous_id).continuousOn hf.continuousOn]

lemma clip_scalar_norm (t : ℝ) (ht : 0 ≤ t) :
    ‖clipFunction t*t*clipFunction t‖ ≤ 1 := by
  have hsq := Real.sq_sqrt ht
  have hs := Real.sqrt_nonneg t
  have hf := clipFunction_nonneg t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold clipFunction
  by_cases ht1 : Real.sqrt t ≤ 1
  · rw [max_eq_left ht1, inv_one, one_mul, mul_one]
    nlinarith
  · have hs1 : 1 < Real.sqrt t := lt_of_not_ge ht1
    rw [max_eq_right hs1.le]
    have hs0 : Real.sqrt t ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs1)
    have : (Real.sqrt t)⁻¹*t*(Real.sqrt t)⁻¹=1 := by
      calc
        _ = (Real.sqrt t)⁻¹*(Real.sqrt t)^2*(Real.sqrt t)⁻¹ := by rw [hsq]
        _ = 1 := by field_simp
    exact this.le

lemma norm_cstarClip_le (v : B) : ‖cstarClip v‖ ≤ 1 := by
  have ha : 0 ≤ star v*v := star_mul_self_nonneg v
  have hn : ‖star (cstarClip v)*cstarClip v‖ ≤ 1 := by
    rw [cstarClip, star_mul_function_square v clipFunction continuous_clipFunction]
    apply norm_cfc_le zero_le_one
    intro t ht
    exact clip_scalar_norm t (spectrum_nonneg_of_nonneg ha ht)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (cstarClip v)]

lemma clip_scalar_difference_bound (t M : ℝ) (ht : 0 ≤ t) (hM : 0 ≤ M) (htM : t ≤ M^2) :
    ‖(1-clipFunction t)*t*(1-clipFunction t)‖ ≤ (max (M-1) 0)^2 := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht
  have hsM : Real.sqrt t ≤ M := by nlinarith
  have hg : 0 ≤ 1-clipFunction t := sub_nonneg.mpr (clipFunction_le_one t)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold clipFunction
  by_cases ht1 : Real.sqrt t ≤ 1
  · rw [max_eq_left ht1, inv_one, sub_self, zero_mul, zero_mul]
    positivity
  · have hs1 : 1 < Real.sqrt t := lt_of_not_ge ht1
    rw [max_eq_right hs1.le]
    have hs0 : Real.sqrt t ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs1)
    have hid : (1-(Real.sqrt t)⁻¹)*t*(1-(Real.sqrt t)⁻¹)=(Real.sqrt t-1)^2 := by
      calc
        _ = (1-(Real.sqrt t)⁻¹)*(Real.sqrt t)^2*(1-(Real.sqrt t)⁻¹) := by rw [hsq]
        _ = (Real.sqrt t-1)^2 := by field_simp
    rw [hid, max_eq_left (by linarith : 0 ≤ M-1)]
    nlinarith

omit [PartialOrder B] [StarOrderedRing B] in
lemma sub_cstarClip (v : B) :
    v-cstarClip v=v*cfc (fun t : ℝ => 1-clipFunction t) (star v*v) := by
  rw [cfc_sub (fun _ : ℝ => 1) clipFunction (star v*v) continuous_const.continuousOn
    continuous_clipFunction.continuousOn, cfc_const_one ℝ (star v*v), mul_sub, mul_one]
  rfl

lemma norm_sub_cstarClip_le (v : B) : ‖v-cstarClip v‖ ≤ max (‖v‖-1) 0 := by
  nontriviality B
  have ha : 0 ≤ star v*v := star_mul_self_nonneg v
  have hn : ‖star (v-cstarClip v)*(v-cstarClip v)‖ ≤ (max (‖v‖-1) 0)^2 := by
    rw [sub_cstarClip, star_mul_function_square v (fun t : ℝ => 1-clipFunction t)
      (continuous_const.sub continuous_clipFunction)]
    apply norm_cfc_le (sq_nonneg _)
    intro t ht
    apply clip_scalar_difference_bound t ‖v‖ (spectrum_nonneg_of_nonneg ha ht) (norm_nonneg v)
    have hh := spectrum.norm_le_norm_of_mem ht
    rw [Real.norm_eq_abs, abs_of_nonneg (spectrum_nonneg_of_nonneg ha ht),
      CStarRing.norm_star_mul_self] at hh
    nlinarith
  rw [CStarRing.norm_star_mul_self] at hn
  have hm : 0 ≤ max (‖v‖-1) 0 := le_max_right _ _
  nlinarith [norm_nonneg (v-cstarClip v)]

lemma map_cstarClip {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (π : B →⋆ₐ[ℂ] C) (v : B) : π (cstarClip v)=cstarClip (π v) := by
  have ha : IsSelfAdjoint (star v*v) := (star_mul_self_nonneg v).isSelfAdjoint
  rw [cstarClip, map_mul, π.map_cfc clipFunction (star v*v)
    continuous_clipFunction.continuousOn (by fun_prop) ha (ha.map π), map_mul, map_star]
  rfl

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ClippingTools
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma norm_clip_sub_le {T W : B} {δ : ℝ} (hδ : 0 ≤ δ)
    (hW : ‖W‖ ≤ 1) (hTW : ‖T-W‖ ≤ δ) : ‖cstarClip T-W‖ ≤ 2*δ := by
  have hT : ‖T‖ ≤ 1+δ := (norm_le_norm_add_norm_sub' T W).trans (add_le_add hW hTW)
  have hc : ‖T-cstarClip T‖ ≤ δ :=
    (norm_sub_cstarClip_le T).trans (max_le (by linarith) hδ)
  calc
    ‖cstarClip T-W‖ ≤ ‖cstarClip T-T‖+‖T-W‖ := by
      simpa only [dist_eq_norm] using dist_triangle (cstarClip T) T W
    _ ≤ δ+δ := by rw [norm_sub_rev (cstarClip T) T]; exact add_le_add hc hTW
    _ = 2*δ := by ring

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
lemma isometry_intertwiner_error_le (T W : K →L[ℂ] K) (D : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (hW : W.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp D) :
    ‖T.comp J.toContinuousLinearMap-J.toContinuousLinearMap.comp D‖ ≤ ‖T-W‖ := by
  rw [← hW, ← ContinuousLinearMap.sub_comp]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hn : ‖J.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖J x‖ ≤ 1*‖x‖
    rw [J.norm_map, one_mul]
  exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _)

lemma clip_reducing_models (T W : K →L[ℂ] K) (D : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) {δ : ℝ} (hδ : 0 ≤ δ) (hW : ‖W‖ ≤ 1) (hTW : ‖T-W‖ ≤ δ)
    (hr : W.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp D)
    (hra : (star W).comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp (star D)) :
    ‖(cstarClip T).comp J.toContinuousLinearMap-J.toContinuousLinearMap.comp D‖ ≤ 2*δ ∧
    ‖(star (cstarClip T)).comp J.toContinuousLinearMap-J.toContinuousLinearMap.comp (star D)‖ ≤ 2*δ := by
  have hnorm := norm_clip_sub_le hδ hW hTW
  constructor
  · exact (isometry_intertwiner_error_le _ _ _ J hr).trans hnorm
  · apply (isometry_intertwiner_error_le _ _ _ J hra).trans
    rwa [← star_sub, norm_star]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniformKernelConvergence
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

lemma isClosed_setOf_tendsto_zero_of_bound {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (l : Filter ι) (T : ι → E →ₗ[ℂ] F)
    (hT : ∀ᶠ i in l, ∀ x, ‖T i x‖ ≤ ‖x‖) :
    IsClosed {x : E | Tendsto (fun i => T i x) l (𝓝 0)} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx (ε/2) (by positivity)
  have hy' := (Metric.tendsto_nhds.mp hy) (ε/2) (by positivity)
  filter_upwards [hT,hy'] with i hi hiy
  rw [dist_zero_right] at hiy ⊢
  have hxy' : ‖x-y‖ < ε/2 := by simpa only [dist_eq_norm] using hxy
  have he : T i x = T i (x-y) + T i y := by rw [← map_add,sub_add_cancel]
  rw [he]
  exact (norm_add_le _ _).trans_lt
    ((add_lt_add_of_le_of_lt (hi (x-y)) hiy).trans_le (by linarith))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorInjectivity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorLeft

universe leftUniverse rightUniverse

variable {A B : Type leftUniverse} {C : Type rightUniverse}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma norm_spatialSum_le_image {ι : Type*} [Finite ι] (s : Finset ι)
    (a : ι → A) (c : ι → C) (φ : A →⋆ₙₐ[ℂ] B)
    (K : ComplexHilbert.{max leftUniverse rightUniverse}) (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ‖∑ i ∈ s, spatialElementary (a i) (c i)‖ ≤
      ‖∑ i ∈ s, spatialElementary (φ (a i)) (c i)‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro π
  rw [spatialSum_apply,norm_completion,norm_tensorSum_flip]
  apply (tensor_norm_le_faithful s (fun i => π.rightRep (c i)) a
    (ψ.comp φ) π.leftRep (hψ.comp hφ)).trans
  rw [norm_tensorSum_flip]
  let ρ : SpatialRepresentation B C :=
    { left := K, right := π.right, leftRep := ψ, rightRep := π.rightRep }
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (∑ i ∈ s, spatialElementary (φ (a i)) (c i)) ρ
  change ‖(∑ i ∈ s, spatialElementary (φ (a i)) (c i)) ρ‖ ≤ _ at h
  rw [spatialSum_apply,norm_completion] at h
  exact h

lemma norm_spatialSum_le_image_finset {ι : Type*} (s : Finset ι)
    (a : ι → A) (c : ι → C) (φ : A →⋆ₙₐ[ℂ] B)
    (K : ComplexHilbert.{max leftUniverse rightUniverse}) (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ‖∑ i ∈ s, spatialElementary (a i) (c i)‖ ≤
      ‖∑ i ∈ s, spatialElementary (φ (a i)) (c i)‖ := by
  classical
  rw [← Finset.sum_coe_sort s (fun i => spatialElementary (a i) (c i)),
    ← Finset.sum_coe_sort s (fun i => spatialElementary (φ (a i)) (c i))]
  exact norm_spatialSum_le_image Finset.univ (fun i : s => a i) (fun i : s => c i) φ K ψ hφ hψ

lemma norm_spatialMapLeft_ge_on_span
    (φ : A →⋆ₙₐ[ℂ] B) (K : ComplexHilbert.{max leftUniverse rightUniverse})
    (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (z : SpatialAmbient A C)
    (hz : z ∈ Submodule.span ℂ (Set.range fun p : A × C => spatialElementary p.1 p.2)) :
    ‖z‖ ≤ ‖spatialMapLeft φ z‖ := by
  classical
  obtain ⟨d, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  simp only [Finsupp.sum, map_sum, map_smul, spatialMapLeft_elementary]
  simpa only [← spatialElementary_smul_left, map_smul] using
    norm_spatialSum_le_image_finset d.support (fun i => d i • i.1) Prod.snd φ K ψ hφ hψ

lemma norm_minimalMapLeft (φ : A →⋆ₙₐ[ℂ] B)
    (K : ComplexHilbert.{max leftUniverse rightUniverse})
    (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (z : MinimalTensor A C) : ‖minimalMapLeft φ z‖ = ‖z‖ := by
  apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le _ _)
  let S := {x : SpatialAmbient A C | ‖x‖ ≤ ‖spatialMapLeft φ x‖}
  have hc : IsClosed S := isClosed_le continuous_norm
    ((nonUnitalStarHom_continuous (spatialMapLeft φ)).norm)
  have hz := z.property
  change z.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hz
  rw [minimalTensor_eq_closure_span] at hz
  exact (closure_minimal (fun _ hx => norm_spatialMapLeft_ge_on_span φ K ψ hφ hψ _ hx) hc) hz

end TensorLeft

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteCoordinates
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexOrder

variable {n : Type*} [Fintype n]

lemma scalarActionHom_eq (D : CStarMatrix n n ℂ) :
    scalarActionHom D=scalarMatrixAction (H := ℂ) D := rfl

lemma scalarActionHom_injective : Function.Injective (scalarActionHom (n := n)) := by
  classical
  intro D E h
  ext i j
  have hh := congrArg (fun T : HilbertVector n ℂ →L[ℂ] HilbertVector n ℂ =>
    T (PiLp.single 2 j 1) i) h
  simpa [scalarActionHom_eq, scalarMatrixAction_apply, PiLp.single_apply, smul_eq_mul] using hh

lemma norm_scalarMatrixAction (D : CStarMatrix n n ℂ) :
    ‖scalarMatrixAction (H := ℂ) D‖=‖D‖ :=
  NonUnitalStarAlgHom.norm_map scalarActionHom scalarActionHom_injective D

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma exists_scalar_matrix_coordinates [FiniteDimensional ℂ H] (D : H →L[ℂ] H) :
    ∃ (d : ℕ) (e : H ≃ₗᵢ[ℂ] HilbertVector (Fin d) ℂ)
      (M : CStarMatrix (Fin d) (Fin d) ℂ),
      ‖M‖=‖D‖ ∧ scalarMatrixAction (H := ℂ) M=e.conjStarAlgEquiv D := by
  classical
  let b := stdOrthonormalBasis ℂ H
  let M : CStarMatrix (Fin (Module.finrank ℂ H)) (Fin (Module.finrank ℂ H)) ℂ :=
    fun i j => ⟪b i, D (b j)⟫_ℂ
  have he : scalarMatrixAction (H := ℂ) M=b.repr.conjStarAlgEquiv D := by
    ext x i
    obtain ⟨y,rfl⟩ := b.repr.surjective x
    rw [scalarMatrixAction_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    rw [b.repr.symm_apply_apply]
    simp only [M, OrthonormalBasis.repr_apply_apply, smul_eq_mul]
    conv_rhs => rw [← b.sum_repr' y]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  refine ⟨Module.finrank ℂ H,b.repr,M,?_,he⟩
  rw [← norm_scalarMatrixAction M, he]
  exact @StarAlgEquiv.norm_map _ (H →L[ℂ] H)
    (HilbertVector (Fin (Module.finrank ℂ H)) ℂ →L[ℂ] HilbertVector (Fin (Module.finrank ℂ H)) ℂ)
    _ _ _ _ _ b.repr.conjStarAlgEquiv D

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SupportedCorner
attribute [-instance] _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma matrixSingletonHom_injective : Function.Injective (matrixSingletonHom (A := A)) := by
  intro x y h
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  exact h

variable {n : Type*} [Fintype n]

variable [PartialOrder A] [StarOrderedRing A]

lemma supportedCompression_inverse (U : CStarMatrix (Fin 1) n A)
    (e : CStarMatrix n n A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e)
    (z : supportedAlgebra e he) :
    U.conjTranspose*(supportedCompression U e he hU z)*U=z.val := by
  change U.conjTranspose*(U*z.val*U.conjTranspose)*U=z.val
  rw [← rectangular_mul_assoc, ← rectangular_mul_assoc, hU,
    rectangular_mul_assoc (e*z.val) U.conjTranspose U, hU, z.property.1, z.property.2]

lemma supportedCompression_injective (U : CStarMatrix (Fin 1) n A)
    (e : CStarMatrix n n A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    Function.Injective (supportedCompression U e he hU) := by
  intro x y h
  apply Subtype.ext
  rw [← supportedCompression_inverse U e he hU x, ← supportedCompression_inverse U e he hU y, h]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorMultiplier
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u v

noncomputable section

open scoped TensorProduct ENNReal ComplexOrder

open UniformSpace Filter Topology

variable {A B : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma norm_tensorCutNonunital_le [PartialOrder C] [StarOrderedRing C]
    (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) (x : MinimalTensor A C) :
    ‖tensorCutNonunital e x‖ ≤ ‖x‖ := by
  let := CStarAlgebra.spectralOrder (SpatialAmbient A C)
  let := CStarAlgebra.spectralOrderedRing (SpatialAmbient A C)
  exact norm_sub_mul_of_pos_contraction x.val (spatialRightMultiplierHom e)
    (map_nonneg (spatialRightMultiplierHom (A := A)) he)
    ((NonUnitalStarAlgHom.norm_apply_le (spatialRightMultiplierHom (A := A)) e).trans hen)

lemma tensorCutNonunital_elementary (e c : C) (a : A) :
    tensorCutNonunital e (minimalElementary a c)=minimalElementary a (c-c*e) := by
  apply Subtype.ext
  change spatialElementary a c-spatialElementary a c*spatialRightMultiplier e=_
  rw [spatialElementary_mul_rightMultiplier]
  have h := spatialElementary_add_right a (c-c*e) (c*e)
  rw [sub_add_cancel] at h
  exact sub_eq_iff_eq_add.mpr h

lemma spatialMapLeft_rightMultiplier (φ : A →⋆ₙₐ[ℂ] B) (e : C) :
    spatialMapLeft φ (spatialRightMultiplier e)=spatialRightMultiplier e := rfl

lemma minimalMapLeft_tensorCutNonunital (φ : A →⋆ₙₐ[ℂ] B) (e : C) (x : MinimalTensor A C) :
    minimalMapLeft φ (tensorCutNonunital e x)=tensorCutNonunital e (minimalMapLeft φ x) := by
  apply Subtype.ext
  change spatialMapLeft φ (x.val-x.val*spatialRightMultiplier e)=_
  rw [map_sub, map_mul, spatialMapLeft_rightMultiplier]
  rfl

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalHeredity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u v

noncomputable section

open Filter Topology

variable {A B : Type u} {C D : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma cutVanishingSpaceNonunital_closed [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1) :
    IsClosed (cutVanishingSpaceNonunital (A := A) l e : Set (MinimalTensor A C)) := by
  apply isClosed_setOf_tendsto_zero_of_bound l (fun i => tensorCutNonunitalLinear (e i))
  filter_upwards [he] with i hi
  exact norm_tensorCutNonunital_le (e i) hi.1 hi.2

lemma tensorCutNonunital_tendsto_zero_on_ideal [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1)
    (q : C →⋆ₙₐ[ℂ] D)
    (happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c))
    (x : MinimalTensor A C) (hx : x.val ∈ tensorKernelIdeal (A := A) q) :
    Tendsto (fun i => tensorCutNonunital (e i) x) l (𝓝 0) := by
  let S := cutVanishingSpaceNonunital (A := A) l e
  let j : MinimalTensor A C →ₗ[ℂ] SpatialAmbient A C :=
    { toFun := Subtype.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let T := S.map j
  have hTc : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ (cutVanishingSpaceNonunital_closed l e he)
  have hgen : ∀ a c, q c = 0 → spatialElementary a c ∈ T := by
    intro a c hc
    refine ⟨minimalElementary a c, ?_, rfl⟩
    change Tendsto (fun i => tensorCutNonunital (e i) (minimalElementary a c)) l (𝓝 0)
    simp only [tensorCutNonunital_elementary]
    let F : C →L[ℂ] MinimalTensor A C :=
      LinearMap.mkContinuous
        { toFun c := minimalElementary a c
          map_add' c d := Subtype.ext (spatialElementary_add_right a c d)
          map_smul' r c := Subtype.ext (spatialElementary_smul_right r a c) }
        ‖a‖ (norm_spatialElementary_le a)
    have hh : Tendsto (fun i => c-c*e i) l (𝓝 0) := by
      simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => c) l (𝓝 c)).sub (happ c hc)
    have hF (b : C) : F b = minimalElementary a b := rfl
    have h := F.continuous.tendsto 0 |>.comp hh
    simp only [Function.comp_def, hF] at h
    have hz : minimalElementary a (0 : C) = (0 : MinimalTensor A C) := map_zero F
    exact hz ▸ h
  have hspan : Submodule.span ℂ
      {z : SpatialAmbient A C | ∃ a : A, ∃ c : C, q c = 0 ∧ z = spatialElementary a c} ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,c,hc,rfl⟩
    exact hgen a c hc
  change x.val ∈ (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A C)) at hx
  rw [tensorKernelIdeal_eq_closure_span] at hx
  have hmem : x.val ∈ T := (closure_minimal hspan hTc) hx
  obtain ⟨y,hy,hyx⟩ := hmem
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

lemma tensorRightMultiply_kernel_mem (q : C →⋆ₙₐ[ℂ] D) (e : C) (he : q e=0)
    (x : MinimalTensor A C) :
    (tensorRightMultiply e x).val ∈ tensorKernelIdeal (A := A) q := by
  have hs : ∀ z ∈ Submodule.span ℂ
      (Set.range fun p : A × C => spatialElementary p.1 p.2),
      z*spatialRightMultiplier e ∈ tensorKernelIdeal (A := A) q := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a,c⟩,rfl⟩ := hz
      rw [spatialElementary_mul_rightMultiplier]
      apply NonUnitalStarSubalgebra.le_topologicalClosure
      apply NonUnitalStarAlgebra.subset_adjoin ℂ
      exact ⟨a,c*e,by rw [map_mul,he,mul_zero],rfl⟩
    | zero => rw [zero_mul]; exact (tensorKernelIdeal (A := A) q).zero_mem
    | add z w _ _ hz hw => rw [add_mul]; exact (tensorKernelIdeal (A := A) q).add_mem hz hw
    | smul c z _ hz => rw [smul_mul_assoc]; exact (tensorKernelIdeal (A := A) q).smul_mem c hz
  have hc : IsClosed {z : SpatialAmbient A C | z*spatialRightMultiplier e ∈ tensorKernelIdeal (A := A) q} :=
    isClosed_closure.preimage (continuous_id.mul continuous_const)
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  exact (closure_minimal hs hc) hx

lemma tensor_mem_ideal_of_nonunitalCuts {ι : Type*} (l : Filter ι) [l.NeBot]
    (e : ι → C) (q : C →⋆ₙₐ[ℂ] D) (he : ∀ i, q (e i)=0)
    (x : MinimalTensor A C)
    (hx : Tendsto (fun i => tensorCutNonunital (e i) x) l (𝓝 0)) :
    x.val ∈ tensorKernelIdeal (A := A) q := by
  have hmul : Tendsto (fun i => tensorRightMultiply (e i) x) l (𝓝 x) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x)).sub hx
    simpa only [tensorCutNonunital, sub_sub_cancel, sub_zero] using h
  apply isClosed_closure.mem_of_tendsto (continuous_subtype_val.tendsto x |>.comp hmul)
  exact Filter.Eventually.of_forall (fun i => tensorRightMultiply_kernel_mem q (e i) (he i) x)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalExactness
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter Topology

universe algebraUniverse

variable {A B : Type algebraUniverse} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem exact_of_injective
    (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (K : ComplexHilbert.{algebraUniverse}) (ψ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (hψ : Function.Injective ψ) (hB : Exact B) : Exact A := by
  intro C D _ _ q hq z hz
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let I := kernelAlgebra q
  let := CStarAlgebra.spectralOrder I
  let := CStarAlgebra.spectralOrderedRing I
  let l := CStarAlgebra.approximateUnit I
  have hl := CStarAlgebra.increasingApproximateUnit I
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  let e : I → C := Subtype.val
  have he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1 := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with i hi hn
    refine ⟨?_, hn⟩
    obtain ⟨x, hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hi
    have hi' : e i = star (e x) * e x := congrArg Subtype.val hx
    rw [hi']
    exact star_mul_self_nonneg _
  have happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c) := by
    intro c hc
    let x : I := ⟨c,hc⟩
    exact continuous_subtype_val.tendsto x |>.comp (hl.tendsto_mul_left x)
  have hmem : (minimalMapLeft φ z).val ∈
      tensorKernelIdeal (A := B) q := by
    apply hB C D q hq
    intro π
    exact hz (π.precompLeft φ)
  have hcuts := tensorCutNonunital_tendsto_zero_on_ideal l e he q happ
    (minimalMapLeft φ z) hmem
  have hcutz : Tendsto (fun i => tensorCutNonunital (e i) z) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := tendsto_zero_iff_norm_tendsto_zero.mp hcuts
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    rw [← minimalMapLeft_tensorCutNonunital]
    exact (norm_minimalMapLeft φ K ψ hφ hψ _).symm
  exact tensor_mem_ideal_of_nonunitalCuts l e q (fun i => i.property) z hcutz

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorSubalgebras
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem exact_subalgebra (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (hB : Exact B) : Exact A := by
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation B
  exact exact_of_injective φ hφ H π hπ hB

lemma minimalMapLeft_injective {C : Type u} [NonUnitalCStarAlgebra C]
    (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) :
    Function.Injective (minimalMapLeft (C := C) φ) := by
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation B
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply norm_eq_zero.mp
  rw [← norm_minimalMapLeft φ H π hφ hπ z, hz, norm_zero]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UnitizationTensor
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.contractionEvaluation_generator _root_.OAI.WeakPureInfiniteness.contractionEvaluation_smul _root_.OAI.WeakPureInfiniteness.contractionEvaluation_star _root_.OAI.WeakPureInfiniteness.contractionEvaluation_word _root_.OAI.WeakPureInfiniteness.fullGroupEvaluation_element _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.spatialElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.spatialElementaryRight_apply _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped TensorProduct ComplexOrder ENNReal

open UniformSpace

variable {A C D : Type u} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma spatialElementary_ne_zero {a : A} {c : C} (ha : a≠0) (hc : c≠0) :
    spatialElementary a c≠0 := by
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation A
  obtain ⟨K,ρ,hρ⟩ := exists_faithful_representation C
  have hπa : π a≠0 := by intro h; apply ha; apply hπ; simpa using h
  have hρc : ρ c≠0 := by intro h; apply hc; apply hρ; simpa using h
  obtain ⟨ξ,hξ⟩ : ∃ ξ : H, π a ξ≠0 := by
    by_contra h
    apply hπa
    ext ξ
    simpa using not_exists.mp h ξ
  obtain ⟨η,hη⟩ : ∃ η : K, ρ c η≠0 := by
    by_contra h
    apply hρc
    ext η
    simpa using not_exists.mp h η
  let σ : SpatialRepresentation A C := {left := H, right := K, leftRep := π, rightRep := ρ}
  intro h
  have hh := congrArg (fun z : SpatialAmbient A C => z σ ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : Completion _)) h
  change ((TensorProduct.mapL (π a) (ρ c)).completion _)=0 at hh
  rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul] at hh
  have hn := congrArg norm hh
  rw [Completion.norm_coe, TensorProduct.norm_tmul, norm_zero] at hn
  exact (ne_of_gt (mul_pos (norm_pos_iff.mpr hξ) (norm_pos_iff.mpr hη))) hn

lemma rightElementaryHom_injective {E : Type u} [CStarAlgebra E] [Nontrivial E] :
    Function.Injective (rightElementaryHom (A := E) (C := C)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  by_contra h
  exact spatialElementary_ne_zero (one_ne_zero : (1 : E)≠0) h (congrArg Subtype.val hc)

lemma minimalTensor_closed_submodule (S : Submodule ℂ (MinimalTensor A C))
    (hS : IsClosed (S : Set (MinimalTensor A C)))
    (he : ∀ a c, minimalElementary a c∈S) (x : MinimalTensor A C) : x∈S := by
  let j : MinimalTensor A C →ₗ[ℂ] SpatialAmbient A C :=
    { toFun := Subtype.val, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let T := S.map j
  have hTc : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ hS
  have hs : Submodule.span ℂ (Set.range fun p : A×C => spatialElementary p.1 p.2) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,c⟩,rfl⟩
    exact ⟨minimalElementary a c,he a c,rfl⟩
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  obtain ⟨y,hy,hyx⟩ := (closure_minimal hs hTc) hx
  exact (Subtype.ext hyx : y=x) ▸ hy

lemma minimalMapLeft_right_commute {B : Type u} [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) (q : C →⋆ₙₐ[ℂ] D) (z : MinimalTensor A C) :
    minimalMapRight q (minimalMapLeft φ z)=minimalMapLeft φ (minimalMapRight q z) := rfl

lemma minimalMapRight_eq_zero_iff (q : C →⋆ₙₐ[ℂ] D) (z : MinimalTensor A C) :
    minimalMapRight q z=0 ↔ ∀ π : SpatialRepresentation A D, z.val (π.precompRight q)=0 := by
  constructor
  · intro h π
    exact congrArg (fun z : MinimalTensor A D => z.val π) h
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    exact funext h

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UnitizationExact
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped TensorProduct ComplexOrder ENNReal

variable {A C D : Type u} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma unitizationScalarEnd_apply (a : Unitization ℂ A) :
    unitizationScalarEnd a=a.fst • (1 : Unitization ℂ A) :=
  by
    change algebraMap ℂ (Unitization ℂ A) a.fst=a.fst • (1 : Unitization ℂ A)
    exact Algebra.algebraMap_eq_smul_one _

lemma unitization_difference_scalarEnd (a : Unitization ℂ A) :
    a-unitizationScalarEnd a=(a.snd : Unitization ℂ A) := by
  change a-algebraMap ℂ (Unitization ℂ A) a.fst=(a.snd : Unitization ℂ A)
  apply Unitization.ext
  · change a.fst-a.fst=0
    exact sub_self _
  · change a.snd-0=a.snd
    exact sub_zero _

lemma minimalMapLeft_scalarEnd_elementary (a : Unitization ℂ A) (c : C) :
    minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom (minimalElementary a c)=
      rightElementaryHom (a.fst • c) := by
  rw [minimalMapLeft_elementary]
  apply Subtype.ext
  change spatialElementary (unitizationScalarEnd a) c=spatialElementary 1 (a.fst • c)
  rw [unitizationScalarEnd_apply, spatialElementary_smul_left, spatialElementary_smul_right]

lemma difference_scalarEnd_elementary (a : Unitization ℂ A) (c : C) :
    minimalElementary a c-
        minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom (minimalElementary a c)=
      minimalMapLeft (Unitization.inrNonUnitalStarAlgHom ℂ A) (minimalElementary a.snd c) := by
  rw [minimalMapLeft_elementary, minimalMapLeft_elementary]
  apply Subtype.ext
  change spatialElementary a c-spatialElementary (unitizationScalarEnd a) c=
    spatialElementary (a.snd : Unitization ℂ A) c
  have h := spatialElementary_add_left (a-unitizationScalarEnd a) (unitizationScalarEnd a) c
  rw [sub_add_cancel, unitization_difference_scalarEnd] at h
  exact sub_eq_iff_eq_add.mpr h

lemma unitizationTensor_decomposition (z : MinimalTensor (Unitization ℂ A) C) :
    ∃ (z₀ : MinimalTensor A C) (c : C),
      z-minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom z=
        minimalMapLeft (Unitization.inrNonUnitalStarAlgHom ℂ A) z₀ ∧
      minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom z=rightElementaryHom c := by
  let P := minimalMapLeft (C := C) (unitizationScalarEnd (A := A)).toNonUnitalStarAlgHom
  let i := minimalMapLeft (C := C) (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let r := rightElementaryHom (A := Unitization ℂ A) (C := C)
  let L : MinimalTensor (Unitization ℂ A) C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C :=
    LinearMap.id-(P : MinimalTensor (Unitization ℂ A) C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  have hL : Continuous L := continuous_id.sub (nonUnitalStarHom_continuous P)
  let R := LinearMap.range (i : MinimalTensor A C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  let S := R.comap L
  have hS : IsClosed (S : Set (MinimalTensor (Unitization ℂ A) C)) :=
    (nonUnitalStarHom_isClosed_range i).preimage hL
  have hz₀ : L z∈R := minimalTensor_closed_submodule S hS (by
    intro a c
    exact ⟨minimalElementary a.snd c, (difference_scalarEnd_elementary a c).symm⟩) z
  obtain ⟨z₀,hz₀⟩ := hz₀
  let R' := LinearMap.range (r : C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  let S' := R'.comap (P : MinimalTensor (Unitization ℂ A) C →ₗ[ℂ] MinimalTensor (Unitization ℂ A) C)
  have hS' : IsClosed (S' : Set (MinimalTensor (Unitization ℂ A) C)) :=
    (nonUnitalStarHom_isClosed_range r).preimage (nonUnitalStarHom_continuous P)
  have hcz : P z∈R' := minimalTensor_closed_submodule S' hS' (by
    intro a c
    exact ⟨a.fst • c, (minimalMapLeft_scalarEnd_elementary a c).symm⟩) z
  obtain ⟨c,hc⟩ := hcz
  exact ⟨z₀,c,hz₀.symm,hc.symm⟩

lemma minimalMapRight_rightElementary {E : Type u} [CStarAlgebra E]
    (q : C →⋆ₙₐ[ℂ] D) (c : C) :
    minimalMapRight q (rightElementaryHom (A := E) c)=rightElementaryHom (q c) := rfl

lemma mapLeft_tensorKernel {B : Type u} [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) (q : C →⋆ₙₐ[ℂ] D) {x : SpatialAmbient A C}
    (hx : x∈tensorKernelIdeal (A := A) q) :
    spatialMapLeft φ x∈tensorKernelIdeal (A := B) q := by
  apply NonUnitalStarSubalgebra.topologicalClosure_minimal _
    (t := NonUnitalStarSubalgebra.comap (spatialMapLeft φ) (tensorKernelIdeal (A := B) q))
    (NonUnitalStarAlgebra.adjoin_le ?_) ?_ hx
  · rintro _ ⟨a,c,hc,rfl⟩
    change spatialMapLeft φ (spatialElementary a c)∈tensorKernelIdeal (A := B) q
    rw [spatialMapLeft_elementary]
    apply NonUnitalStarSubalgebra.le_topologicalClosure
    exact NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨φ a,c,hc,rfl⟩
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous (spatialMapLeft φ))

theorem exact_unitization (hA : Exact A) : Exact (Unitization ℂ A) := by
  intro C D _ _ q hq z hz
  have hzq : minimalMapRight q z=0 := (minimalMapRight_eq_zero_iff q z).mpr hz
  obtain ⟨z₀,c,hz₀,hc⟩ := unitizationTensor_decomposition z
  have hPq : minimalMapRight q (minimalMapLeft unitizationScalarEnd.toNonUnitalStarAlgHom z)=0 := by
    rw [minimalMapLeft_right_commute, hzq, map_zero]
  have hqc : q c=0 := by
    apply (rightElementaryHom_injective (E := Unitization ℂ A))
    rw [map_zero, ← minimalMapRight_rightElementary, ← hc, hPq]
  have hz₀q : minimalMapRight q z₀=0 := by
    apply minimalMapLeft_injective (Unitization.inrNonUnitalStarAlgHom ℂ A) Unitization.inr_injective
    rw [map_zero, ← minimalMapLeft_right_commute, ← hz₀, map_sub, hzq, hPq, sub_self]
  have hz₀mem := hA C D q hq z₀ ((minimalMapRight_eq_zero_iff q z₀).mp hz₀q)
  have hz' : z=minimalMapLeft (Unitization.inrNonUnitalStarAlgHom ℂ A) z₀+rightElementaryHom c := by
    rw [← hz₀, ← hc, sub_add_cancel]
  rw [hz']
  apply (tensorKernelIdeal (A := Unitization ℂ A) q).add_mem
  · exact mapLeft_tensorKernel (Unitization.inrNonUnitalStarAlgHom ℂ A) q hz₀mem
  · apply NonUnitalStarSubalgebra.le_topologicalClosure
    exact NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨1,c,hqc,rfl⟩

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SupportedExact
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

lemma exact_supportedAlgebra (hA : Exact A) (U : CStarMatrix (Fin 1) (Fin n) A)
    (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    Exact (supportedAlgebra e he) :=
  exact_subalgebra (matrixSingletonHom.comp (supportedCompression U e he hU))
    (matrixSingletonHom_injective.comp (supportedCompression_injective U e he hU)) hA

lemma exact_unitization_supportedAlgebra (hA : Exact A) (U : CStarMatrix (Fin 1) (Fin n) A)
    (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    Exact (Unitization ℂ (supportedAlgebra e he)) :=
  exact_unitization (exact_supportedAlgebra hA U e he hU)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SupportedSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexOrder

lemma transport_reducing_coordinates {H X K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] X) (J : X →ₗᵢ[ℂ] K) (W : K →L[ℂ] K) (D : H →L[ℂ] H)
    (h : W.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp (e.conjStarAlgEquiv D)) :
    W.comp (J.comp e.toLinearIsometry).toContinuousLinearMap=
      (J.comp e.toLinearIsometry).toContinuousLinearMap.comp D := by
  ext x
  have hh := congrArg (fun L : X →L[ℂ] K => L (e x)) h
  simpa using hh

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseSupportedSeparation
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

theorem exists_separated_supported_model_any_oai
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (c : A) (hc : 0 ≤ c) {α : ℝ} (hα : 0 < α)
    (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e)
    (U : CStarMatrix (Fin 1) (Fin n) A) (hU : U.conjTranspose*U=e)
    (V : supportedAlgebra e he) :
    ∃ w : CStarMatrix (Fin n) (Fin n) A, ‖w‖ ≤ 1 ∧
      diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*w*
        diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)=w ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ ≤ ‖matrixRepresentation π (Fin n) (V.val-w)‖ := by
  classical
  by_contra h
  push Not at h
  let B := Unitization ℂ (supportedAlgebra e he)
  let V₀ : B := Unitization.inr V
  let v : B := cstarClip V₀
  have hB : Exact B := exact_unitization_supportedAlgebra hA U e he hU
  have hmodels : FiniteContractionModelsAny B v γ := by
    intro H _ D hD
    obtain ⟨d,coord,M,hMn,hM⟩ := exists_scalar_matrix_coordinates D
    obtain ⟨w,hwn,hEw,hred⟩ := exists_uniform_reducing_model hn hpi c hc hα d M (hMn.trans_le hD)
    obtain ⟨K,π,hπc,hnear⟩ := h w hwn hEw
    obtain ⟨J,hJ,hJa⟩ := hred K π hπc
    let lam : supportedAlgebra e he →⋆ₙₐ[ℂ]
        (HilbertVector (Fin n) K →L[ℂ] HilbertVector (Fin n) K) :=
      (matrixRepresentation π (Fin n)).comp (NonUnitalStarSubalgebraClass.subtype (supportedAlgebra e he))
    let πB : B →⋆ₐ[ℂ] (HilbertVector (Fin n) K →L[ℂ] HilbertVector (Fin n) K) :=
      Unitization.starLift lam
    let J' := J.comp coord.toLinearIsometry
    let T := matrixRepresentation π (Fin n) V.val
    let W := matrixRepresentation π (Fin n) w
    have hr : W.comp J'.toContinuousLinearMap=J'.toContinuousLinearMap.comp D := by
      apply transport_reducing_coordinates coord J W D
      rwa [← hM]
    have hra : (star W).comp J'.toContinuousLinearMap=J'.toContinuousLinearMap.comp (star D) := by
      apply transport_reducing_coordinates coord J (star W) (star D)
      rw [show coord.conjStarAlgEquiv (star D)=star (coord.conjStarAlgEquiv D) from
        map_star coord.conjStarAlgEquiv.toStarAlgHom D, ← hM]
      exact hJa
    have hTW : ‖T-W‖ ≤ σ := by
      simpa only [T,W,map_sub] using hnear.le
    have hW : ‖W‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le (matrixRepresentation π (Fin n)) w).trans hwn
    have herr := clip_reducing_models T W D J' hσ hW hTW hr hra
    have hclip : πB v=cstarClip T := by
      change πB (cstarClip V₀)=cstarClip T
      rw [map_cstarClip]
      congr 1
      calc
        πB V₀ = (Unitization.starLift.symm πB) V :=
          (Unitization.starLift_symm_apply_apply πB V).symm
        _ = lam V := congrArg (fun f => f V) (Unitization.starLift.left_inv lam)
        _ = T := rfl
    refine ⟨⟨HilbertVector (Fin n) K⟩,πB,J',?_,?_⟩
    · rw [hclip]
      exact herr.1.trans hσγ
    · rw [hclip]
      exact herr.2.trans hσγ
  exact hgap B v (norm_cstarClip_le V₀) hB hmodels

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u} : type_of% @OAI.WeakPureInfiniteness.exists_separated_supported_model_any_oai.{u} := @OAI.WeakPureInfiniteness.exists_separated_supported_model_any_oai.{u}
