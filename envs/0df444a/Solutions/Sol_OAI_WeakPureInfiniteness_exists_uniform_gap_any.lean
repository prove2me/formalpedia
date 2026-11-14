-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.exists_uniform_gap_any
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:22:01.211594+00:00
-- url     : https://prove2.me/submissions/d9eb5013-f58e-4c61-961e-2ccc6f6d92cd

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W005
import Theorems.Thm_OAI_WeakPureInfiniteness_universal_fixed_kernel_impossible

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorCut
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

namespace WeakPureInfiniteness

universe u v

section TensorCut

variable {A : Type u} {C : Type v} [CStarAlgebra A] [NonUnitalCStarAlgebra C]

lemma norm_tensorCut_le [PartialOrder C] [StarOrderedRing C]
    (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) (x : MinimalTensor A C) :
    ‖tensorCut e x‖ ≤ ‖x‖ := by
  let := CStarAlgebra.spectralOrder (MinimalTensor A C)
  let := CStarAlgebra.spectralOrderedRing (MinimalTensor A C)
  exact norm_sub_mul_of_pos_contraction x (rightElementaryHom e)
    (map_nonneg (rightElementaryHom (A := A)) he)
    ((NonUnitalStarAlgHom.norm_apply_le (rightElementaryHom (A := A)) e).trans hen)

lemma tensorCut_elementary (e c : C) (a : A) :
    tensorCut e (minimalElementary a c) = minimalElementary a (c - c * e) := by
  apply Subtype.ext
  change spatialElementary a c - spatialElementary a c * spatialElementary 1 e = _
  rw [← spatialElementary_mul, mul_one]
  have h := spatialElementary_add_right a (c-c*e) (c*e)
  rw [sub_add_cancel] at h
  exact sub_eq_iff_eq_add.mpr h

end TensorCut

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorIdealCut
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

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

open Filter Topology

section TensorIdealCut

variable {A : Type u} {C D : Type v} [CStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma cutVanishingSpace_closed [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1) :
    IsClosed (cutVanishingSpace (A := A) l e : Set (MinimalTensor A C)) := by
  apply isClosed_setOf_tendsto_zero_of_bound l (fun i => tensorCutLinear (e i))
  filter_upwards [he] with i hi
  exact norm_tensorCut_le (e i) hi.1 hi.2

lemma tensorCut_tendsto_zero_on_ideal [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1)
    (q : C →⋆ₙₐ[ℂ] D)
    (happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c))
    (x : MinimalTensor A C) (hx : x.val ∈ tensorKernelIdeal (A := A) q) :
    Tendsto (fun i => tensorCut (e i) x) l (𝓝 0) := by
  let S := cutVanishingSpace (A := A) l e
  let j : MinimalTensor A C →ₗ[ℂ] SpatialAmbient A C :=
    { toFun := Subtype.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let T := S.map j
  have hTc : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ (cutVanishingSpace_closed l e he)
  have hgen : ∀ a c, q c = 0 → spatialElementary a c ∈ T := by
    intro a c hc
    refine ⟨minimalElementary a c, ?_, rfl⟩
    change Tendsto (fun i => tensorCut (e i) (minimalElementary a c)) l (𝓝 0)
    simp only [tensorCut_elementary]
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

end TensorIdealCut

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ExactHereditary
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
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

universe u v

section IdealCharacterization

variable {A : Type u} {C D : Type v} [CStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma tensor_mul_kernel_element_mem (q : C →⋆ₙₐ[ℂ] D) (e : C) (he : q e = 0)
    (x : MinimalTensor A C) :
    (x * rightElementaryHom e).val ∈ tensorKernelIdeal (A := A) q := by
  have hs : ∀ z ∈ Submodule.span ℂ
      (Set.range fun p : A × C => spatialElementary p.1 p.2),
      z * spatialElementary (1 : A) e ∈ tensorKernelIdeal (A := A) q := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a,c⟩,rfl⟩ := hz
      rw [← spatialElementary_mul, mul_one]
      apply NonUnitalStarSubalgebra.le_topologicalClosure
      apply NonUnitalStarAlgebra.subset_adjoin ℂ
      exact ⟨a,c*e,by rw [map_mul,he,mul_zero],rfl⟩
    | zero =>
      rw [zero_mul]
      exact (tensorKernelIdeal (A := A) q).zero_mem
    | add z w _ _ hz hw =>
      rw [add_mul]
      exact (tensorKernelIdeal (A := A) q).add_mem hz hw
    | smul c z _ hz =>
      rw [smul_mul_assoc]
      exact (tensorKernelIdeal (A := A) q).smul_mem c hz
  have hc : IsClosed {z : SpatialAmbient A C |
      z * spatialElementary (1 : A) e ∈ tensorKernelIdeal (A := A) q} :=
    isClosed_closure.preimage (continuous_id.mul continuous_const)
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  exact (closure_minimal hs hc) hx

lemma tensor_mem_ideal_of_cuts {ι : Type*} (l : Filter ι) [l.NeBot]
    (e : ι → C) (q : C →⋆ₙₐ[ℂ] D) (he : ∀ i, q (e i) = 0)
    (x : MinimalTensor A C)
    (hx : Tendsto (fun i => tensorCut (e i) x) l (𝓝 0)) :
    x.val ∈ tensorKernelIdeal (A := A) q := by
  have hmul : Tendsto (fun i => x * rightElementaryHom (e i)) l (𝓝 x) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x)).sub hx
    simpa only [tensorCut, sub_sub_cancel, sub_zero] using h
  apply isClosed_closure.mem_of_tendsto (continuous_subtype_val.tendsto x |>.comp hmul)
  exact Filter.Eventually.of_forall (fun i => tensor_mul_kernel_element_mem q (e i) (he i) x)

end IdealCharacterization

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducedGroupAlgebra
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

variable {G : Type u} [Group G]

lemma fullToReduced_surjective : Function.Surjective (fullToReduced (G := G)) := by
  rintro ⟨x, hx⟩
  change ∃ y, fullGroupEvaluation (leftRegularRepresentation G) y = x at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FullGroupDensity
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

namespace WeakPureInfiniteness

universe u

section GroupPolynomialDensity

variable {G : Type u} [Group G]

lemma groupSpan_eq_adjoin : groupSpan (G := G) =
    StarAlgebra.adjoin ℂ (Set.range (fullGroupOperator (G := G))) := by
  apply le_antisymm
  · change Submodule.span ℂ (Set.range (fullGroupOperator (G := G))) ≤
      (StarAlgebra.adjoin ℂ (Set.range (fullGroupOperator (G := G)))).toSubalgebra.toSubmodule
    exact Submodule.span_le.mpr (StarAlgebra.subset_adjoin ℂ _)
  · exact StarAlgebra.adjoin_le (fun _ hx => Submodule.subset_span hx)

lemma fullGroupSubalgebra_eq_closure_span :
    (fullGroupSubalgebra G : Set (FullGroupAmbient G)) =
      closure (Submodule.span ℂ (Set.range (fullGroupOperator (G := G))) : Set (FullGroupAmbient G)) := by
  rw [fullGroupSubalgebra, closedStarSpan, ← groupSpan_eq_adjoin]
  rfl

end GroupPolynomialDensity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducedOperators
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

lemma fullToReducedLarge_surjective : Function.Surjective fullToReducedLarge := by
  intro d
  obtain ⟨b,hb⟩ := fullToReduced_surjective d.down
  exact ⟨b, ULift.down_injective hb⟩

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ProductRepresentation
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

namespace WeakPureInfiniteness

universe u v

section ProductRepresentation

variable {ι : Type u} {H : ι → Type v}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

lemma productRepresentation_injective : Function.Injective (productRepresentation (H := H)) := by
  classical
  intro S T h
  apply Subtype.ext
  funext i
  apply ContinuousLinearMap.ext
  intro ξ
  have he := congrArg (fun F : lp H 2 →L[ℂ] lp H 2 => F (lp.single 2 i ξ) i) h
  change (productAction S (lp.single 2 i ξ)) i = (productAction T (lp.single 2 i ξ)) i at he
  simpa only [productAction_apply, lp.single_apply_self] using he

end ProductRepresentation

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalFreeEmbedding
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing _root_.OAI.WeakPureInfiniteness.universalGraphCStar
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

lemma norm_universalContractionGenerator_le_one : ‖universalContractionGenerator‖ ≤ 1 := by
  change ‖(universalOperator : ContractionAmbient)‖ ≤ 1
  apply lp.norm_le_of_forall_le zero_le_one
  exact fun π => π.norm_operator_le_one

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FaithfulContractions
attribute [-instance] _root_.OAI.WeakPureInfiniteness.universalGraphCStar
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

namespace WeakPureInfiniteness

lemma contractionAmbientRepresentation_injective :
    Function.Injective contractionAmbientRepresentation := productRepresentation_injective

lemma universalFaithfulRepresentation_injective :
    Function.Injective universalFaithfulRepresentation :=
  contractionAmbientRepresentation_injective.comp Subtype.val_injective

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordCompression
attribute [-instance] _root_.OAI.WeakPureInfiniteness.freeOrbitSpace_finite _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.contractionEvaluation_word
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

namespace WeakPureInfiniteness

section Words

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma norm_wordEval_le_one (T : ι → E →L[ℂ] E) (hT : ∀ i, ‖T i‖ ≤ 1)
    (w : List ι) : ‖wordEval T w‖ ≤ 1 := by
  induction w with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons i w ih =>
    calc
      ‖wordEval T (i :: w)‖ ≤ ‖T i‖ * ‖wordEval T w‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (hT i) ih (norm_nonneg _) (by positivity)
      _ = 1 := one_mul _

lemma norm_wordEval_intertwining_le
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →L[ℂ] F)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : ∀ i, ‖D i‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hJ : ∀ i, ‖(T i).comp J - J.comp (D i)‖ ≤ θ)
    (w : List ι) :
    ‖(wordEval T w).comp J - J.comp (wordEval D w)‖ ≤ w.length * θ := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    have hid :
        (wordEval T (i :: w)).comp J - J.comp (wordEval D (i :: w)) =
          (T i).comp ((wordEval T w).comp J - J.comp (wordEval D w)) +
          ((T i).comp J - J.comp (D i)).comp (wordEval D w) := by
      simp only [wordEval, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_assoc]
      abel
    rw [hid]
    calc
      _ ≤ ‖(T i).comp ((wordEval T w).comp J - J.comp (wordEval D w))‖ +
          ‖((T i).comp J - J.comp (D i)).comp (wordEval D w)‖ := norm_add_le _ _
      _ ≤ ‖T i‖ * ‖(wordEval T w).comp J - J.comp (wordEval D w)‖ +
          ‖(T i).comp J - J.comp (D i)‖ * ‖wordEval D w‖ := by
        exact add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 1 * (w.length * θ) + θ * 1 := by
        apply add_le_add
        · exact mul_le_mul (hT i) ih (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hJ i) (norm_wordEval_le_one D hD w) (norm_nonneg _) hθ
      _ = (i :: w).length * θ := by simp [Nat.cast_add, add_mul]

end Words

section Amplification

open scoped TensorProduct

variable {ι K E F : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma amplifiedPolynomial_intertwining
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →L[ℂ] F) :
    (amplifiedPolynomial s B T).comp (J.lTensor K) -
      (J.lTensor K).comp (amplifiedPolynomial s B D) =
      ∑ w ∈ s, TensorProduct.mapL (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w)) := by
  simp only [amplifiedPolynomial, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.mapL_comp_lTensor, ContinuousLinearMap.lTensor_comp_mapL,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [TensorProduct.mapL, ContinuousLinearMap.lTensor_sub, ContinuousLinearMap.comp_sub]

lemma norm_amplifiedPolynomial_intertwining_le
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →L[ℂ] F)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : ∀ i, ‖D i‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hJ : ∀ i, ‖(T i).comp J - J.comp (D i)‖ ≤ θ) :
    ‖(amplifiedPolynomial s B T).comp (J.lTensor K) -
      (J.lTensor K).comp (amplifiedPolynomial s B D)‖ ≤
      (∑ w ∈ s, ‖B w‖ * w.length) * θ := by
  rw [amplifiedPolynomial_intertwining]
  calc
    _ ≤ ∑ w ∈ s, ‖TensorProduct.mapL (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w))‖ := by
      have hs := norm_sum_le s (fun w => TensorProduct.mapL (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w)))
      exact hs
    _ ≤ ∑ w ∈ s, ‖B w‖ * (w.length * θ) := by
      apply Finset.sum_le_sum
      intro w hw
      have hm := TensorProduct.norm_mapL_le (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w))
      have hw := norm_wordEval_intertwining_le T D J hT hD hθ hJ w
      exact hm.trans (mul_le_mul_of_nonneg_left hw (norm_nonneg (B w)))
    _ = _ := by simp only [← mul_assoc, Finset.sum_mul]

lemma norm_amplifiedPolynomial_le
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →ₗᵢ[ℂ] F)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : ∀ i, ‖D i‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hJ : ∀ i, ‖(T i).comp J.toContinuousLinearMap -
        J.toContinuousLinearMap.comp (D i)‖ ≤ θ) :
    ‖amplifiedPolynomial s B D‖ ≤ ‖amplifiedPolynomial s B T‖ +
      (∑ w ∈ s, ‖B w‖ * w.length) * θ := by
  let Q := (J.lTensor K).toContinuousLinearMap
  have hQ : ‖Q‖ ≤ 1 := (J.lTensor K).norm_toContinuousLinearMap_le
  have herr : ‖(amplifiedPolynomial s B T).comp Q -
      Q.comp (amplifiedPolynomial s B D)‖ ≤ (∑ w ∈ s, ‖B w‖ * w.length) * θ :=
    by
      simpa only [Q, LinearIsometry.toContinuousLinearMap_lTensor] using
        norm_amplifiedPolynomial_intertwining_le s B T D J.toContinuousLinearMap hT hD hθ hJ
  calc
    _ = ‖Q.comp (amplifiedPolynomial s B D)‖ :=
      ((J.lTensor K).norm_toContinuousLinearMap_comp).symm
    _ ≤ ‖(amplifiedPolynomial s B T).comp Q‖ +
        ‖(amplifiedPolynomial s B T).comp Q - Q.comp (amplifiedPolynomial s B D)‖ :=
      by
        rw [norm_sub_rev ((amplifiedPolynomial s B T).comp Q)]
        exact norm_le_norm_add_norm_sub' (Q.comp (amplifiedPolynomial s B D))
          ((amplifiedPolynomial s B T).comp Q)
    _ ≤ ‖amplifiedPolynomial s B T‖ * ‖Q‖ +
        (∑ w ∈ s, ‖B w‖ * w.length) * θ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) herr
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_right (norm_nonneg (amplifiedPolynomial s B T)) hQ) le_rfl

end Amplification

section FiniteAmplificationTests

open scoped TensorProduct

variable {ι S K H : Type*} [Finite ι] [Fintype S]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [Finite ι] [Fintype S] in
lemma amplifiedPolynomial_tmul (s : Finset (List ι))
    (B : List ι → K →L[ℂ] K) (T : ι → H →L[ℂ] H) (κ : K) (ξ : H) :
    amplifiedPolynomial s B T (κ ⊗ₜ[ℂ] ξ) =
      ∑ w ∈ s, B w κ ⊗ₜ[ℂ] wordEval T w ξ := by
  simp only [amplifiedPolynomial, sum_apply, TensorProduct.mapL_tmul]

lemma amplifiedPolynomial_compression_exact
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → H →L[ℂ] H) (κ : S → K) (ξ : S → H) {m : ℕ}
    (hm : ∀ w ∈ s, w.length ≤ m) :
    let L := wordSpace T ξ m
    let v : K ⊗[ℂ] L := ∑ j, κ j ⊗ₜ[ℂ] ⟨ξ j, testVector_mem_wordSpace T ξ m j⟩
    (L.subtypeₗᵢ.lTensor K) (amplifiedPolynomial s B (fun i => compress L (T i)) v) =
      amplifiedPolynomial s B T (∑ j, κ j ⊗ₜ[ℂ] ξ j) := by
  dsimp only
  simp only [map_sum, amplifiedPolynomial_tmul, LinearIsometry.lTensor_apply, LinearMap.lTensor_tmul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  exact wordSpace_compression_exact T ξ m w (hm w hw) j

omit [Fintype S] in
lemma norm_amplifiedPolynomial_le_of_finite_compressions
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K) (T : ι → H →L[ℂ] H)
    {M : ℝ} (hM : 0 ≤ M)
    (htest : ∀ (L : Submodule ℂ H) [FiniteDimensional ℂ L],
      ‖amplifiedPolynomial s B (fun i => compress L (T i))‖ ≤ M) :
    ‖amplifiedPolynomial s B T‖ ≤ M := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  obtain ⟨k, κ, ξ, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  let m := s.sup List.length
  have hm : ∀ w ∈ s, w.length ≤ m := fun w hw => Finset.le_sup hw
  let L := wordSpace T ξ m
  let v : K ⊗[ℂ] L := ∑ j, κ j ⊗ₜ[ℂ] ⟨ξ j, testVector_mem_wordSpace T ξ m j⟩
  let Q : (K ⊗[ℂ] L) →ₗᵢ[ℂ] (K ⊗[ℂ] H) := L.subtypeₗᵢ.lTensor K
  have hv : Q v = ∑ j, κ j ⊗ₜ[ℂ] ξ j := by
    simp only [Q, v, LinearIsometry.lTensor_apply, map_sum, LinearMap.lTensor_tmul]
    rfl
  have hp : Q (amplifiedPolynomial s B (fun i => compress L (T i)) v) =
      amplifiedPolynomial s B T (∑ j, κ j ⊗ₜ[ℂ] ξ j) :=
    amplifiedPolynomial_compression_exact s B T κ ξ hm
  rw [← hp, Q.norm_map, ← hv, Q.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (htest L) (norm_nonneg v))

end FiniteAmplificationTests

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalMapping
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing _root_.OAI.WeakPureInfiniteness.universalGraphCStar
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

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma algebraWord_universal (w : List Bool) :
    algebraWord universalContractionGenerator w = universalWord w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [algebraWord, universalWord, ih]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniformModels
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.universalGraphCStar
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

open scoped TensorProduct

lemma unitalRep_universalWord {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UniversalContraction →⋆ₐ[ℂ] (H →L[ℂ] H)) (w : List Bool) :
    π (universalWord w) = wordEval (operatorLetters (π universalContractionGenerator)) w := by
  rw [← algebraWord_universal, map_algebraWord, algebraWord_operator]

lemma operatorLetters_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∀ i, ‖operatorLetters T i‖ ≤ 1 := by
  intro i
  cases i <;> simpa [operatorLetters] using hT

section PolynomialTensorEstimate

variable {B C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma wordTensor_val (s : Finset (List Bool)) (c : List Bool → C) :
    (wordTensor s c).val = ∑ w ∈ s, spatialElementary (universalWord w) (c w) := by
  change (minimalTensorSubalgebra UniversalContraction C).subtype
    (∑ w ∈ s, minimalElementary (universalWord w) (c w)) = _
  rw [map_sum]
  rfl

lemma wordTensorCost_nonneg (s : Finset (List Bool)) (c : List Bool → C) :
    0 ≤ wordTensorCost s c := by
  unfold wordTensorCost
  positivity

end PolynomialTensorEstimate

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordTensorDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

lemma universal_word_span_dense (S : Submodule ℂ UniversalContraction)
    (hS : IsClosed (S : Set UniversalContraction)) (hw : ∀ w, universalWord w ∈ S) :
    S = ⊤ := by
  let f : UniversalContraction →⋆ₐ[ℂ] ContractionAmbient := universalContractionSubalgebra.subtype
  let T : Submodule ℂ ContractionAmbient := S.map f.toLinearMap
  have hT : IsClosed (T : Set ContractionAmbient) :=
    (closedStarSpan_closed {universalOperator}).isClosedMap_subtype_val _ hS
  have hp : ∀ c : List Bool →₀ ℂ, algebraPolynomial universalContractionGenerator c ∈ S := by
    intro c
    unfold algebraPolynomial
    apply S.sum_mem
    intro w _hw
    exact S.smul_mem _ (algebraWord_universal w ▸ hw w)
  have ha : (StarAlgebra.adjoin ℂ {universalOperator} : Set ContractionAmbient) ⊆ T := by
    intro y hy
    obtain ⟨c, rfl⟩ := exists_polynomial_of_mem_adjoin universalOperator y hy
    let z : UniversalContraction := algebraPolynomial universalContractionGenerator c
    refine ⟨z, hp c, ?_⟩
    exact map_algebraPolynomial f universalContractionGenerator c
  apply top_unique
  intro x _hx
  have hxT : x.val ∈ T := (closure_minimal ha hT) x.property
  obtain ⟨y, hy, he⟩ := hxT
  have hey : y = x := Subtype.ext he
  exact hey ▸ hy

section TensorDensity

variable {A : Type*} {C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

lemma minimal_elementary_span_dense (S : Submodule ℂ (MinimalTensor A C))
    (hS : IsClosed (S : Set (MinimalTensor A C)))
    (he : ∀ a c, minimalElementary a c ∈ S) : S = ⊤ := by
  let T : Submodule ℂ (SpatialAmbient A C) :=
    S.map (minimalTensorSubalgebra A C).toSubmodule.subtype
  have hT : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ hS
  have hs : Submodule.span ℂ
      (Set.range fun p : A × C => spatialElementary p.1 p.2) ≤ T := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨a,c⟩,rfl⟩
    exact ⟨minimalElementary a c, he a c, rfl⟩
  apply top_unique
  intro x _hx
  have hx' := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx'
  rw [minimalTensor_eq_closure_span] at hx'
  have hxT : x.val ∈ T := (closure_minimal hs hT) hx'
  obtain ⟨y,hy,he⟩ := hxT
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

end TensorDensity

variable {C : Type*} [NonUnitalCStarAlgebra C]

lemma wordTensorLinear_apply (c : List Bool →₀ C) :
    wordTensorLinear c = ∑ w ∈ c.support, minimalElementary (universalWord w) (c w) := rfl

lemma wordTensorLinear_range_dense : DenseRange (wordTensorLinear (C := C)) := by
  have hd : (LinearMap.range (wordTensorLinear (C := C))).topologicalClosure = ⊤ := by
    apply minimal_elementary_span_dense _ (Submodule.isClosed_topologicalClosure _)
    intro a c
    let S : Submodule ℂ UniversalContraction :=
      (LinearMap.range (wordTensorLinear (C := C))).topologicalClosure.comap
        (minimalElementaryLeftLinear c)
    have hS : IsClosed (S : Set UniversalContraction) :=
      (Submodule.isClosed_topologicalClosure _).preimage (minimalElementaryLeftContinuous c).continuous
    have hw : ∀ w, universalWord w ∈ S := by
      intro w
      apply Submodule.le_topologicalClosure
      refine ⟨Finsupp.single w c, ?_⟩
      exact Finsupp.lsum_single ℂ (fun w => minimalElementaryRightLinear (universalWord w)) w c
    have hall := universal_word_span_dense S hS hw
    have ha : a ∈ S := by rw [hall]; trivial
    exact ha
  apply dense_iff_closure_eq.mpr
  exact congrArg (fun S : Submodule ℂ (MinimalTensor UniversalContraction C) => (S : Set (MinimalTensor UniversalContraction C))) hd

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseTensorLaws
attribute [-simp] _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary
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

open scoped TensorProduct ENNReal

open UniformSpace Topology

universe u v w x y z

section

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma minimalTensor_hom_ext {E : Type*} [NonUnitalCStarAlgebra E]
    (f g : MinimalTensor A C →⋆ₙₐ[ℂ] E)
    (h : ∀ a c, f (minimalElementary a c)=g (minimalElementary a c)) : f=g := by
  let S : Submodule ℂ (MinimalTensor A C) :=
    { carrier := {x | f x=g x}
      zero_mem' := by simp
      add_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq,map_add] at *; rw [ha,hb]
      smul_mem' := by intro t a ha; simp only [Set.mem_ofPred_eq,map_smul] at *; rw [ha] }
  have hS : S=⊤ := minimal_elementary_span_dense S
    (isClosed_eq (nonUnitalStarHom_continuous f) (nonUnitalStarHom_continuous g)) h
  ext a
  have ha : a ∈ S := by rw [hS]; trivial
  exact ha

@[simp] lemma minimalMapAny_id :
    minimalMapAny (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ C)=
      NonUnitalStarAlgHom.id ℂ (MinimalTensor A C) := by
  apply minimalTensor_hom_ext
  intro a c
  simp

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UnitizationTensor
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

open scoped TensorProduct ComplexOrder ENNReal

open UniformSpace

variable {A C D : Type u} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseKernel
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

open TopologicalSpace Topology

universe u v w x y z

section

variable {A : Type u} {C D : Type v} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma minimalMapAny_right (q : C →⋆ₙₐ[ℂ] D) :
    minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q=minimalMapRight (A := A) q := by
  apply minimalTensor_hom_ext
  intro a c
  simp only [minimalMapAny_elementary,minimalMapRight_elementary]
  rfl

lemma minimalKernel_induction (q : C →⋆ₙₐ[ℂ] D)
    (S : Submodule ℂ (MinimalTensor A C)) (hS : IsClosed (S : Set (MinimalTensor A C)))
    (he : ∀ a c, q c=0 → minimalElementary a c ∈ S)
    (z : MinimalTensor A C) (hz : z.val ∈ tensorKernelIdeal (A := A) q) : z ∈ S := by
  let T : Submodule ℂ (SpatialAmbient A C) := S.map (minimalTensorSubalgebra A C).toSubmodule.subtype
  have hT : IsClosed (T : Set (SpatialAmbient A C)) := isClosed_closure.isClosedMap_subtype_val _ hS
  have hs : Submodule.span ℂ {z | ∃ a : A,∃ c : C,q c=0 ∧ z=spatialElementary a c} ≤ T := by
    apply Submodule.span_le.mpr
    rintro y ⟨a,c,hc,rfl⟩
    exact ⟨minimalElementary a c,he a c hc,rfl⟩
  change z.val ∈ (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A C)) at hz
  rw [tensorKernelIdeal_eq_closure_span] at hz
  obtain ⟨y,hy,hyz⟩ := (closure_minimal hs hT) hz
  exact (Subtype.ext hyz : y=z) ▸ hy

lemma exact_kernel_mapAny (hA : Exact A) (C D : Type u)
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (q : C →⋆ₙₐ[ℂ] D) (hq : Function.Surjective q)
    (z : MinimalTensor A C) (hz : minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z=0) :
    z.val ∈ tensorKernelIdeal (A := A) q := by
  apply hA C D q hq z
  exact (minimalMapRight_eq_zero_iff q z).mp (by rw [← minimalMapAny_right]; exact hz)

end

section KernelMap

variable {A : Type u} {B : Type w} {C D : Type v} {E F : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra F]

lemma minimalMapAny_tensorKernel (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] E)
    (q : C →⋆ₙₐ[ℂ] D) (r : E →⋆ₙₐ[ℂ] F) (hqr : ∀ c, q c=0 → r (ψ c)=0)
    (z : MinimalTensor A C) (hz : z.val ∈ tensorKernelIdeal (A := A) q) :
    (minimalMapAny φ ψ z).val ∈ tensorKernelIdeal (A := B) r := by
  let f := (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra B E)).comp (minimalMapAny φ ψ)
  let S := (tensorKernelIdeal (A := B) r).toSubmodule.comap (show MinimalTensor A C →ₗ[ℂ] SpatialAmbient B E from
    { toFun := f, map_add' := map_add f, map_smul' := map_smul f })
  apply minimalKernel_induction q S ?_ ?_ z hz
  · exact isClosed_closure.preimage (nonUnitalStarHom_continuous f)
  · intro a c hc
    change (minimalMapAny φ ψ (minimalElementary a c)).val ∈ tensorKernelIdeal (A := B) r
    rw [minimalMapAny_elementary]
    apply NonUnitalStarSubalgebra.le_topologicalClosure
    apply NonUnitalStarAlgebra.subset_adjoin
    exact ⟨φ a,ψ c,hqr c hc,rfl⟩

end KernelMap

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseLeftMap
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

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma minimalMapLeftAny_tensorCut {A : Type u} {B : Type v}
    [CStarAlgebra A] [CStarAlgebra B] (φ : A →⋆ₐ[ℂ] B) (e : C)
    (x : MinimalTensor A C) :
    minimalMapLeftAny φ.toNonUnitalStarAlgHom (tensorCut e x)=
      tensorCut e (minimalMapLeftAny φ.toNonUnitalStarAlgHom x) := by
  simp only [tensorCut,map_sub,map_mul]
  congr 2
  change minimalMapLeftAny φ.toNonUnitalStarAlgHom (minimalElementary (1:A) e)=minimalElementary (1:B) e
  rw [minimalMapLeftAny_elementary]
  change minimalElementary (φ 1) e=_
  rw [map_one]

lemma minimalMapLeftAny_right_comm {D : Type w} [NonUnitalCStarAlgebra D]
    (φ : A →⋆ₙₐ[ℂ] B) (q : C →⋆ₙₐ[ℂ] D) :
    (minimalMapAny (NonUnitalStarAlgHom.id ℂ B) q).comp (minimalMapLeftAny φ)=
      (minimalMapLeftAny φ).comp (minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q) := by
  apply minimalTensor_hom_ext
  intro a c
  simp [minimalMapLeftAny]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SmallCStar
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

open TopologicalSpace

universe u v

lemma small_of_separable_metric (X : Type u) [MetricSpace X] [SeparableSpace X]
    [Nonempty X] : Small.{0} X := by
  apply small_of_injective (f := fun x : X => fun n : ℕ => dist x (denseSeq X n))
  intro x y h
  have he : (fun z : X => dist x z)=(fun z : X => dist y z) :=
    (denseRange_denseSeq X).equalizer (by fun_prop) (by fun_prop) h
  have hy := congrFun he x
  simpa only [dist_self,eq_comm,dist_eq_zero] using hy

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseSmallExact
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

universe u v

lemma exact_kernel_small (A : Type u) [NonUnitalCStarAlgebra A] (hA : Exact A)
    {C D : Type v} [CStarAlgebra C] [CStarAlgebra D]
    [Small.{0} C] [Small.{0} D]
    (q : C →⋆ₙₐ[ℂ] D) (hq : Function.Surjective q)
    (z : MinimalTensor A C)
    (hz : minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z=0) :
    z.val ∈ tensorKernelIdeal (A := A) q := by
  let E := ULift.{u} (SmallCStarCarrier C)
  let F := ULift.{u} (SmallCStarCarrier D)
  let e : E ≃⋆ₐ[ℂ] C := uliftStarAlgEquiv.trans (smallCStarStarAlgEquiv C)
  let f : F ≃⋆ₐ[ℂ] D := uliftStarAlgEquiv.trans (smallCStarStarAlgEquiv D)
  let r : E →⋆ₙₐ[ℂ] F := f.symm.toNonUnitalStarAlgHom.comp (q.comp e.toNonUnitalStarAlgHom)
  have hr : Function.Surjective r := f.symm.surjective.comp (hq.comp e.surjective)
  let idA := NonUnitalStarAlgHom.id ℂ A
  let Z := minimalMapAny idA e.symm.toNonUnitalStarAlgHom z
  have heq : (minimalMapAny idA r).comp (minimalMapAny idA e.symm.toNonUnitalStarAlgHom)=
      (minimalMapAny idA f.symm.toNonUnitalStarAlgHom).comp (minimalMapAny idA q) := by
    apply minimalTensor_hom_ext
    intro a c
    rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply,
      minimalMapAny_elementary idA e.symm.toNonUnitalStarAlgHom,
      minimalMapAny_elementary idA r, minimalMapAny_elementary idA q,
      minimalMapAny_elementary idA f.symm.toNonUnitalStarAlgHom]
    change minimalElementary a (f.symm (q (e (e.symm c)))) =
      minimalElementary a (f.symm (q c))
    rw [e.apply_symm_apply]
  have hZ : minimalMapAny idA r Z=0 := by
    change ((minimalMapAny idA r).comp (minimalMapAny idA e.symm.toNonUnitalStarAlgHom)) z=0
    rw [heq]
    change minimalMapAny idA f.symm.toNonUnitalStarAlgHom (minimalMapAny idA q z)=0
    rw [hz,map_zero]
  have hm := exact_kernel_mapAny hA E F r hr Z hZ
  have hqr : ∀ c, r c=0 → q (e c)=0 := by
    intro c hc
    change f.symm (q (e c)) = 0 at hc
    have hh := congrArg f hc
    simpa only [StarAlgEquiv.apply_symm_apply, map_zero] using hh
  have hh := minimalMapAny_tensorKernel idA e.toNonUnitalStarAlgHom r q hqr Z hm
  have hi : (minimalMapAny idA e.toNonUnitalStarAlgHom).comp
      (minimalMapAny idA e.symm.toNonUnitalStarAlgHom)=
      NonUnitalStarAlgHom.id ℂ (MinimalTensor A C) := by
    apply minimalTensor_hom_ext
    intro a c
    rw [NonUnitalStarAlgHom.comp_apply,
      minimalMapAny_elementary idA e.symm.toNonUnitalStarAlgHom,
      minimalMapAny_elementary idA e.toNonUnitalStarAlgHom]
    change minimalElementary a (e (e.symm c)) = minimalElementary a c
    rw [e.apply_symm_apply]
  have hzz : minimalMapAny idA e.toNonUnitalStarAlgHom Z=z := DFunLike.congr_fun hi z
  rwa [hzz] at hh

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseUniformModels
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

open scoped TensorProduct

universe u

variable {B : Type u} {C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma minimalMapLeft_wordTensor_any (s : Finset (List Bool)) (c : List Bool → C)
    (φ : UniversalContraction →⋆ₐ[ℂ] B) :
    minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c) =
      ∑ w ∈ s, minimalElementary (φ (universalWord w)) (c w) := by
  rw [wordTensor, map_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  exact minimalMapLeftAny_elementary φ.toNonUnitalStarAlgHom (universalWord w) (c w)

lemma norm_model_amplifiedPolynomial_le_any (s : Finset (List Bool)) (c : List Bool → C)
    (φ : UniversalContraction →⋆ₐ[ℂ] B) (K : ComplexHilbert.{1}) (L : ComplexHilbert.{u})
    (π : B →⋆ₐ[ℂ] (L →L[ℂ] L)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖amplifiedPolynomial s (fun w => σ (c w))
      (operatorLetters (π (φ universalContractionGenerator)))‖ ≤
      ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ := by
  calc
    _ = ‖∑ w ∈ s, TensorProduct.mapL (π (φ (universalWord w))) (σ (c w))‖ := by
      rw [norm_tensorSum_flip]
      unfold amplifiedPolynomial
      congr 1
      apply Finset.sum_congr rfl
      intro w _hw
      congr 1
      exact (unitalRep_universalWord (π.comp φ) w).symm
    _ ≤ ‖∑ w ∈ s,spatialElementary (φ (universalWord w)) (c w)‖ :=
      norm_tensorSum_le_spatial_any s (fun w => φ (universalWord w)) c π.toNonUnitalStarAlgHom σ
    _ = _ := by
      rw [minimalMapLeft_wordTensor_any]
      change _ = ‖(minimalTensorSubalgebra B C).subtype
        (∑ w ∈ s,minimalElementary (φ (universalWord w)) (c w))‖
      rw [map_sum]
      rfl

lemma norm_faithfulAmplifiedPolynomial_le_of_models_any (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModelsAny B v θ) (K : ComplexHilbert.{1})
    (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖amplifiedPolynomial s (fun w => σ (c w))
      (operatorLetters (universalUnitalRepresentation universalContractionGenerator))‖ ≤
      ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ + wordTensorCost s c * θ := by
  have hM : 0 ≤ ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
      wordTensorCost s c * θ := add_nonneg (norm_nonneg _) (mul_nonneg (wordTensorCost_nonneg s c) hθ)
  apply norm_amplifiedPolynomial_le_of_finite_compressions _ _ _ hM
  intro E hE
  let T := universalUnitalRepresentation universalContractionGenerator
  have hT : ‖T‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le universalUnitalRepresentation _).trans
    norm_universalContractionGenerator_le_one
  let H : ComplexHilbert.{1} := { Carrier := E }
  obtain ⟨L, π, J, hj, hjstar⟩ := hmodels H (compress E T) ((norm_compress_le E T).trans hT)
  have hJ : ∀ i : Bool, ‖(operatorLetters (π v) i).comp J.toContinuousLinearMap -
      J.toContinuousLinearMap.comp (operatorLetters (compress E T) i)‖ ≤ θ := by
    intro i
    cases i
    · exact hjstar
    · exact hj
  have hcomp : (fun i => compress E (operatorLetters T i)) = operatorLetters (compress E T) := by
    funext i
    exact (operatorLetters_compress E T i).symm
  rw [hcomp]
  have hπ : ‖π v‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le π v).trans hv
  have hb := norm_amplifiedPolynomial_le s (fun w => σ (c w))
    (operatorLetters (π v)) (operatorLetters (compress E T)) J
    (operatorLetters_norm _ hπ) (operatorLetters_norm _ ((norm_compress_le E T).trans hT)) hθ hJ
  have hcost : (∑ w ∈ s, ‖σ (c w)‖ * w.length) ≤ wordTensorCost s c := by
    apply Finset.sum_le_sum
    intro w hw
    exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le σ _) (Nat.cast_nonneg _)
  apply hb.trans
  apply add_le_add
  · simpa only [hφ] using norm_model_amplifiedPolynomial_le_any s c φ K L π σ
  · exact mul_le_mul_of_nonneg_right hcost hθ

lemma norm_wordTensor_le_of_models_any (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModelsAny B v θ) :
    ‖wordTensor s c‖ ≤ ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
      wordTensorCost s c * θ := by
  let := CStarAlgebra.spectralOrder UniversalContraction
  let := CStarAlgebra.spectralOrderedRing UniversalContraction
  have hM : 0 ≤ ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (wordTensor s c)‖ +
      wordTensorCost s c * θ := add_nonneg (norm_nonneg _) (mul_nonneg (wordTensorCost_nonneg s c) hθ)
  change ‖(wordTensor s c).val‖ ≤ _
  rw [wordTensor_val]
  apply lp.norm_le_of_forall_le hM
  intro ρ
  rw [spatialSum_apply, norm_completion, norm_tensorSum_flip]
  apply (tensor_norm_le_faithful_finset s (fun w => ρ.rightRep (c w)) universalWord
    universalFaithfulRepresentation ρ.leftRep universalFaithfulRepresentation_injective).trans
  have he : ∀ w, universalFaithfulRepresentation (universalWord w) =
      wordEval (operatorLetters (universalUnitalRepresentation universalContractionGenerator)) w :=
    unitalRep_universalWord universalUnitalRepresentation
  simp only [he]
  exact norm_faithfulAmplifiedPolynomial_le_of_models_any s c v hv φ hφ hθ hmodels ρ.right ρ.rightRep

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SmallFree
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

open TopologicalSpace

instance fullGroup_separable {G : Type*} [Group G] [Countable G] :
    SeparableSpace (FullGroupAlgebra G) := by
  have hs : IsSeparable (fullGroupSubalgebra G : Set (FullGroupAmbient G)) := by
    rw [fullGroupSubalgebra_eq_closure_span]
    exact (Set.countable_range (fullGroupOperator (G := G))).isSeparable.span.closure
  exact hs.separableSpace

instance fullGroup_small {G : Type*} [Group G] [Countable G] : Small.{0} (FullGroupAlgebra G) :=
  small_of_separable_metric _

instance reducedFreeLarge_separable : SeparableSpace ReducedFreeLarge := by
  have hs := isSeparable_range (starHom_continuous fullToReducedLarge)
  rw [Set.range_eq_univ.mpr fullToReducedLarge_surjective] at hs
  exact isSeparable_univ_iff.mp hs

instance reducedFreeLarge_small : Small.{0} ReducedFreeLarge := small_of_separable_metric _

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniformGap
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar
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

open Filter

open scoped Topology

section UniformCutEstimate

variable {B C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder C] [StarOrderedRing C] in
lemma tensorCut_wordTensor (s : Finset (List Bool)) (c : List Bool → C) (e : C) :
    tensorCut e (wordTensor s c) = wordTensor s (fun w => c w - c w * e) := by
  change tensorCutLinear e (∑ w ∈ s, minimalElementary (universalWord w) (c w)) = _
  rw [map_sum]
  unfold wordTensor
  apply Finset.sum_congr rfl
  intro w _hw
  exact tensorCut_elementary e (c w) (universalWord w)

lemma wordTensorCost_cut_le (s : Finset (List Bool)) (c : List Bool → C)
    (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) :
    wordTensorCost s (fun w => c w - c w * e) ≤ wordTensorCost s c := by
  unfold wordTensorCost
  apply Finset.sum_le_sum
  intro w _hw
  exact mul_le_mul_of_nonneg_right (norm_sub_mul_of_pos_contraction (c w) e he hen)
    (Nat.cast_nonneg _)

end UniformCutEstimate

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseUniformGap
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

open Filter

open scoped Topology

universe u

section UniformCutEstimate

variable {B : Type u} {C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]

lemma norm_tensorCut_wordTensor_le_of_models_any (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModelsAny B v θ) (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) :
    ‖tensorCut e (wordTensor s c)‖ ≤
      ‖minimalMapLeftAny φ.toNonUnitalStarAlgHom (tensorCut e (wordTensor s c))‖ +
        wordTensorCost s c * θ := by
  rw [tensorCut_wordTensor]
  exact (norm_wordTensor_le_of_models_any s (fun w => c w - c w * e) v hv φ hφ hθ hmodels).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (wordTensorCost_cut_le s c e he hen) hθ))

end UniformCutEstimate

lemma fixed_kernel_universal_of_arbitrarily_good_models
    (hall : ∀ θ : ℝ, 0 < θ → Nonempty (ExactModelDataAny.{u} θ)) {C D : Type 1} [CStarAlgebra C] [CStarAlgebra D]
    [Small.{0} C] [Small.{0} D] (q : C →⋆ₙₐ[ℂ] D) (hq : Function.Surjective q)
    (z : MinimalTensor UniversalContraction C)
    (hz : minimalMapAny (NonUnitalStarAlgHom.id ℂ UniversalContraction) q z=0) :
    z.val ∈ tensorKernelIdeal (A := UniversalContraction) q := by
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
    obtain ⟨x,hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hi
    have hi' : e i = star (e x) * e x := congrArg Subtype.val hx
    rw [hi']
    exact star_mul_self_nonneg _
  have happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c) := by
    intro c hc
    let x : I := ⟨c,hc⟩
    exact continuous_subtype_val.tendsto x |>.comp (hl.tendsto_mul_left x)
  apply tensor_mem_ideal_of_cuts l e q (fun i => i.property) z
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c,hc⟩ := wordTensorLinear_range_dense.exists_dist_lt z (by positivity : 0 < ε/4)
  let s := c.support
  let w := wordTensor s c
  have hzw : ‖z-w‖ < ε/4 := by
    simpa only [dist_eq_norm, wordTensorLinear_apply, w, s, wordTensor] using hc
  let cost := wordTensorCost s c
  have hc0 : 0 ≤ cost := wordTensorCost_nonneg s c
  let θ := (ε/4)/(cost+1)
  have hθ : 0 < θ := div_pos (by positivity) (by positivity)
  have hcost : cost * θ ≤ ε/4 := by
    have heq : (cost+1)*θ = ε/4 := mul_div_cancel₀ _ (by positivity)
    nlinarith [le_of_lt hθ]
  obtain ⟨M⟩ := hall θ hθ
  let := CStarAlgebra.spectralOrder M.Carrier
  let := CStarAlgebra.spectralOrderedRing M.Carrier
  let φ := universalContractionMap M.v M.norm_v
  have hφ : φ universalContractionGenerator = M.v := universalContractionMap_generator _ _
  let Φ : MinimalTensor UniversalContraction C →⋆ₙₐ[ℂ] MinimalTensor M.Carrier C :=
    minimalMapLeftAny φ.toNonUnitalStarAlgHom
  have hmem : (Φ z).val ∈ tensorKernelIdeal (A := M.Carrier) q := by
    apply exact_kernel_small M.Carrier M.exactAlgebra q hq
    have hh := DFunLike.congr_fun (minimalMapLeftAny_right_comm φ.toNonUnitalStarAlgHom q) z
    change minimalMapAny (NonUnitalStarAlgHom.id ℂ M.Carrier) q (Φ z)=
      minimalMapLeftAny φ.toNonUnitalStarAlgHom (minimalMapAny (NonUnitalStarAlgHom.id ℂ UniversalContraction) q z) at hh
    rw [hh,hz,map_zero]
  have hcuts := tensorCut_tendsto_zero_on_ideal l e he q happ (Φ z) hmem
  have hsmall : ∀ᶠ i in l, ‖Φ (tensorCut (e i) z)‖ < ε/4 := by
    have h := Metric.tendsto_nhds.mp hcuts (ε/4) (by positivity)
    filter_upwards [h] with i hi
    simpa only [Φ, minimalMapLeftAny_tensorCut, dist_zero_right] using hi
  filter_upwards [he,hsmall] with i hi his
  rw [dist_zero_right]
  have hdiff : ‖tensorCut (e i) z - tensorCut (e i) w‖ ≤ ‖z-w‖ := by
    change ‖tensorCutLinear (e i) z - tensorCutLinear (e i) w‖ ≤ _
    rw [← map_sub]
    exact norm_tensorCut_le (e i) hi.1 hi.2 (z-w)
  have hΦdiff : ‖Φ (tensorCut (e i) w) - Φ (tensorCut (e i) z)‖ ≤ ‖z-w‖ := by
    rw [← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le Φ _).trans ((norm_sub_rev _ _).le.trans hdiff)
  have hmodel := norm_tensorCut_wordTensor_le_of_models_any s c M.v M.norm_v φ hφ
    (le_of_lt hθ) M.models (e i) hi.1 hi.2
  have hm : ‖Φ (tensorCut (e i) w)‖ ≤ ‖Φ (tensorCut (e i) z)‖ + ‖z-w‖ :=
    (norm_le_norm_add_norm_sub' _ _).trans (add_le_add le_rfl hΦdiff)
  have hn := norm_le_norm_add_norm_sub' (tensorCut (e i) z) (tensorCut (e i) w)
  change ‖tensorCut (e i) w‖ ≤ ‖Φ (tensorCut (e i) w)‖ + cost * θ at hmodel
  linarith

theorem exists_uniform_gap_any_oai :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (B : Type u) [CStarAlgebra B] (v : B),
      ‖v‖ ≤ 1 → Exact B → ¬ FiniteContractionModelsAny B v γ := by
  classical
  by_contra h
  have hall : ∀ θ : ℝ, 0 < θ → Nonempty (ExactModelDataAny.{u} θ) := by
    intro θ hθ
    by_contra hn
    apply h
    refine ⟨θ,hθ,?_⟩
    intro B hB v hv hExact hmodels
    exact hn ⟨{ Carrier := B, v := v, norm_v := hv, exactAlgebra := hExact, models := hmodels }⟩
  exact universal_fixed_kernel_impossible (fixed_kernel_universal_of_arbitrarily_good_models hall
    fullToReducedLarge.toNonUnitalStarAlgHom fullToReducedLarge_surjective)

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u} : type_of% @OAI.WeakPureInfiniteness.exists_uniform_gap_any_oai.{u} := @OAI.WeakPureInfiniteness.exists_uniform_gap_any_oai.{u}
