-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:21:15.238561+00:00
-- url     : https://prove2.me/submissions/ff7e712a-23f2-4fa5-a64a-814c12bd8cab

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W005
import Theorems.Thm_OAI_WeakPureInfiniteness_freeDiagonalFunctional_bound_of_kernel

section
-- module Solutions.OAIQ246_WI.Compat
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FullGroupAlgebra
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

namespace WeakPureInfiniteness

variable {G : Type u} [Group G]

lemma norm_fullGroup_le_iff (x : FullGroupAlgebra G) {c : ℝ} (hc : 0 ≤ c) :
    ‖x‖ ≤ c ↔ ∀ π : GroupRepresentation G, ‖fullGroupEvaluation π x‖ ≤ c := by
  constructor
  · exact fun h π =>
      (NonUnitalStarAlgHom.norm_apply_le (fullGroupEvaluation π).toNonUnitalStarAlgHom x).trans h
  · intro h
    change ‖(x.val : FullGroupAmbient G)‖ ≤ c
    exact lp.norm_le_of_forall_le hc h

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_GroupRegular
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToReduced_element _root_.OAI.WeakPureInfiniteness.tensorSequence_apply _root_.OAI.WeakPureInfiniteness.tensorToHilbertSumMap_tmul
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

namespace WeakPureInfiniteness

variable {G K : Type*}

lemma l2Reindex_single [DecidableEq G] [DecidableEq K] (e : G ≃ K) (g : G) (c : ℂ) :
    l2Reindex e (lp.single 2 g c) = lp.single 2 (e g) c := by
  classical
  ext k
  simp only [l2Reindex_apply, lp.single_apply, Pi.single_apply]
  have he : e.symm k = g ↔ k = e g := e.symm_apply_eq
  simp only [he]

variable [Group G]

lemma leftRegular_single [DecidableEq G] (s g : G) (c : ℂ) :
    (leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) (lp.single 2 g c) =
      lp.single 2 (s * g) c := l2Reindex_single (Equiv.mulLeft s) g c

lemma rightRegular_single [DecidableEq G] (s g : G) (c : ℂ) :
    (rightRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) (lp.single 2 g c) =
      lp.single 2 (g * s⁻¹) c := l2Reindex_single (Equiv.mulRight s⁻¹) g c

lemma groupInversion_intertwines (s : G) (ξ : GroupHilbert G) :
    groupInversion ((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) ξ) =
      (rightRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) (groupInversion ξ) := by
  ext g
  simp [groupInversion]

lemma inner_leftRight_regular_base [DecidableEq G] (s t : G) :
    inner ℂ (lp.single (E := fun _ : G => ℂ) 2 1 1)
      (((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) * rightRegular t)
        (lp.single 2 1 1)) = if s = t then 1 else 0 := by
  classical
  rw [mul_apply_eq_comp, rightRegular_single, leftRegular_single]
  simp only [one_mul, lp.inner_single_left, RCLike.inner_apply,
    map_one, one_mul, lp.single_apply]
  simp [Pi.single_apply, eq_comm, mul_inv_eq_one]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteDiagonalState
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

namespace WeakPureInfiniteness

lemma tensor_inner_smul_smul {E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x y : E ⊗[ℂ] K) (c : ℂ) :
    inner ℂ (c • x) (c • y) = star c * c * inner ℂ x y := by
  calc
    _ = star c * inner ℂ x (c • y) := inner_smul_left x (c • y) c
    _ = star c * (c * inner ℂ x y) := congrArg (star c * ·) (inner_smul_right x y c)
    _ = _ := by ring

variable (F : Type*) [Group F] [Fintype F] [DecidableEq F]

lemma inner_finiteDiagonalVector_translate (s t : F) :
    inner ℂ (finiteDiagonalVector F)
      (TensorProduct.mapL (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteDiagonalVector F)) = if s = t then (Fintype.card F : ℂ) else 0 := by
  classical
  simp only [finiteDiagonalVector, map_sum, TensorProduct.mapL_tmul,
    finiteLeftRegular_single, inner_sum, sum_inner, TensorProduct.inner_tmul,
    EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst]
    apply Finset.sum_eq_zero
    intro g _
    apply Finset.sum_eq_zero
    intro h _
    by_cases hg : h = s * g
    · simp [hg, hst]
    · simp [hg]

lemma normalizedFiniteDiagonalVector_inner_translate (s t : F) :
    inner ℂ (normalizedFiniteDiagonalVector F)
      (TensorProduct.mapL (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (normalizedFiniteDiagonalVector F)) = if s = t then 1 else 0 := by
  classical
  have hc : (Fintype.card F : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hsq : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt hc.le
  let c : ℂ := (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹
  let T := TensorProduct.mapL
    (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
    (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
  have hi := tensor_inner_smul_smul (finiteDiagonalVector F) (T (finiteDiagonalVector F)) c
  have ht := inner_finiteDiagonalVector_translate F s t
  change inner ℂ (c • finiteDiagonalVector F) (T (c • finiteDiagonalVector F)) = _
  rw [map_smul]
  calc
    _ = star c * c * inner ℂ (finiteDiagonalVector F) (T (finiteDiagonalVector F)) := hi
    _ = star c * c * (if s = t then (Fintype.card F : ℂ) else 0) :=
      congrArg (star c * c * ·) ht
    _ = _ := by
      simp only [c, star_inv₀, Complex.star_def, Complex.conj_ofReal]
      by_cases hst : s = t
      · simp only [ite_eq_left hst]
        rw [← hsq]
        have hsc : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
        field_simp
      · simp [hst]

lemma norm_normalizedFiniteDiagonalVector : ‖normalizedFiniteDiagonalVector F‖ = 1 := by
  have h : inner ℂ (normalizedFiniteDiagonalVector F) (normalizedFiniteDiagonalVector F) = 1 := by
    simpa using normalizedFiniteDiagonalVector_inner_translate F 1 1
  calc
    _ = Real.sqrt (Complex.re (inner ℂ (normalizedFiniteDiagonalVector F)
      (normalizedFiniteDiagonalVector F))) :=
      norm_eq_sqrt_re_inner (𝕜 := ℂ) (normalizedFiniteDiagonalVector F)
    _ = 1 := by rw [h]; simp

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpatialVectorStates
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

namespace WeakPureInfiniteness

universe u v

section SpatialVectorStates

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma norm_spatialVectorFunctional_le (π : SpatialRepresentation A B) (ξ : π.space) :
    ‖spatialVectorFunctional π ξ‖ ≤ ‖ξ‖ * ‖ξ‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_self_nonneg _) _

end SpatialVectorStates

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteGroupTensor
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

namespace WeakPureInfiniteness

section TensorConjugation

variable {H K L M : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

lemma tensor_map_conj (e : H ≃ₗᵢ[ℂ] L) (f : K ≃ₗᵢ[ℂ] M)
    (S : H →L[ℂ] H) (T : K →L[ℂ] K) (ξ : H ⊗[ℂ] K) :
    TensorProduct.mapL (e.conjStarAlgEquiv S) (f.conjStarAlgEquiv T)
      (TensorProduct.congrIsometry e f ξ) =
      TensorProduct.congrIsometry e f (TensorProduct.mapL S T ξ) := by
  induction ξ using OAI.tensorInductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorConjugation

section FiniteGroupSpatial

variable {G F : Type u} [Group G] [Group F] [Fintype F] [DecidableEq F]

lemma norm_finiteGroupSpatialDiagonal (q : G →* F) : ‖finiteGroupSpatialDiagonal q‖ = 1 := by
  unfold finiteGroupSpatialDiagonal
  exact (LinearIsometryEquiv.norm_map _ _).trans (norm_normalizedFiniteDiagonalVector F)

lemma finiteGroupSpatialDiagonal_coefficient (q : G →* F) (s t : G) :
    spatialVectorFunctional (finiteGroupSpatialRepresentation q)
      (finiteGroupSpatialDiagonal q : Completion
        (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
      (spatialElementary (fullGroupElement s) (fullGroupElement t)) =
      if q s = q t then (1 : ℂ) else 0 := by
  rw [spatialVectorFunctional_elementary]
  change inner ℂ (TensorProduct.congrIsometry
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F)) (TensorProduct.mapL
    ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv (finiteLeftRegular F (q s)))
    ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv (finiteLeftRegular F (q t)))
    (TensorProduct.congrIsometry
      (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
      (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F))) = _
  rw [tensor_map_conj]
  exact (LinearIsometryEquiv.inner_map_map ..).trans
    (normalizedFiniteDiagonalVector_inner_translate F (q s) (q t))

end FiniteGroupSpatial

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FreeFiniteQuotients
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

namespace WeakPureInfiniteness

open FreeGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma freeBallTranslation_apply (m : ℕ) (a : α) (x : freeWordBall (α := α) m)
    (hx : FreeGroup.of a * x.val ∈ freeWordBall m) :
    (freeBallTranslation m a x).val = FreeGroup.of a * x.val :=
  (exists_freeBallTranslation m a).choose_spec x hx

lemma freeBallTranslation_inv_apply (m : ℕ) (a : α) (x : freeWordBall (α := α) m)
    (hx : (FreeGroup.of a)⁻¹ * x.val ∈ freeWordBall m) :
    ((freeBallTranslation m a)⁻¹ x).val = (FreeGroup.of a)⁻¹ * x.val := by
  let y : freeWordBall (α := α) m := ⟨(FreeGroup.of a)⁻¹ * x.val, hx⟩
  have hy : freeBallTranslation m a y = x := by
    apply Subtype.ext
    rw [freeBallTranslation_apply]
    · simp [y]
    · simp [y, x.property]
  have hiy := congrArg (freeBallTranslation m a).symm hy
  simp only [Equiv.symm_apply_apply] at hiy
  exact congrArg Subtype.val hiy.symm

lemma freeFiniteQuotient_of (m : ℕ) (a : α) :
    freeFiniteQuotient m (FreeGroup.of a) = freeBallTranslation m a := by
  simp [freeFiniteQuotient]

omit [Fintype α] [DecidableEq α] in
lemma free_mk_cons_pos (a : α) (w : List (α × Bool)) :
    FreeGroup.mk ((a, true) :: w) = FreeGroup.of a * FreeGroup.mk w := rfl

omit [Fintype α] [DecidableEq α] in
lemma free_mk_cons_neg (a : α) (w : List (α × Bool)) :
    FreeGroup.mk ((a, false) :: w) = (FreeGroup.of a)⁻¹ * FreeGroup.mk w := rfl

lemma freeFiniteQuotient_word_apply (m : ℕ) (w : List (α × Bool)) (hw : w.length ≤ m) :
    (freeFiniteQuotient m (FreeGroup.mk w) ⟨1, one_mem_freeWordBall m⟩).val =
      FreeGroup.mk w := by
  induction w with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons x w ih =>
    have hw' : w.length ≤ m := (Nat.le_succ w.length).trans hw
    have ih' := ih hw'
    have hmem : FreeGroup.mk (x :: w) ∈ freeWordBall (α := α) m :=
      (mem_freeWordBall _ _).mpr (FreeGroup.norm_mk_le.trans hw)
    rcases x with ⟨a, b⟩
    cases b
    · rw [free_mk_cons_neg] at hmem ⊢
      simp only [_root_.map_mul, _root_.map_inv, freeFiniteQuotient_of, Equiv.Perm.coe_mul,
        Function.comp_apply]
      rw [freeBallTranslation_inv_apply, ih']
      simpa only [ih'] using hmem
    · rw [free_mk_cons_pos] at hmem ⊢
      simp only [_root_.map_mul, freeFiniteQuotient_of, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [freeBallTranslation_apply, ih']
      simpa only [ih'] using hmem

lemma freeFiniteQuotient_apply_base (m : ℕ) (g : FreeGroup α) (hg : g ∈ freeWordBall m) :
    (freeFiniteQuotient m g ⟨1, one_mem_freeWordBall m⟩).val = g := by
  have hw := freeFiniteQuotient_word_apply m g.toWord ((mem_freeWordBall g m).mp hg)
  simpa only [FreeGroup.mk_toWord] using hw

lemma freeFiniteQuotient_injOn_ball (m : ℕ) :
    Set.InjOn (freeFiniteQuotient (α := α) m) (↑(freeWordBall (α := α) m) : Set (FreeGroup α)) := by
  intro x hx y hy h
  have he := congrArg (fun σ : Equiv.Perm (freeWordBall (α := α) m) =>
    (σ ⟨1, one_mem_freeWordBall m⟩).val) h
  simpa only [freeFiniteQuotient_apply_base m x hx,
    freeFiniteQuotient_apply_base m y hy] using he

lemma freeFiniteQuotient_injOn_finset (S : Finset (FreeGroup α)) :
    ∃ m : ℕ, Set.InjOn (freeFiniteQuotient (α := α) m) (↑S : Set (FreeGroup α)) := by
  refine ⟨S.sup FreeGroup.norm, fun x hx y hy h => ?_⟩
  apply freeFiniteQuotient_injOn_ball _ ?_ ?_ h
  · exact (mem_freeWordBall _ _).mpr (Finset.le_sup hx)
  · exact (mem_freeWordBall _ _).mpr (Finset.le_sup hy)

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_GroupPolynomials
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

variable {G : Type*} [Group G]

lemma fullGroupPolynomial_val (c : G →₀ ℂ) :
    (fullGroupPolynomial c).val = c.sum (fun g z => z • fullGroupOperator g) := by
  simp only [fullGroupPolynomial, Finsupp.linearCombination_apply, Finsupp.sum]
  change (fullGroupAmbientInclusion (G := G)) (∑ g ∈ c.support, c g • fullGroupElement g) = _
  simp only [map_sum, map_smul]
  rfl

lemma fullGroupPolynomial_dense : DenseRange (fullGroupPolynomial (G := G)) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx : x.val ∈ (fullGroupSubalgebra G : Set (FullGroupAmbient G)) := x.property
  rw [fullGroupSubalgebra_eq_closure_span] at hx
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨c, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (fullGroupPolynomial c).val‖ < ε
  rw [fullGroupPolynomial_val]
  simpa only [dist_eq_norm] using hdist

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
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

section TensorContinuity

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma spatialElementary_sum_left {I : Type*} (s : Finset I) (a : I → A) (b : B) :
    spatialElementary (∑ i ∈ s, a i) b = ∑ i ∈ s, spatialElementary (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, spatialElementary_add_left, ih]

lemma spatialElementary_sum_right {I : Type*} (s : Finset I) (a : A) (b : I → B) :
    spatialElementary a (∑ i ∈ s, b i) = ∑ i ∈ s, spatialElementary a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, spatialElementary_add_right, ih]

end TensorContinuity

section GroupTensorDensity

variable {G : Type u} [Group G]

lemma groupTensorPolynomial_val (c : G × G →₀ ℂ) :
    (groupTensorPolynomial c).val = c.sum (fun p z => z •
      spatialElementary (fullGroupElement p.1) (fullGroupElement p.2)) := by
  simp only [groupTensorPolynomial, Finsupp.linearCombination_apply, Finsupp.sum]
  change (minimalAmbientInclusion (A := FullGroupAlgebra G) (B := FullGroupAlgebra G))
    (∑ p ∈ c.support, c p • minimalElementary (fullGroupElement p.1) (fullGroupElement p.2)) = _
  simp only [map_sum, map_smul]
  rfl

lemma groupTensorPolynomial_dense : DenseRange (groupTensorPolynomial (G := G)) := by
  let S : Submodule ℂ (SpatialAmbient (FullGroupAlgebra G) (FullGroupAlgebra G)) :=
    Submodule.span ℂ (Set.range fun p : G × G =>
      spatialElementary (fullGroupElement p.1) (fullGroupElement p.2))
  have hgen (s t : G) : spatialElementary (fullGroupElement s) (fullGroupElement t) ∈ S :=
    Submodule.subset_span (Set.mem_range_self (s,t))
  have hpoly (c d : G →₀ ℂ) :
      spatialElementary (fullGroupPolynomial c) (fullGroupPolynomial d) ∈ S := by
    change spatialElementary (c.sum (fun s z => z • fullGroupElement s))
      (d.sum (fun t z => z • fullGroupElement t)) ∈ S
    have hl := spatialElementary_sum_left (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      c.support (fun s => c s • fullGroupElement s) (d.sum (fun t z => z • fullGroupElement t))
    refine hl.symm ▸ ?_
    apply Submodule.sum_mem S
    intro s hs
    have hsm := spatialElementary_smul_left (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      (c s) (fullGroupElement s) (d.sum (fun t z => z • fullGroupElement t))
    refine hsm.symm ▸ ?_
    apply Submodule.smul_mem S
    have hr := spatialElementary_sum_right (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      d.support (fullGroupElement s) (fun t => d t • fullGroupElement t)
    refine hr.symm ▸ ?_
    apply Submodule.sum_mem S
    intro t ht
    have hsm' := spatialElementary_smul_right (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      (d t) (fullGroupElement s) (fullGroupElement t)
    exact hsm'.symm ▸ Submodule.smul_mem S _ (hgen s t)
  have hall (a b : FullGroupAlgebra G) : spatialElementary a b ∈ S.topologicalClosure := by
    refine (fullGroupPolynomial_dense (G := G)).induction_on a ?_ ?_
    · exact S.isClosed_topologicalClosure.preimage (spatialElementaryLeft b).continuous
    · intro c
      refine (fullGroupPolynomial_dense (G := G)).induction_on b ?_ ?_
      · exact S.isClosed_topologicalClosure.preimage (spatialElementaryRight (fullGroupPolynomial c)).continuous
      · intro d
        exact Submodule.le_topologicalClosure S (hpoly c d)
  have hr (x : MinimalTensor (FullGroupAlgebra G) (FullGroupAlgebra G)) : x.val ∈ S.topologicalClosure := by
    have hx : x.val ∈ (minimalTensorSubalgebra (FullGroupAlgebra G) (FullGroupAlgebra G) : Set _) := x.property
    rw [minimalTensor_eq_closure_span] at hx
    exact closure_minimal (Submodule.span_le.mpr (by rintro _ ⟨⟨a,b⟩,rfl⟩; exact hall a b))
      S.isClosed_topologicalClosure hx
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp (hr x) ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨c, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (groupTensorPolynomial c).val‖ < ε
  rw [groupTensorPolynomial_val]
  simpa only [dist_eq_norm] using hd

end GroupTensorDensity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ScalarDiagonal
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToReduced_element _root_.OAI.WeakPureInfiniteness.fullToUniversal_element _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary
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

universe u

section DiagonalPolynomial

variable {G : Type u} [Group G]

lemma finite_diagonal_polynomial (F : Type u) [Group F] [Fintype F] [DecidableEq F]
    (q : G →* F) (c : G × G →₀ ℂ) :
    spatialVectorFunctional (finiteGroupSpatialRepresentation q)
      (finiteGroupSpatialDiagonal q : Completion
        (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
      (groupTensorPolynomial c).val =
      c.sum (fun p z => z • (if q p.1 = q p.2 then (1 : ℂ) else 0)) := by
  rw [groupTensorPolynomial_val]
  simp only [Finsupp.sum, map_sum, map_smul, finiteGroupSpatialDiagonal_coefficient]

lemma finite_diagonal_polynomial_bound (F : Type u) [Group F] [Fintype F] [DecidableEq F]
    (q : G →* F) (c : G × G →₀ ℂ) :
    ‖c.sum (fun p z => z • (if q p.1 = q p.2 then (1 : ℂ) else 0))‖ ≤
      ‖groupTensorPolynomial c‖ := by
  rw [← finite_diagonal_polynomial F q c]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hb := norm_spatialVectorFunctional_le (finiteGroupSpatialRepresentation q)
    (finiteGroupSpatialDiagonal q : Completion
      (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
  simp only [Completion.norm_coe, norm_finiteGroupSpatialDiagonal, one_mul] at hb
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

end DiagonalPolynomial

section FreeDiagonal

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma norm_free_diagonalCoefficient_le (c : FreeGroup α × FreeGroup α →₀ ℂ) :
    ‖diagonalCoefficient c‖ ≤ ‖groupTensorPolynomial c‖ := by
  classical
  let S := c.support.image Prod.fst ∪ c.support.image Prod.snd
  obtain ⟨m, hm⟩ := freeFiniteQuotient_injOn_finset S
  have heq (p : FreeGroup α × FreeGroup α) (hp : p ∈ c.support) :
      freeFiniteQuotient m p.1 = freeFiniteQuotient m p.2 ↔ p.1 = p.2 := by
    constructor
    · exact hm (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
    · rintro h; rw [h]
  have hv : diagonalCoefficient c = c.sum (fun p z =>
      z • (if freeFiniteQuotient m p.1 = freeFiniteQuotient m p.2 then (1 : ℂ) else 0)) := by
    simp only [diagonalCoefficient, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.1 = p.2
    · simp [h]
    · simp [h, not_congr (heq p hp)]
  rw [hv]
  exact finite_diagonal_polynomial_bound _ (freeFiniteQuotient m) c

lemma freeDiagonalFunctional_polynomial (c : FreeGroup α × FreeGroup α →₀ ℂ) :
    freeDiagonalFunctional (groupTensorPolynomial c) = diagonalCoefficient c := by
  apply LinearMap.extendOfNorm_eq groupTensorPolynomial_dense
  exact ⟨1, fun c => by simpa only [one_mul] using norm_free_diagonalCoefficient_le c⟩

lemma freeDiagonalFunctional_group_tensors (s t : FreeGroup α) :
    freeDiagonalFunctional (minimalElementary (fullGroupElement s) (fullGroupElement t)) =
      if s = t then (1 : ℂ) else 0 := by
  have h := freeDiagonalFunctional_polynomial (Finsupp.single (s,t) 1)
  by_cases hst : s = t
  · simpa [hst, groupTensorPolynomial, diagonalCoefficient, Finsupp.linearCombination_single] using h
  · simpa [hst, groupTensorPolynomial, diagonalCoefficient, Finsupp.linearCombination_single] using h

end FreeDiagonal

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_DiagonalRegular
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.contractionEvaluation_generator _root_.OAI.WeakPureInfiniteness.contractionEvaluation_smul _root_.OAI.WeakPureInfiniteness.contractionEvaluation_star _root_.OAI.WeakPureInfiniteness.contractionEvaluation_word _root_.OAI.WeakPureInfiniteness.fullToUniversal_element _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary _root_.OAI.WeakPureInfiniteness.tensorSequence_apply _root_.OAI.WeakPureInfiniteness.tensorToHilbertSumMap_tmul
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

namespace WeakPureInfiniteness

section ContinuousGroupCoefficients

variable {G : Type u} [Group G]

lemma groupCLM_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : FullGroupAlgebra G →L[ℂ] E)
    (h : ∀ s : G, f (fullGroupElement s) = g (fullGroupElement s)) : f = g := by
  apply DFunLike.coe_injective
  apply fullGroupPolynomial_dense.equalizer f.continuous g.continuous
  funext c
  simp only [Function.comp_apply, fullGroupPolynomial, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum, map_smul, h]

lemma rightGroupEvaluation_element (s : G) :
    rightGroupEvaluation (fullGroupElement s) = rightRegular s := by
  apply ContinuousLinearMap.ext
  intro ξ
  change groupInversion ((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G)
    (groupInversion.symm ξ)) = _
  rw [groupInversion_intertwines, LinearIsometryEquiv.apply_symm_apply]

lemma rightGroupEvaluation_eq_zero {b : FullGroupAlgebra G} (hb : fullToReduced b = 0) :
    rightGroupEvaluation b = 0 := by
  have h : fullGroupEvaluation (leftRegularRepresentation G) b = 0 :=
    congrArg Subtype.val hb
  change groupInversion.conjStarAlgEquiv
    (fullGroupEvaluation (leftRegularRepresentation G) b) = 0
  rw [h, map_zero]

end ContinuousGroupCoefficients

section RegularPairing

variable {G : Type u} [Group G]

lemma regularBase_eq [DecidableEq G] :
    regularBase (G := G) = lp.single 2 1 1 := by
  apply Subtype.ext
  funext g
  simp [regularBase, lp.single, Pi.single_apply]

lemma regularPairingRight_apply (a b : FullGroupAlgebra G) :
    regularPairingRight a b = inner ℂ (regularBase (G := G))
      (fullGroupEvaluation (leftRegularRepresentation G) a
        (rightGroupEvaluation b regularBase)) := rfl

end RegularPairing

section FreeRegularPairing

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma freeDiagonalFunctional_regular (a b : FullGroupAlgebra (FreeGroup α)) :
    freeDiagonalFunctional (minimalElementary a b) = regularPairingRight a b := by
  classical
  have hright (s : FreeGroup α) :
      freeDiagonalFunctional.comp (minimalElementaryRight (fullGroupElement s)) =
        regularPairingRight (fullGroupElement s) := by
    apply groupCLM_ext
    intro t
    change freeDiagonalFunctional (minimalElementary (fullGroupElement s) (fullGroupElement t)) =
      regularPairingRight (fullGroupElement s) (fullGroupElement t)
    simp only [freeDiagonalFunctional_group_tensors, regularPairingRight_apply,
      rightGroupEvaluation_element]
    change (if s = t then (1 : ℂ) else 0) = inner ℂ (regularBase (G := FreeGroup α))
      ((leftRegular s : GroupHilbert (FreeGroup α) →L[ℂ] GroupHilbert (FreeGroup α))
        ((rightRegular t : GroupHilbert (FreeGroup α) →L[ℂ] GroupHilbert (FreeGroup α)) regularBase))
    rw [regularBase_eq]
    have hh := inner_leftRight_regular_base s t
    by_cases hst : s = t
    · simpa only [ite_eq_left hst, mul_apply_eq_comp] using hh.symm
    · simpa only [ite_eq_right hst, mul_apply_eq_comp] using hh.symm
  have hleft : freeDiagonalFunctional.comp (minimalElementaryLeft b) = regularPairingLeft b := by
    apply groupCLM_ext
    intro s
    exact DFunLike.congr_fun (hright s) b
  exact DFunLike.congr_fun hleft a

lemma freeDiagonalFunctional_elementary_kernel (a b : FullGroupAlgebra (FreeGroup α))
    (hb : fullToReduced b = 0) :
    freeDiagonalFunctional (minimalElementary a b) = 0 := by
  rw [freeDiagonalFunctional_regular, regularPairingRight_apply,
    rightGroupEvaluation_eq_zero hb]
  simp

end FreeRegularPairing

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducedOperators
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToUniversal_element _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary
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

lemma freeDiagonalFunctional_witness : freeDiagonalFunctional freeDiagonalWitness = 4 := by
  simp only [freeDiagonalWitness, map_sum, freeDiagonalFunctional_group_tensors]
  norm_num [FreeLetter]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NormKernelWitness
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToUniversal_element _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary
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

lemma freeDiagonalFunctional_large_elementary_kernel (a b : FullGroupAlgebra (FreeGroup Bool))
    (hb : fullToReducedLarge b = 0) :
    freeDiagonalFunctional (minimalElementary a b) = 0 :=
  freeDiagonalFunctional_elementary_kernel a b (congrArg ULift.down hb)

lemma freeDiagonalFunctional_witness_gap :
    2 * Real.sqrt 3 < ‖freeDiagonalFunctional freeDiagonalWitness‖ := by
  rw [freeDiagonalFunctional_witness]
  norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FreeFiniteRepresentations
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing _root_.OAI.WeakPureInfiniteness.wordSpace_finiteDimensional
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
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

open FreeGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma extendUnitaryOn_apply (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (U : H ≃ₗᵢ[ℂ] H) (x : K) (hx : U x.val ∈ K) :
    (extendUnitaryOn K U x).val = U x.val := by
  unfold extendUnitaryOn
  exact congrArg Subtype.val (LinearIsometry.extend_apply _ ⟨x,hx⟩)

lemma extendUnitaryOn_symm_apply (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (U : H ≃ₗᵢ[ℂ] H) (x : K) (hx : U.symm x.val ∈ K) :
    ((extendUnitaryOn K U).symm x).val = U.symm x.val := by
  let y : K := ⟨U.symm x.val, hx⟩
  have hy : extendUnitaryOn K U y = x := by
    apply Subtype.ext
    rw [extendUnitaryOn_apply, LinearIsometryEquiv.apply_symm_apply]
    simpa only [y, LinearIsometryEquiv.apply_symm_apply] using x.property
  have he := congrArg (extendUnitaryOn K U).symm hy
  simp only [LinearIsometryEquiv.symm_apply_apply] at he
  exact congrArg Subtype.val he.symm

lemma freeFiniteRepresentation_of (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) (a : α) :
    freeFiniteRepresentation π m ξ (FreeGroup.of a) =
    extendUnitaryOn (freeOrbitSpace π m ξ) (π (FreeGroup.of a)) := by
  simp [freeFiniteRepresentation]

lemma freeFiniteRepresentation_word (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H)
    (w : List (α × Bool)) (hw : w.length ≤ m) :
    (freeFiniteRepresentation π m ξ (FreeGroup.mk w) ⟨ξ, freeOrbitSpace_base π m ξ⟩).val =
      π (FreeGroup.mk w) ξ := by
  induction w with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons x w ih =>
    have hw' : w.length ≤ m := (Nat.le_succ w.length).trans hw
    have ih' := ih hw'
    have hmem : π (FreeGroup.mk (x :: w)) ξ ∈ freeOrbitSpace π m ξ :=
      freeOrbitSpace_mem π m ξ _ ((mem_freeWordBall _ _).mpr (FreeGroup.norm_mk_le.trans hw))
    rcases x with ⟨a,b⟩
    cases b
    · rw [free_mk_cons_neg] at hmem ⊢
      simp only [_root_.map_mul, _root_.map_inv, freeFiniteRepresentation_of,
        LinearIsometryEquiv.coe_mul, Function.comp_apply, LinearIsometryEquiv.coe_inv] at hmem ⊢
      rw [extendUnitaryOn_symm_apply, ih']
      simpa only [ih'] using hmem
    · rw [free_mk_cons_pos] at hmem ⊢
      simp only [_root_.map_mul, freeFiniteRepresentation_of,
        LinearIsometryEquiv.coe_mul, Function.comp_apply] at hmem ⊢
      rw [extendUnitaryOn_apply, ih']
      simpa only [ih'] using hmem

lemma freeFiniteRepresentation_ball (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H)
    (g : FreeGroup α) (hg : g ∈ freeWordBall m) :
    (freeFiniteRepresentation π m ξ g ⟨ξ, freeOrbitSpace_base π m ξ⟩).val = π g ξ := by
  simpa only [FreeGroup.mk_toWord] using
    freeFiniteRepresentation_word π m ξ g.toWord ((mem_freeWordBall g m).mp hg)

lemma norm_freePolynomial_le_of_finite_tests (c : FreeGroup α →₀ ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : FreeGroup α →* V ≃ₗᵢ[ℂ] V),
      ‖c.sum (fun g a => a • (ρ g : V →L[ℂ] V))‖ ≤ C)
    (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) :
    ‖c.sum (fun g a => a • (π g : H →L[ℂ] H))‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro ξ
  let m := c.support.sup FreeGroup.norm
  let K := freeOrbitSpace π m ξ
  let η : K := ⟨ξ, freeOrbitSpace_base π m ξ⟩
  let ρ := freeFiniteRepresentation π m ξ
  have he : (c.sum (fun g a => a • (ρ g : K →L[ℂ] K)) η).val =
      c.sum (fun g a => a • (π g : H →L[ℂ] H)) ξ := by
    simp only [Finsupp.sum, sum_apply, smul_apply,
      Submodule.coe_sum, Submodule.coe_smul_of_tower]
    apply Finset.sum_congr rfl
    intro g hg
    exact congrArg (fun x : H => c g • x)
      (freeFiniteRepresentation_ball π m ξ g ((mem_freeWordBall _ _).mpr (Finset.le_sup hg)))
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm _ η).trans
    (mul_le_mul_of_nonneg_right (h K ρ) (norm_nonneg η))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteUnitaryLog
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

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

lemma finite_spectrum_continuousEnd (T : H →L[ℂ] H) : (spectrum ℂ T).Finite := by
  rw [← finiteContinuousEndAlgEquiv.apply_symm_apply T, AlgEquiv.spectrum_eq]
  exact Module.End.finite_spectrum _

lemma finite_expUnitary_argSelfAdjoint (u : unitary (H →L[ℂ] H)) :
    expUnitary (Unitary.argSelfAdjoint u) = u := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  apply Subtype.ext
  have : ContinuousOn arg (spectrum ℂ (u : H →L[ℂ] H)) :=
    (finite_spectrum_continuousEnd _).continuousOn _
  rw [expUnitary_coe, Unitary.argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : H →L[ℂ] H)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have hh : I * y.arg = log y :=
    Complex.ext (by simp [log_re, hy₁]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, hh] using exp_log (by aesop)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PairUnitary
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

universe u

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma norm_logarithmContraction_le (S T : unitary A) :
    ‖logarithmContraction S T‖ ≤ 1 := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [logarithmContraction, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr hp.le)).trans
  rw [norm_smul, Complex.norm_I, one_mul]
  have hS : ‖(Unitary.argSelfAdjoint S : A)‖ ≤ Real.pi := Unitary.norm_argSelfAdjoint_le_pi S
  have hT : ‖(Unitary.argSelfAdjoint T : A)‖ ≤ Real.pi := Unitary.norm_argSelfAdjoint_le_pi T
  have hn := add_le_add hS hT
  have hn' : ‖(Unitary.argSelfAdjoint S : A)‖ + ‖(Unitary.argSelfAdjoint T : A)‖ ≤
      2 * Real.pi := by simpa only [two_mul] using hn
  exact (mul_le_mul_of_nonneg_left hn' (inv_nonneg.mpr hp.le)).trans_eq
    (inv_mul_cancel₀ (ne_of_gt hp))

lemma realPart_logarithmContraction (S T : unitary A) :
    (2 * Real.pi) • realPart (logarithmContraction S T) = Unitary.argSelfAdjoint S := by
  have hr (h : selfAdjoint A) : realPart (h : A) = h := Subtype.ext h.property.coe_realPart
  simp only [logarithmContraction, map_smul, map_add, realPart_I_smul, hr,
    (Unitary.argSelfAdjoint T).property.imaginaryPart, neg_zero, add_zero, smul_smul]
  rw [mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_smul]

lemma imaginaryPart_logarithmContraction (S T : unitary A) :
    (2 * Real.pi) • imaginaryPart (logarithmContraction S T) = Unitary.argSelfAdjoint T := by
  have hr (h : selfAdjoint A) : realPart (h : A) = h := Subtype.ext h.property.coe_realPart
  simp only [logarithmContraction, map_smul, map_add, imaginaryPart_I_smul, hr,
    (Unitary.argSelfAdjoint S).property.imaginaryPart, zero_add, smul_smul]
  rw [mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_smul]

lemma pairUnitary_logarithmContraction {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (S T : unitary (H →L[ℂ] H)) (b : Bool) :
    pairUnitary (logarithmContraction S T) b = if b then S else T := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  cases b <;> simp only [pairUnitary, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · rw [imaginaryPart_logarithmContraction, finite_expUnitary_argSelfAdjoint]
  · rw [realPart_logarithmContraction, finite_expUnitary_argSelfAdjoint]

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalGroupMap
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

namespace WeakPureInfiniteness

lemma fullToUniversal_evaluation (π : ContractionRepresentation)
    (x : FullGroupAlgebra (FreeGroup Bool)) :
    contractionEvaluation π (fullToUniversal x) = fullGroupEvaluation (pairRepresentation π) x := rfl

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalGroupNorm
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

namespace WeakPureInfiniteness

lemma fullGroupEvaluation_polynomial {G : Type*} [Group G] (π : GroupRepresentation G)
    (c : G →₀ ℂ) : fullGroupEvaluation π (fullGroupPolynomial c) =
      c.sum (fun g a => a • (π.group g : π.hilbert →L[ℂ] π.hilbert)) := by
  simp only [fullGroupPolynomial, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, fullGroupEvaluation_element]

lemma finite_norm_le_fullToUniversal (c : FreeGroup Bool →₀ ℂ)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : FreeGroup Bool →* V ≃ₗᵢ[ℂ] V) :
    ‖c.sum (fun g a => a • (ρ g : V →L[ℂ] V))‖ ≤ ‖fullToUniversal (fullGroupPolynomial c)‖ := by
  classical
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  cases subsingleton_or_nontrivial V with
  | inl h =>
    let := h
    have hz : c.sum (fun g a => a • (ρ g : V →L[ℂ] V)) = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact norm_nonneg _
  | inr h =>
    let := h
    let uρ : FreeGroup Bool →* unitary (V →L[ℂ] V) :=
      Unitary.linearIsometryEquiv.symm.toMonoidHom.comp ρ
    let S := uρ (FreeGroup.of true)
    let T := uρ (FreeGroup.of false)
    let π : ContractionRepresentation :=
      { hilbert := ⟨V⟩
        operator := logarithmContraction S T
        norm_operator_le_one := norm_logarithmContraction_le S T }
    have hpair : pairGroup π.operator = uρ := by
      apply FreeGroup.ext_hom
      intro b
      rw [pairGroup_of]
      change pairUnitary (logarithmContraction S T) b = uρ (FreeGroup.of b)
      rw [pairUnitary_logarithmContraction]
      cases b <;> rfl
    have he : contractionEvaluation π (fullToUniversal (fullGroupPolynomial c)) =
        c.sum (fun g a => a • (ρ g : V →L[ℂ] V)) := by
      rw [fullToUniversal_evaluation,fullGroupEvaluation_polynomial]
      apply Finsupp.sum_congr
      intro g _
      change c g • (pairGroup π.operator g : V →L[ℂ] V) = c g • (ρ g : V →L[ℂ] V)
      rw [hpair]
      rfl
    exact he ▸ NonUnitalStarAlgHom.norm_apply_le (contractionEvaluation π)
      (fullToUniversal (fullGroupPolynomial c))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalGroupEmbedding
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

namespace WeakPureInfiniteness

lemma norm_fullToUniversal_polynomial (c : FreeGroup Bool →₀ ℂ) :
    ‖fullToUniversal (fullGroupPolynomial c)‖ = ‖fullGroupPolynomial c‖ := by
  apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le fullToUniversal _)
  apply (norm_fullGroup_le_iff _ (norm_nonneg _)).mpr
  intro π
  rw [fullGroupEvaluation_polynomial]
  let ρ := Unitary.linearIsometryEquiv.toMonoidHom.comp π.group
  exact norm_freePolynomial_le_of_finite_tests c _ (norm_nonneg _)
    (fun V _ _ _ ρ => finite_norm_le_fullToUniversal c V ρ) ρ

lemma fullToUniversal_continuous : Continuous fullToUniversal :=
  (fullToUniversal.toAlgHom.toLinearMap.mkContinuous 1 (fun x => by
    change ‖fullToUniversal x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le fullToUniversal x)).continuous

lemma norm_fullToUniversal (x : FullGroupAlgebra (FreeGroup Bool)) :
    ‖fullToUniversal x‖ = ‖x‖ := by
  refine (fullGroupPolynomial_dense (G := FreeGroup Bool)).induction_on
    (p := fun y => ‖fullToUniversal y‖ = ‖y‖) x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp fullToUniversal_continuous) continuous_norm
  · exact norm_fullToUniversal_polynomial

theorem fullToUniversal_isometry : Isometry fullToUniversal :=
  AddMonoidHomClass.isometry_of_norm fullToUniversal norm_fullToUniversal

lemma fullToUniversal_injective : Function.Injective fullToUniversal :=
  fullToUniversal_isometry.injective

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordTensorDensity
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
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

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

lemma norm_spatialSum_le_image_any {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ‖∑ i ∈ s,spatialElementary (a i) (c i)‖ ≤
      ‖∑ i ∈ s,spatialElementary (φ (a i)) (ψ (c i))‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let := CStarAlgebra.spectralOrder B
  let := CStarAlgebra.spectralOrderedRing B
  let := CStarAlgebra.spectralOrder D
  let := CStarAlgebra.spectralOrderedRing D
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation B
  obtain ⟨K,ρ,hρ⟩ := exists_faithful_representation D
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro σ
  rw [spatialSum_apply,norm_completion]
  calc
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (σ.leftRep (a i)) (ρ (ψ (c i)))‖ :=
      tensor_norm_le_faithful_finset s (fun i => σ.leftRep (a i)) c
        (ρ.comp ψ) σ.rightRep (hρ.comp hψ)
    _ = ‖∑ i ∈ s,TensorProduct.mapL (ρ (ψ (c i))) (σ.leftRep (a i))‖ := norm_tensorSum_flip s _ _
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (ρ (ψ (c i))) (π (φ (a i)))‖ :=
      tensor_norm_le_faithful_finset s (fun i => ρ (ψ (c i))) a
        (π.comp φ) σ.leftRep (hπ.comp hφ)
    _ = ‖∑ i ∈ s,TensorProduct.mapL (π (φ (a i))) (ρ (ψ (c i)))‖ := norm_tensorSum_flip s _ _
    _ ≤ _ := norm_tensorSum_le_spatial_any s (fun i => φ (a i)) (fun i => ψ (c i)) π ρ

lemma norm_minimalMapAny (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (z : MinimalTensor A C) :
    ‖minimalMapAny φ ψ z‖=‖z‖ := by
  apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le _ _)
  let S := Submodule.span ℂ (Set.range fun p : A × C => minimalElementary p.1 p.2)
  have hd : S.topologicalClosure=⊤ := by
    apply minimal_elementary_span_dense _ (Submodule.isClosed_topologicalClosure _)
    intro a c
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self (a,c)))
  have hz : z ∈ closure (S : Set (MinimalTensor A C)) := by
    change z ∈ S.topologicalClosure
    rw [hd]
    trivial
  apply closure_minimal (t := {z | ‖z‖ ≤ ‖minimalMapAny φ ψ z‖}) ?_
    (isClosed_le continuous_norm ((nonUnitalStarHom_continuous _).norm)) hz
  intro z hz
  classical
  obtain ⟨d,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  change ‖d.sum (fun p t => t • minimalElementary p.1 p.2)‖ ≤
    ‖minimalMapAny φ ψ (d.sum (fun p t => t • minimalElementary p.1 p.2))‖
  simp only [Finsupp.sum,map_sum,map_smul,minimalMapAny_elementary]
  change ‖(minimalTensorSubalgebra A C).subtype (∑ p ∈ d.support,d p • minimalElementary p.1 p.2)‖ ≤
    ‖(minimalTensorSubalgebra B D).subtype (∑ p ∈ d.support,d p • minimalElementary (φ p.1) (ψ p.2))‖
  simp only [map_sum,map_smul]
  change ‖∑ p ∈ d.support,d p • spatialElementary p.1 p.2‖ ≤
    ‖∑ p ∈ d.support,d p • spatialElementary (φ p.1) (ψ p.2)‖
  simpa only [map_smul,spatialElementary_smul_left] using
    norm_spatialSum_le_image_any d.support (fun p => d p • p.1) Prod.snd φ ψ hφ hψ

end

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

end

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

lemma norm_minimalMapLeftAny (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (z : MinimalTensor A C) : ‖minimalMapLeftAny φ z‖=‖z‖ :=
  norm_minimalMapAny φ _ hφ Function.injective_id z

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseKernelHeredity
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

universe u v w

lemma kernel_of_injective_unital {A : Type u} {B : Type v} {C D : Type w}
    [CStarAlgebra A] [CStarAlgebra B] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (q : C →⋆ₙₐ[ℂ] D)
    (hB : ∀ z : MinimalTensor B C, minimalMapAny (NonUnitalStarAlgHom.id ℂ B) q z=0 →
      z.val ∈ tensorKernelIdeal (A := B) q)
    (z : MinimalTensor A C) (hz : minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z=0) :
    z.val ∈ tensorKernelIdeal (A := A) q := by
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
    filter_upwards [hl.eventually_nonneg,hl.eventually_norm] with i hi hn
    refine ⟨?_,hn⟩
    obtain ⟨x,hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hi
    have hi' : e i=star (e x)*e x := congrArg Subtype.val hx
    rw [hi']
    exact star_mul_self_nonneg _
  have happ : ∀ c : C,q c=0 → Tendsto (fun i => c*e i) l (𝓝 c) := by
    intro c hc
    let x : I := ⟨c,hc⟩
    exact continuous_subtype_val.tendsto x |>.comp (hl.tendsto_mul_left x)
  let Φ : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B C := minimalMapLeftAny φ.toNonUnitalStarAlgHom
  have hm : (Φ z).val ∈ tensorKernelIdeal (A := B) q := by
    apply hB
    have heq := minimalMapLeftAny_right_comm φ.toNonUnitalStarAlgHom q
    have hh := DFunLike.congr_fun heq z
    change minimalMapAny (NonUnitalStarAlgHom.id ℂ B) q (Φ z)=minimalMapLeftAny φ.toNonUnitalStarAlgHom (minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q z) at hh
    rw [hh,hz,map_zero]
  have hcuts := tensorCut_tendsto_zero_on_ideal l e he q happ (Φ z) hm
  have hcutz : Tendsto (fun i => tensorCut (e i) z) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := tendsto_zero_iff_norm_tendsto_zero.mp hcuts
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    rw [← minimalMapLeftAny_tensorCut]
    exact (norm_minimalMapLeftAny φ.toNonUnitalStarAlgHom hφ _).symm
  exact tensor_mem_ideal_of_cuts l e q (fun i => i.property) z hcutz

lemma universal_fixed_kernel_impossible_oai
    (h : ∀ z : MinimalTensor UniversalContraction (FullGroupAlgebra (FreeGroup Bool)),
      minimalMapAny (NonUnitalStarAlgHom.id ℂ UniversalContraction)
        fullToReducedLarge.toNonUnitalStarAlgHom z=0 →
      z.val ∈ tensorKernelIdeal (A := UniversalContraction) fullToReducedLarge.toNonUnitalStarAlgHom) : False := by
  apply not_le_of_gt freeDiagonalFunctional_witness_gap
  apply freeDiagonalFunctional_bound_of_kernel
  intro z hz
  have hm := kernel_of_injective_unital fullToUniversal fullToUniversal_injective
    fullToReducedLarge.toNonUnitalStarAlgHom h z ((DFunLike.congr_fun (minimalMapAny_right fullToReducedLarge.toNonUnitalStarAlgHom) z).trans hz)
  apply minimalKernel_induction fullToReducedLarge.toNonUnitalStarAlgHom
    freeDiagonalFunctional.toLinearMap.ker
    (isClosed_singleton.preimage freeDiagonalFunctional.continuous) ?_ z hm
  intro a c hc
  exact freeDiagonalFunctional_large_elementary_kernel a c hc

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution : type_of% @OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible_oai := @OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible_oai
