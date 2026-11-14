-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.exists_square_zero_on_norm_slice_of_gap_any
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:22:00.093132+00:00
-- url     : https://prove2.me/submissions/c0285737-489c-4902-ac30-de42849a3249

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_core_perturbationData
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_finite_coupling_of_gap_any
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_orthogonal_detected_pair

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PureStates
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
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder

section States

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma realStateSpace_isCompact : IsCompact (realStateSpace A) := by
  have h := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ (selfAdjoint A)) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous (1 : selfAdjoint A))
      (continuous_const : Continuous (fun _ : WeakDual ℝ (selfAdjoint A) => (1 : ℝ))))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext f
  change (‖WeakDual.toStrongDual f‖ ≤ 1 ∧ f 1=1) ↔
    (dist (WeakDual.toStrongDual f) 0 ≤ 1 ∧ f 1=1)
  have hd := dist_zero_right (WeakDual.toStrongDual f)
  rw [hd]

variable {A}

lemma exists_norming_real_state [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ∃ f ∈ realStateSpace A,f ⟨b,hb.isSelfAdjoint⟩=‖b‖ := by
  let b' : selfAdjoint A := ⟨b,hb.isSelfAdjoint⟩
  have hn : ‖b'+1‖=‖b‖+1 := norm_add_one_of_nonneg b hb
  obtain ⟨f,hf,hfb⟩ := exists_dual_vector ℝ (b'+1) (by rw [hn]; positivity)
  have hf1 : f 1 ≤ 1 := calc
    f 1 ≤ ‖f 1‖ := Real.le_norm_self _
    _ ≤ ‖f‖*‖(1 : selfAdjoint A)‖ := f.le_opNorm _
    _ = 1 := by rw [hf]; change 1*‖(1 : A)‖=1; simp
  have hfb' : f b' ≤ ‖b‖ := calc
    f b' ≤ ‖f b'‖ := Real.le_norm_self _
    _ ≤ ‖f‖*‖b'‖ := f.le_opNorm _
    _ = ‖b‖ := by rw [hf,one_mul]; rfl
  rw [map_add,hn] at hfb
  change f b'+f 1=‖b‖+1 at hfb
  have hfone : f 1=1 := by linarith
  have hfnorm : f b'=‖b‖ := by linarith
  refine ⟨f,⟨hf.le,hfone⟩,hfnorm⟩

lemma realStateComplexification_apply (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ realStateSpace A) (b : selfAdjoint A) :
    realStateComplexification f hf (b : A)=(f b : ℂ) :=
  positiveComplexification_apply _ _ _ _

lemma realStateComplexification_one (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ realStateSpace A) : realStateComplexification f hf 1=1 := by
  change realStateComplexification f hf ((1 : selfAdjoint A) : A)=1
  rw [realStateComplexification_apply,hf.2,Complex.ofReal_one]

end States

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_VectorStates
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

open scoped Topology ComplexOrder InnerProductSpace

section VectorStates

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma representationVectorFunctional_norm_le (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ‖representationVectorFunctional π ξ‖ ≤ ‖ξ‖^2 := by
  apply (representationVectorFunctional π ξ).opNorm_le_bound (sq_nonneg _)
  intro b
  change ‖(inner ℂ ξ (π (b : A) ξ)).re‖ ≤ ‖ξ‖^2*‖b‖
  calc
    _ ≤ ‖inner ℂ ξ (π (b : A) ξ)‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (inner ℂ ξ (π (b : A) ξ))
    _ ≤ ‖ξ‖*‖π (b : A) ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖*(‖π (b : A)‖*‖ξ‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖ξ‖*(‖(b : A)‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _
    _ = ‖ξ‖^2*‖b‖ := by change ‖ξ‖*(‖b‖*‖ξ‖)=_; ring

lemma representationVectorFunctional_one (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    representationVectorFunctional π ξ 1=‖ξ‖^2 := by
  change (inner ℂ ξ (π 1 ξ)).re=_
  rw [map_one,one_apply_eq_self]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ

variable [PartialOrder A] [StarOrderedRing A]

lemma representationVectorFunctional_square (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    representationVectorFunctional π ξ ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩=
      ‖π a ξ‖^2 := by
  change (inner ℂ ξ (π (star a*a) ξ)).re=_
  rw [map_mul,map_star]
  change (inner ℂ ξ ((π a).adjoint (π a ξ))).re=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

omit [PartialOrder A] [StarOrderedRing A] in
lemma normalized_vector_mem_realStateSpace (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {ξ : H} (hξ : ξ ≠ 0) :
    (StrongDual.toWeakDual ((‖ξ‖^2)⁻¹ • representationVectorFunctional π ξ)) ∈ realStateSpace A := by
  have ht : 0 < ‖ξ‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  constructor
  · change ‖(‖ξ‖^2)⁻¹ • representationVectorFunctional π ξ‖ ≤ 1
    calc
      _ ≤ ‖(‖ξ‖^2)⁻¹‖*‖representationVectorFunctional π ξ‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = (‖ξ‖^2)⁻¹*‖representationVectorFunctional π ξ‖ := by
        rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      _ ≤ (‖ξ‖^2)⁻¹*(‖ξ‖^2) := mul_le_mul_of_nonneg_left
        (representationVectorFunctional_norm_le π ξ) (le_of_lt (inv_pos.mpr ht))
      _ = 1 := inv_mul_cancel₀ ht.ne'
  · change (‖ξ‖^2)⁻¹*representationVectorFunctional π ξ 1=1
    rw [representationVectorFunctional_one,inv_mul_cancel₀ ht.ne']

lemma gns_vectorFunctional_eq (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ realStateSpace A) :
    StrongDual.toWeakDual (representationVectorFunctional
      (realStateComplexification f hf).gnsStarAlgHom
      (gnsCyclicVector (realStateComplexification f hf)))=f := by
  apply DFunLike.ext
  intro b
  change (inner ℂ (gnsCyclicVector (realStateComplexification f hf))
    ((realStateComplexification f hf).gnsStarAlgHom (b : A)
      (gnsCyclicVector (realStateComplexification f hf)))).re=f b
  change (inner ℂ (((realStateComplexification f hf).toPreGNS 1) :
    (realStateComplexification f hf).GNS)
    ((realStateComplexification f hf).gnsNonUnitalStarAlgHom (b : A)
      ((realStateComplexification f hf).toPreGNS 1))).re=f b
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,UniformSpace.Completion.inner_coe]
  change ((realStateComplexification f hf) (star (1 : A)*((b : A)*1))).re=f b
  rw [star_one,one_mul,mul_one,realStateComplexification_apply,Complex.ofReal_re]

end VectorStates

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_InvariantSubspaces
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

open scoped ComplexOrder InnerProductSpace Topology

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma RepresentationInvariant.orthogonal {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    {S : Submodule ℂ H} (hS : RepresentationInvariant π S) :
    RepresentationInvariant π Sᗮ := by
  intro a x hx y hy
  have ho := hx (π (star a) y) (hS (star a) y hy)
  rw [map_star] at ho
  change inner ℂ ((π a).adjoint y) x=0 at ho
  rwa [ContinuousLinearMap.adjoint_inner_left] at ho

lemma RepresentationInvariant.projection_commutes {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    {S : Submodule ℂ H} [S.HasOrthogonalProjection] (hS : RepresentationInvariant π S)
    (a : A) (x : H) : S.starProjection (π a x)= π a (S.starProjection x) := by
  apply S.eq_starProjection_of_mem_orthogonal
  · exact hS a _ (S.starProjection_apply_mem x)
  · rw [← map_sub]
    exact hS.orthogonal a _ (S.sub_starProjection_mem_orthogonal x)

lemma RepresentationInvariant.vectorFunctional_decomposition {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    {S : Submodule ℂ H} [S.HasOrthogonalProjection] (hS : RepresentationInvariant π S)
    (x : H) : representationVectorFunctional π x =
      representationVectorFunctional π (S.starProjection x)+
        representationVectorFunctional π (Sᗮ.starProjection x) := by
  ext b
  change (inner ℂ x (π (b : A) x)).re=
    (inner ℂ (S.starProjection x) (π (b : A) (S.starProjection x))).re+
    (inner ℂ (Sᗮ.starProjection x) (π (b : A) (Sᗮ.starProjection x))).re
  have hxy : inner ℂ (S.starProjection x) (π (b : A) (Sᗮ.starProjection x))=0 :=
    hS.orthogonal (b : A) _ (Sᗮ.starProjection_apply_mem x) _ (S.starProjection_apply_mem x)
  have hyx : inner ℂ (Sᗮ.starProjection x) (π (b : A) (S.starProjection x))=0 :=
    inner_eq_zero_symm.mpr ((Sᗮ.starProjection_apply_mem x) _ (hS (b : A) _ (S.starProjection_apply_mem x)))
  conv_lhs => rw [← S.starProjection_add_starProjection_orthogonal x]
  simp only [map_add,inner_add_left,inner_add_right,hxy,hyx,add_zero,zero_add,Complex.add_re]

variable [PartialOrder A] [StarOrderedRing A]

lemma gnsAction_cyclic_eq (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsCyclicVector f)=(f.toPreGNS a : f.GNS) := by
  change f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1 : f.GNS)=_
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  change ((f.toPreGNS (a*1)) : f.GNS)=_
  rw [mul_one]

lemma gnsAction_cyclic_dense (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsCyclicVector f)) := by
  have hr : Set.range (fun a : A => f.gnsStarAlgHom a (gnsCyclicVector f))=
      Set.range (fun a : f.PreGNS => (a : f.GNS)) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨f.toPreGNS a,(gnsAction_cyclic_eq f a).symm⟩
    · rintro ⟨a,rfl⟩
      refine ⟨f.ofPreGNS a,?_⟩
      change f.gnsStarAlgHom (f.ofPreGNS a) (gnsCyclicVector f)=(a : f.GNS)
      rw [gnsAction_cyclic_eq,PositiveLinearMap.toPreGNS_ofPreGNS]
  change Dense (Set.range _)
  rw [hr]
  exact UniformSpace.Completion.denseRange_coe

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_AnnihilatorStates
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

open scoped ComplexOrder InnerProductSpace Topology

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma realState_nonneg {f : WeakDual ℝ (selfAdjoint A)} (hf : f ∈ realStateSpace A)
    {a : A} (ha : 0 ≤ a) : 0 ≤ f ⟨a,ha.isSelfAdjoint⟩ := by
  have h := (realStateComplexification f hf).map_nonneg ha
  rw [realStateComplexification_apply f hf ⟨a,ha.isSelfAdjoint⟩] at h
  exact (Complex.le_def.mp h).1

lemma annihilatorStates_isCompact (S : Set A) : IsCompact (annihilatorStates S) := by
  apply (realStateSpace_isCompact A).inter_right
  show IsClosed {f : WeakDual ℝ (selfAdjoint A) | ∀ x ∈ S,∀ a : A,
    f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0}
  have he : {f : WeakDual ℝ (selfAdjoint A) | ∀ x ∈ S,∀ a : A,
    f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0} =
    ⋂ x : A,⋂ _hx : x ∈ S,⋂ a : A,{f : WeakDual ℝ (selfAdjoint A) |
      f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0} := by
    ext f
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
  rw [he]
  exact isClosed_iInter (fun x : A => isClosed_iInter (fun _hx : x ∈ S =>
    isClosed_iInter (fun a : A => isClosed_eq
      (WeakDual.eval_continuous (⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩ : selfAdjoint A))
      (continuous_const : Continuous (fun _ : WeakDual ℝ (selfAdjoint A) => (0 : ℝ))))))

lemma annihilatorStates_isExtreme (S : Set A) : IsExtreme ℝ (realStateSpace A) (annihilatorStates S) := by
  constructor
  · exact fun _ hf => hf.1
  · intro g hg k hk f hf hseg
    obtain ⟨t,s,ht,hs,hts,he⟩ := hseg
    have hz : ∀ x ∈ S,∀ a : A,g ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0 := by
      intro x hx a
      have hv := DFunLike.congr_fun he ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩
      change t*g _+s*k _=f _ at hv
      rw [hf.2 x hx a] at hv
      have hg0 := realState_nonneg hg (star_mul_self_nonneg (x*a))
      have hk0 := realState_nonneg hk (star_mul_self_nonneg (x*a))
      nlinarith
    exact ⟨hg,hz⟩

lemma annihilatorStates_gns_zero {S : Set A} {f : WeakDual ℝ (selfAdjoint A)}
    (hf : f ∈ annihilatorStates S) {x : A} (hx : x ∈ S) :
    (realStateComplexification f hf.1).gnsStarAlgHom x=0 := by
  let Φ := realStateComplexification f hf.1
  let Ω := gnsCyclicVector Φ
  have hzero : ∀ η : Φ.GNS,Φ.gnsStarAlgHom x η=0 :=
    isClosed_property (gnsAction_cyclic_dense Φ)
      (isClosed_eq (Φ.gnsStarAlgHom x).continuous continuous_const) (by
        intro a
        have he := DFunLike.congr_fun (gns_vectorFunctional_eq f hf.1)
          ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩
        change representationVectorFunctional Φ.gnsStarAlgHom Ω _=f _ at he
        rw [representationVectorFunctional_square,hf.2 x hx a] at he
        have hn : Φ.gnsStarAlgHom (x*a) Ω=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
        simpa only [map_mul,mul_apply_eq_comp] using hn)
  ext η
  exact hzero η

theorem exists_extreme_annihilator_state {S : Set A} {g : WeakDual ℝ (selfAdjoint A)}
    (hg : g ∈ annihilatorStates S) (b : selfAdjoint A) :
    ∃ f ∈ (realStateSpace A).extremePoints ℝ,
      f ∈ annihilatorStates S ∧ g b ≤ f b := by
  let F := annihilatorStates S
  let T := {f ∈ F | ∀ h ∈ F,h b ≤ f b}
  have hT : T.Nonempty := by
    obtain ⟨f,hf,hm⟩ := (annihilatorStates_isCompact S).exists_isMaxOn ⟨g,hg⟩
      (WeakDual.eval_continuous b).continuousOn
    exact ⟨f,hf,hm⟩
  have he : IsExposed ℝ F T := by
    intro _
    exact ⟨realStateEvaluation b,rfl⟩
  let : LocallyConvexSpace ℝ (WeakDual ℝ (selfAdjoint A)) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℝ (selfAdjoint A))))
  obtain ⟨f,hf⟩ := (he.isCompact (annihilatorStates_isCompact S)).extremePoints_nonempty hT
  refine ⟨f,(annihilatorStates_isExtreme S).extremePoints_subset_extremePoints
    (he.isExtreme.extremePoints_subset_extremePoints hf),hf.1.1,hf.1.2 g hg⟩

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SmallPartition
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

open scoped BigOperators Topology

lemma exists_small_partition (K : Set ℝ) (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ c : Fin n → ℝ, ∃ f : Fin n → C(ℝ,ℝ),
      (∀ i, tsupport (f i) ⊆ Metric.ball (c i) δ) ∧
      (∀ x ∈ K, ∑ i,f i x=1) ∧ (∀ i x,0 ≤ f i x ∧ f i x ≤ 1) := by
  classical
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun c : ℝ => Metric.ball c δ)
    (fun _ => Metric.isOpen_ball) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x,by simpa using hδ⟩)
  let e : Fin s.card ≃ s := by simpa using (Fintype.equivFin s).symm
  let c : Fin s.card → ℝ := fun i => (e i).val
  have hcover : K ⊆ ⋃ i, Metric.ball (c i) δ := by
    intro x hx
    obtain ⟨y,hxy⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hy',hxy'⟩ := Set.mem_iUnion.mp hxy
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨y,hy'⟩,by simpa [c] using hxy'⟩
  obtain ⟨f,hf,hfs,hn,_⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (s := fun i : Fin s.card => Metric.ball (c i) δ)
    (fun _ => Metric.isOpen_ball) hK hcover
  refine ⟨s.card,c,f,hf,?_,hn⟩
  intro x hx
  simpa using hfs hx

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralDeletion
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

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



open scoped BigOperators CStarAlgebra

section PositiveDiagonal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_mul_eq_zero_of_sandwich_eq_zero {a e : A} (ha : 0 ≤ a)
    (he : IsSelfAdjoint e) (h : e*a*e=0) : CFC.sqrt a*e=0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  rw [star_mul,he.star_eq,(CFC.sqrt_nonneg a).star_eq]
  calc
    (e*CFC.sqrt a)*(CFC.sqrt a*e)=e*(CFC.sqrt a*CFC.sqrt a)*e := by noncomm_ring
    _ = 0 := by rw [CFC.sqrt_mul_sqrt_self a ha,h]

end PositiveDiagonal

section UnitPartition

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type*} [Fintype ι]

lemma eq_zero_of_nonneg_of_partition_diagonals {a : A} (ha : 0 ≤ a)
    (e : ι → A) (he : ∀ i, IsSelfAdjoint (e i)) (hs : ∑ i,e i=1)
    (hd : ∀ i,e i*a*e i=0) : a=0 := by
  have hz : CFC.sqrt a=0 := by
    calc
      CFC.sqrt a=CFC.sqrt a*(∑ i,e i) := by rw [hs,mul_one]
      _ = ∑ i,CFC.sqrt a*e i := Finset.mul_sum ..
      _ = 0 := by simp only [sqrt_mul_eq_zero_of_sandwich_eq_zero ha (he _) (hd _),
        Finset.sum_const_zero]
  exact (CFC.sqrt_eq_zero_iff a ha).mp hz

lemma both_signs_of_partition_diagonals {a : A} (ha : IsSelfAdjoint a) (hne : a ≠ 0)
    (e : ι → A) (he : ∀ i, IsSelfAdjoint (e i)) (hs : ∑ i,e i=1)
    (hd : ∀ i,e i*a*e i=0) : a⁺ ≠ 0 ∧ a⁻ ≠ 0 := by
  constructor
  · intro h
    have han : 0 ≤ -a := neg_nonneg.mpr ((CFC.posPart_eq_zero_iff a ha).mp h)
    have hz := eq_zero_of_nonneg_of_partition_diagonals han e he hs (by simpa using hd)
    exact hne (neg_eq_zero.mp hz)
  · intro h
    exact hne (eq_zero_of_nonneg_of_partition_diagonals
      ((CFC.negPart_eq_zero_iff a ha).mp h) e he hs hd)

end UnitPartition

section FiniteDeletion

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {ι κ : Type*} [Fintype ι]

lemma finiteDeletion_selfAdjoint (f : ι → A) (V : A) (R : ι → ι → Prop)
    [DecidableRel R] (hf : ∀ j, IsSelfAdjoint (f j)) (hV : IsSelfAdjoint V)
    (hR : ∀ j k,R j k ↔ R k j) : IsSelfAdjoint (finiteDeletion f V R) := by
  show star (finiteDeletion f V R)=finiteDeletion f V R
  simp only [finiteDeletion, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : R j k
  · rw [ite_eq_left h,ite_eq_left ((hR j k).mp h),star_mul,star_mul,(hf j).star_eq,
      (hf k).star_eq,hV.star_eq]
    noncomm_ring
  · rw [ite_eq_right h,ite_eq_right (by simpa only [← hR j k] using h),star_zero]

lemma finiteDeletion_diagonals (f : ι → A) (V : A) (R : ι → ι → Prop)
    [DecidableRel R] (e : κ → A)
    (h : ∀ l j k,R j k → e l*f j=0 ∨ f k*e l=0) :
    ∀ l,e l*finiteDeletion f V R*e l=0 := by
  intro l
  simp only [finiteDeletion,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  by_cases hjk : R j k
  · rw [ite_eq_left hjk]
    rcases h l j k hjk with hleft | hright
    · rw [← mul_assoc,← mul_assoc,hleft,zero_mul,zero_mul,zero_mul]
    · calc
        e l*(f j*V*f k)*e l=e l*f j*V*(f k*e l) := by noncomm_ring
        _ = 0 := by rw [hright,mul_zero]
  · simp only [ite_eq_right hjk,mul_zero,zero_mul]

end FiniteDeletion


variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} [Fintype ι]

lemma finiteDeletion_preserves_corner (f : ι → A) (V p q : A)
    (R : ι → ι → Prop) [DecidableRel R] (hs : ∑ i,f i=1)
    (h : ∀ j k,¬R j k → p*f j=0 ∨ f k*q=0) :
    p*finiteDeletion f V R*q=p*V*q := by
  calc
    p*finiteDeletion f V R*q=∑ j,∑ k,p*(f j*V*f k)*q := by
      simp only [finiteDeletion,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hjk : R j k
      · rw [ite_eq_left hjk]
      · rw [ite_eq_right hjk,mul_zero,zero_mul]
        rcases h j k hjk with hleft | hright
        · rw [← mul_assoc,← mul_assoc,hleft,zero_mul,zero_mul,zero_mul]
        · symm
          calc
            p*(f j*V*f k)*q=p*f j*V*(f k*q) := by noncomm_ring
            _ = 0 := by rw [hright,mul_zero]
    _ = p*((∑ j,f j)*V*(∑ k,f k))*q := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      exact Finset.sum_comm
    _ = p*V*q := by rw [hs,one_mul,mul_one]




end WeakPureInfiniteness

end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ContinuousDeletion
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
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped BigOperators Topology CStarAlgebra

section CFCDeletion

variable {A : Type*} [CStarAlgebra A]

lemma cfc_partition_sum (U : A) (hU : IsSelfAdjoint U)
    {ι : Type*} [Fintype ι] (f : ι → C(ℝ,ℝ))
    (hs : ∀ x ∈ spectrum ℝ U,∑ i,f i x=1) : ∑ i,cfc (f i) U=1 := by
  rw [← cfc_sum_univ (fun i => ⇑(f i)) U (fun i => (f i).continuous.continuousOn)]
  calc
    cfc (∑ i,⇑(f i)) U=cfc (fun _ : ℝ => 1) U := by
      apply cfc_congr
      intro x hx
      simpa using hs x hx
    _ = 1 := by rw [cfc_const_one ℝ U hU]

lemma cfc_mul_eq_zero_of_small_supports (U : A)
    (f g : C(ℝ,ℝ)) (c d δ : ℝ)
    (hf : tsupport f ⊆ Metric.ball c δ) (hg : tsupport g ⊆ Metric.ball d δ)
    (hcd : 2*δ ≤ dist c d) : cfc f U*cfc g U=0 := by
  rw [← cfc_mul f g U f.continuous.continuousOn g.continuous.continuousOn]
  calc
    cfc (fun x => f x*g x) U=cfc (fun _ : ℝ => 0) U := by
      apply cfc_congr
      intro x _
      by_cases hfx : f x=0
      · simp only [hfx,zero_mul]
      by_cases hgx : g x=0
      · simp only [hgx,mul_zero]
      have hx1 : dist x c < δ := hf (subset_tsupport f hfx)
      have hx2 : dist x d < δ := hg (subset_tsupport g hgx)
      have ht := dist_triangle c x d
      rw [dist_comm c x] at ht
      exfalso
      linarith
    _ = 0 := cfc_zero ℝ U

lemma vanishes_on_separated_sets (f g : C(ℝ,ℝ)) (c d δ : ℝ)
    (hf : tsupport f ⊆ Metric.ball c δ) (hg : tsupport g ⊆ Metric.ball d δ)
    (S T : Set ℝ) (hsep : ∀ x ∈ S,∀ y ∈ T,8*δ ≤ dist x y)
    (hcd : ¬4*δ < dist c d) :
    (∀ x ∈ S,f x=0) ∨ (∀ y ∈ T,g y=0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x,hx,hfx⟩,⟨y,hy,hgy⟩⟩ := h
  have hxc : dist x c < δ := hf (subset_tsupport f hfx)
  have hyd : dist y d < δ := hg (subset_tsupport g hgy)
  have ht1 := dist_triangle x c y
  have ht2 := dist_triangle c d y
  rw [dist_comm d y] at ht2
  have hs := hsep x hx y hy
  have h0 : 0 < δ := lt_of_le_of_lt (dist_nonneg) hxc
  have hc := le_of_not_gt hcd
  linarith

end CFCDeletion

section Images

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

lemma both_signs_in_image_of_partition_diagonals (π : A →⋆ₐ[ℂ] B)
    {a : A} (ha : IsSelfAdjoint a) (hne : π a ≠ 0)
    {ι : Type*} [Fintype ι] (e : ι → A) (he : ∀ i,IsSelfAdjoint (e i))
    (hs : ∑ i,e i=1) (hd : ∀ i,e i*a*e i=0) :
    (π a)⁺ ≠ 0 ∧ (π a)⁻ ≠ 0 := by
  apply both_signs_of_partition_diagonals (ha.map π) hne (fun i => π (e i))
    (fun i => (he i).map π)
  · rw [← map_sum,hs,map_one]
  · intro i
    simpa only [map_mul,map_zero] using congrArg π (hd i)

end Images

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Hereditary
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
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

open Filter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma sandwich_mem (h b : A) (hh : IsSelfAdjoint h) : h*b*h ∈ hereditarySubalgebra h hh :=
  (sandwichSubalgebra h hh).le_topologicalClosure ⟨b, rfl⟩

lemma residual_nonneg (e h : A) (he : IsSelfAdjoint e) (hh : 0 ≤ h) :
    0 ≤ residual e h := by
  have hs : CFC.sqrt h * CFC.sqrt h = h := CFC.sqrt_mul_sqrt_self h hh
  convert mul_star_self_nonneg (CFC.sqrt h-e*CFC.sqrt h) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [residual, star_sub, star_mul, (CFC.sqrt_nonneg h).star_eq, he.star_eq]
  rw [show (CFC.sqrt h-e*CFC.sqrt h) * (CFC.sqrt h-CFC.sqrt h*e) =
    CFC.sqrt h*CFC.sqrt h-e*(CFC.sqrt h*CFC.sqrt h) -
      (CFC.sqrt h*CFC.sqrt h)*e+e*(CFC.sqrt h*CFC.sqrt h)*e by noncomm_ring, hs]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CoreSelection
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positiveCut_eq_zero_of_norm_le {B : Type*} [CStarAlgebra B]
    (b : B) {α : ℝ} (hα : 0 ≤ α) (hbn : ‖b‖ ≤ α) : positiveCut α b=0 := by
  obtain hB | hB := subsingleton_or_nontrivial B
  · exact Subsingleton.elim _ _
  let : Nontrivial B := hB
  change cfcₙ (fun s : ℝ => max (s-α) 0) b=0
  calc
    cfcₙ (fun s : ℝ => max (s-α) 0) b=cfcₙ (0 : ℝ → ℝ) b := by
      apply cfcₙ_congr
      intro s hs
      change max (s-α) 0=0
      apply max_eq_right
      rcases mem_quasispectrum_iff.mp hs with rfl | hs
      · linarith
      · have := spectrum.norm_le_norm_of_mem hs
        have := Real.le_norm_self s
        linarith
    _ = 0 := cfcₙ_zero ℝ b

lemma norm_lt_of_positiveCut_image_ne_zero
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {c : A} (hc : 0 ≤ c) {α : ℝ} (hα : 0 ≤ α)
    (hn : π (positiveCut α c) ≠ 0) : α < ‖π c‖ := by
  have he : π (positiveCut α c)=positiveCut α (π c) :=
    π.map_cfcₙ (fun s : ℝ => max (s-α) 0) c (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hc.isSelfAdjoint (map_nonneg π hc).isSelfAdjoint
  rw [he] at hn
  exact lt_of_not_ge (fun h => hn (positiveCut_eq_zero_of_norm_le _ hα h))

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PureIrreducible
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

open scoped ComplexOrder InnerProductSpace Topology

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma RepresentationInvariant.eq_bot_of_projected_cyclic_zero
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {S : Submodule ℂ H} [S.HasOrthogonalProjection]
    (hS : RepresentationInvariant π S) (Ω : H)
    (hd : DenseRange (fun a : A => π a Ω)) (hΩ : S.starProjection Ω=0) : S=⊥ := by
  have hzero : ∀ x : H,S.starProjection x=0 := isClosed_property hd
    (isClosed_eq S.starProjection.continuous continuous_const) (by
      intro a
      rw [hS.projection_commutes,hΩ,map_zero])
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    rw [← S.starProjection_eq_self_iff.mpr hx]
    exact hzero x
  · exact bot_le

variable [PartialOrder A] [StarOrderedRing A]

theorem irreducible_of_extreme_cyclic_vector_state
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (hΩ : ‖Ω‖=1)
    (hd : DenseRange (fun a : A => π a Ω))
    (hf : StrongDual.toWeakDual (representationVectorFunctional π Ω) ∈
      (realStateSpace A).extremePoints ℝ) : RepresentationIrreducible π := by
  intro S hSc hS
  let : CompleteSpace S := hSc.isComplete.completeSpace_coe
  by_cases h0 : S.starProjection Ω=0
  · exact Or.inl (hS.eq_bot_of_projected_cyclic_zero Ω hd h0)
  by_cases h1 : Sᗮ.starProjection Ω=0
  · right
    have he : Sᗮ=⊥ := hS.orthogonal.eq_bot_of_projected_cyclic_zero Ω hd h1
    have he' := congrArg Submodule.orthogonal he
    simpa using he'
  exfalso
  let t : ℝ := ‖S.starProjection Ω‖^2
  let s : ℝ := ‖Sᗮ.starProjection Ω‖^2
  have ht : 0 < t := sq_pos_of_pos (norm_pos_iff.mpr h0)
  have hs : 0 < s := sq_pos_of_pos (norm_pos_iff.mpr h1)
  have hts : t+s=1 := by
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection Ω S
    rw [hΩ,one_pow] at h
    exact h.symm
  let g := StrongDual.toWeakDual (t⁻¹ • representationVectorFunctional π (S.starProjection Ω))
  let k := StrongDual.toWeakDual (s⁻¹ • representationVectorFunctional π (Sᗮ.starProjection Ω))
  have hg : g ∈ realStateSpace A := normalized_vector_mem_realStateSpace π h0
  have hk : k ∈ realStateSpace A := normalized_vector_mem_realStateSpace π h1
  have hsum : t • g+s • k=StrongDual.toWeakDual (representationVectorFunctional π Ω) := by
    apply DFunLike.ext
    intro b
    change t*(t⁻¹*representationVectorFunctional π (S.starProjection Ω) b)+
      s*(s⁻¹*representationVectorFunctional π (Sᗮ.starProjection Ω) b)=
        representationVectorFunctional π Ω b
    rw [← mul_assoc t, mul_inv_cancel₀ ht.ne',one_mul,
      ← mul_assoc s,mul_inv_cancel₀ hs.ne',one_mul]
    exact (DFunLike.congr_fun (hS.vectorFunctional_decomposition Ω) b).symm
  have hgf : g=StrongDual.toWeakDual (representationVectorFunctional π Ω) :=
    hf.2 hg hk ⟨t,s,ht,hs,hts,hsum⟩
  have hnorm : ∀ x : H,‖S.starProjection x‖^2=t*‖x‖^2 := by
    apply isClosed_property hd (isClosed_eq (by fun_prop) (by fun_prop))
    intro a
    have he := DFunLike.congr_fun hgf
      ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩
    change t⁻¹*representationVectorFunctional π (S.starProjection Ω)
      ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩=
        representationVectorFunctional π Ω ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩ at he
    rw [representationVectorFunctional_square,representationVectorFunctional_square] at he
    rw [hS.projection_commutes]
    have hem := congrArg (fun r : ℝ => t*r) he
    rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] at hem
    exact hem
  have he := hnorm (S.starProjection Ω)
  rw [S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem Ω)] at he
  change t=t*t at he
  nlinarith

theorem extreme_real_state_gns_irreducible
    (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ (realStateSpace A).extremePoints ℝ) :
    RepresentationIrreducible (realStateComplexification f hf.1).gnsStarAlgHom := by
  let Φ := realStateComplexification f hf.1
  apply irreducible_of_extreme_cyclic_vector_state Φ.gnsStarAlgHom (gnsCyclicVector Φ)
  · exact norm_gnsCyclicVector Φ (realStateComplexification_one f hf.1)
  · exact gnsAction_cyclic_dense Φ
  · rwa [gns_vectorFunctional_eq]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CyclicOrbit
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

universe u v

open scoped ComplexOrder InnerProductSpace Topology

section NonUnital

variable {A : Type u} {H : Type v} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma irreducible_restrict_unitization
    (π : Unitization ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : RepresentationIrreducible π) :
    NonUnitalRepresentationIrreducible
      (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)) := by
  intro S hSc hS
  apply hπ S hSc
  intro u x hx
  rw [← Unitization.inl_fst_add_inr_snd_eq u,map_add, ← Unitization.algebraMap_eq_inl]
  have hc : π (algebraMap ℂ (Unitization ℂ A) u.fst) =
      algebraMap ℂ (H →L[ℂ] H) u.fst := AlgHomClass.commutes π _
  rw [hc]
  change u.fst • x+π (Unitization.inr u.snd) x ∈ S
  exact S.add_mem (S.smul_mem _ hx) (hS _ _ hx)

end NonUnital

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_InnerSubalgebras
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

open scoped Topology

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma hereditarySubalgebra_le_of_mem {D : NonUnitalStarSubalgebra ℂ A}
    (hD : IsClosedInner D) {h : A} (hh : IsSelfAdjoint h) (hm : h ∈ D) :
    hereditarySubalgebra h hh ≤ D := by
  intro a ha
  apply closure_minimal _ hD.1 ha
  rintro _ ⟨x,rfl⟩
  exact hD.2 h hm h hm x

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalFamily
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

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma mul_zero_of_mem_hereditary_left {a b x : A} (ha : IsSelfAdjoint a)
    (hab : a*b=0) (hx : x ∈ hereditarySubalgebra a ha) : x*b=0 := by
  apply closure_minimal _ (isClosed_eq (continuous_id.mul_const b) continuous_const) hx
  rintro _ ⟨c,rfl⟩
  change a*c*a*b=0
  rw [mul_assoc,hab,mul_zero]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralWindows
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

open scoped CStarAlgebra Topology

lemma spectralTent_continuous (t r : ℝ) : Continuous (spectralTent t r) := by
  unfold spectralTent; fun_prop

lemma spectralTent_nonneg (t r x : ℝ) : 0 ≤ spectralTent t r x := le_max_right _ _

lemma spectralTent_center (t r : ℝ) : spectralTent t r t=1 := by
  simp [spectralTent]

lemma spectralTent_zero {t r x : ℝ} (hr : 0 < r) (hx : r ≤ |x-t|) :
    spectralTent t r x=0 := by
  apply max_eq_right
  have : 1 ≤ |x-t|/r := (le_div_iff₀ hr).mpr (by simpa using hx)
  linarith

lemma spectralPlateau_continuous (t r : ℝ) : Continuous (spectralPlateau t r) := by
  unfold spectralPlateau; fun_prop

lemma spectralPlateau_one {t r x : ℝ} (hr : 0 < r) (hx : |x-t| ≤ r) :
    spectralPlateau t r x=1 := by
  apply min_eq_left
  have : |x-t|/r ≤ 1 := (div_le_iff₀ hr).mpr (by simpa using hx)
  exact (by linarith : 1 ≤ 2-|x-t|/r).trans (le_max_right _ _)

lemma spectralPlateau_zero {t r x : ℝ} (hr : 0 < r) (hx : 2*r ≤ |x-t|) :
    spectralPlateau t r x=0 := by
  unfold spectralPlateau
  have : 2 ≤ |x-t|/r := (le_div_iff₀ hr).mpr (by linarith)
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma continuouslySupported_cfc (U : A) (f : C(ℝ,ℝ)) (S : Set ℝ)
    (hf : ∀ x,f x ≠ 0 → x ∈ S) : ContinuouslySupported U (cfc f U) S := by
  intro g hg
  constructor
  · rw [← cfc_mul f g U f.continuous.continuousOn g.continuous.continuousOn]
    calc
      cfc (fun x => f x*g x) U=cfc (0 : ℝ → ℝ) U := by
        apply cfc_congr
        intro x _
        change f x*g x=0
        by_cases hx : f x=0
        · rw [hx,zero_mul]
        · rw [hg x (hf x hx),mul_zero]
      _ = 0 := cfc_zero ℝ U
  · rw [← cfc_mul g f U g.continuous.continuousOn f.continuous.continuousOn]
    calc
      cfc (fun x => g x*f x) U=cfc (0 : ℝ → ℝ) U := by
        apply cfc_congr
        intro x _
        change g x*f x=0
        by_cases hx : f x=0
        · rw [hx,mul_zero]
        · rw [hg x (hf x hx),zero_mul]
      _ = 0 := cfc_zero ℝ U

lemma continuouslySupported_hereditary (U u : A) (hu : IsSelfAdjoint u) (S : Set ℝ)
    (hs : ContinuouslySupported U u S) {v : A} (hv : v ∈ hereditarySubalgebra u hu) :
    ContinuouslySupported U v S := by
  intro g hg
  constructor
  · exact mul_zero_of_mem_hereditary_left hu (hs g hg).1 hv
  · have hright := mul_zero_of_mem_hereditary_left hu (hs g hg).1
      (star_mem (s := hereditarySubalgebra u hu) hv)
    have he := congrArg star hright
    simpa only [star_mul,star_star,(cfc_predicate g U).star_eq,star_zero] using he

lemma cfc_nonzero_of_spectral_value (π : A →⋆ₐ[ℂ] B) {U : A} (hU : IsSelfAdjoint U)
    (f : C(ℝ,ℝ)) {t : ℝ} (ht : t ∈ spectrum ℝ (π U)) (hf : f t ≠ 0) :
    π (cfc f U) ≠ 0 := by
  rw [π.map_cfc f U f.continuous.continuousOn (by fun_prop) hU (hU.map π)]
  intro hz
  have he := norm_apply_le_norm_cfc f (π U) ht f.continuous.continuousOn (hU.map π)
  rw [hz,norm_zero] at he
  exact (not_le_of_gt (norm_pos_iff.mpr hf)) he

lemma cfc_mem_of_zero (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    {U : A} (hU : U ∈ D) (f : C(ℝ,ℝ)) (hf : f 0=0) : cfc f U ∈ D := by
  rw [← cfcₙ_eq_cfc (f := (f : ℝ → ℝ)) (a := U) f.continuous.continuousOn hf]
  exact cfcₙ_mem f hU

lemma exists_nonzero_spectral_value {U : B} (hU : IsSelfAdjoint U) (hn : U ≠ 0) :
    ∃ t ∈ spectrum ℝ U,t ≠ 0 := by
  by_contra! h
  apply hn
  calc
    U=cfc (fun x : ℝ => x) U := (cfc_id' ℝ U hU).symm
    _ = cfc (0 : ℝ → ℝ) U := cfc_congr (fun x hx => h x hx)
    _ = 0 := cfc_zero ℝ U

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalSpectralTools2
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
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma map_mem_hereditary (φ : A →⋆ₙₐ[ℂ] B) {h x : A} (hh : IsSelfAdjoint h)
    (hx : x ∈ hereditarySubalgebra h hh) :
    φ x ∈ hereditarySubalgebra (φ h) (hh.map φ) := by
  apply closure_minimal _ ((NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
    (map_continuous φ)) hx
  rintro _ ⟨b,rfl⟩
  change φ (h*b*h) ∈ hereditarySubalgebra (φ h) (hh.map φ)
  rw [map_mul,map_mul]
  exact sandwich_mem (φ h) (φ b) (hh.map φ)

lemma continuouslySupported_hereditary_nonunital (U u : A) (hu : IsSelfAdjoint u) (S : Set ℝ)
    (hs : ContinuouslySupported (U : Unitization ℂ A) (u : Unitization ℂ A) S)
    {v : A} (hv : v ∈ hereditarySubalgebra u hu) :
    ContinuouslySupported (U : Unitization ℂ A) (v : Unitization ℂ A) S :=
  continuouslySupported_hereditary (U : Unitization ℂ A) (u : Unitization ℂ A)
    (hu.map (Unitization.inrNonUnitalStarAlgHom ℂ A)) S hs
    (map_mem_hereditary (Unitization.inrNonUnitalStarAlgHom ℂ A) hu hv)

lemma unitizationSubalgebra_closed (D : NonUnitalStarSubalgebra ℂ A)
    (hD : IsClosed (D : Set A)) : IsClosed (unitizationSubalgebra D : Set (Unitization ℂ A)) :=
  hD.preimage Unitization.continuous_snd

lemma unitizationSubalgebra_inr_mem (D : NonUnitalStarSubalgebra ℂ A) {a : A} (ha : a ∈ D) :
    (a : Unitization ℂ A) ∈ unitizationSubalgebra D := ha

omit [NonUnitalCStarAlgebra A] in
lemma unitization_inr_snd_of_fst_eq_zero {z : Unitization ℂ A} (hz : z.fst=0) :
    (z.snd : Unitization ℂ A)=z := by
  ext <;> simp [hz]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_HereditaryDeletion
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
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped BigOperators Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem exists_hereditary_continuous_deletion
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A))
    (U V : A) (hUD : U ∈ D) (hVD : V ∈ D)
    (hU : IsSelfAdjoint U) (hV : IsSelfAdjoint V) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ H ∈ D,IsSelfAdjoint H ∧ ∃ n : ℕ,∃ e : Fin n → Unitization ℂ A,
      (∀ i,IsSelfAdjoint (e i)) ∧ (∑ i,e i=1) ∧
      (∀ i,e i*(H : Unitization ℂ A)*e i=0) ∧
      ∀ (p q : A) (S T : Set ℝ),
        ContinuouslySupported (U : Unitization ℂ A) (p : Unitization ℂ A) S →
        ContinuouslySupported (U : Unitization ℂ A) (q : Unitization ℂ A) T →
        (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) → p*H*q=p*V*q := by
  classical
  let u : Unitization ℂ A := U
  let v : Unitization ℂ A := V
  let E := unitizationSubalgebra D
  let : IsClosed (E : Set (Unitization ℂ A)) := unitizationSubalgebra_closed D hD
  have hu : IsSelfAdjoint u := hU.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hv : IsSelfAdjoint v := hV.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let δ : ℝ := ρ/8
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  obtain ⟨n,c,f,hf,hfs,_⟩ := exists_small_partition (spectrum ℝ u)
    (ContinuousFunctionalCalculus.isCompact_spectrum u) hδ
  let e : Fin n → Unitization ℂ A := fun i => cfc (f i) u
  let R : Fin n → Fin n → Prop := fun j k => 4*δ < dist (c j) (c k)
  let H := finiteDeletion e v R
  have heD : ∀ i,e i ∈ E := fun i => cfc_mem (f i) (unitizationSubalgebra_inr_mem D hUD)
  have hHD : H ∈ E := by
    apply E.sum_mem
    intro j _
    apply E.sum_mem
    intro k _
    split_ifs
    · exact E.mul_mem (E.mul_mem (heD j) hVD) (heD k)
    · exact E.zero_mem
  have hH0 : H.fst=0 := by
    change (Unitization.fstHom ℂ A) H=0
    simp only [H,finiteDeletion,map_sum,apply_ite,map_mul,map_zero]
    simp [v]
  have hHe : (H.snd : Unitization ℂ A)=H := unitization_inr_snd_of_fst_eq_zero hH0
  have hesa : ∀ i,IsSelfAdjoint (e i) := fun i => cfc_predicate (f i) u
  have hHsa : IsSelfAdjoint H := finiteDeletion_selfAdjoint e v R hesa hv (fun j k => by
    dsimp [R]; rw [dist_comm])
  have hdiag : ∀ i,e i*H*e i=0 := by
    apply finiteDeletion_diagonals e v R e
    intro l j k hjk
    dsimp only [R] at hjk
    by_cases hlj : 2*δ ≤ dist (c l) (c j)
    · exact Or.inl (cfc_mul_eq_zero_of_small_supports u (f l) (f j)
        (c l) (c j) δ (hf l) (hf j) hlj)
    · right
      apply cfc_mul_eq_zero_of_small_supports u (f k) (f l)
        (c k) (c l) δ (hf k) (hf l)
      have ht := dist_triangle (c j) (c l) (c k)
      rw [dist_comm (c j) (c l),dist_comm (c l) (c k)] at ht
      have hh := lt_of_not_ge hlj
      linarith
  refine ⟨H.snd,hHD,?_,n,e,hesa,cfc_partition_sum u hu f hfs,?_,?_⟩
  · have := congrArg (fun z : Unitization ℂ A => z.snd) hHsa.star_eq
    exact this
  · simpa only [hHe] using hdiag
  · intro p q S T hp hq hsep
    apply Unitization.inr_injective (R := ℂ)
    simp only [Unitization.inr_mul]
    rw [hHe]
    apply finiteDeletion_preserves_corner e v _ _ R (cfc_partition_sum u hu f hfs)
    intro j k hjk
    have hs : ∀ x ∈ S,∀ y ∈ T,8*δ ≤ dist x y := by
      have heq : 8*δ=ρ := by dsimp [δ] <;> ring
      simpa only [heq] using hsep
    rcases vanishes_on_separated_sets (f j) (f k) (c j) (c k) δ
      (hf j) (hf k) S T hs hjk with hj | hk
    · exact Or.inl (hp (f j) hj).1
    · exact Or.inr (hq (f k) hk).2

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalConnection2
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

open scoped CStarAlgebra Topology InnerProductSpace

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma starLift_inr_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    (Unitization.starLift π) (a : Unitization ℂ A)=π a :=
  congrArg (fun f : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) => f a) (Equiv.symm_apply_apply Unitization.starLift π)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_StatePullback
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

open scoped ComplexOrder InnerProductSpace Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma realStatePullback_mem (π : A →⋆ₐ[ℂ] B) {f : WeakDual ℝ (selfAdjoint B)}
    (hf : f ∈ realStateSpace B) : realStatePullback π f ∈ realStateSpace A := by
  constructor
  · apply ((WeakDual.toStrongDual f).comp (selfAdjointMap π)).opNorm_le_bound zero_le_one
    intro b
    change ‖f (selfAdjointMap π b)‖ ≤ 1*‖b‖
    calc
      _ ≤ ‖WeakDual.toStrongDual f‖*‖selfAdjointMap π b‖ :=
        (WeakDual.toStrongDual f).le_opNorm _
      _ ≤ 1*‖selfAdjointMap π b‖ := mul_le_mul_of_nonneg_right hf.1 (norm_nonneg _)
      _ ≤ 1*‖b‖ := by
        gcongr
        exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom (b : A)
  · change f (selfAdjointMap π 1)=1
    have h1 : selfAdjointMap π 1=1 := Subtype.ext (map_one π)
    rw [h1]
    exact hf.2

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma realStatePullback_annihilator (π : A →⋆ₐ[ℂ] B) {f : WeakDual ℝ (selfAdjoint B)}
    (hf : f ∈ realStateSpace B) (S : Set A) (hS : ∀ x ∈ S,π x=0) :
    realStatePullback π f ∈ annihilatorStates S := by
  refine ⟨realStatePullback_mem π hf,?_⟩
  intro x hx a
  change f (selfAdjointMap π ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩)=0
  have hz : selfAdjointMap π ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0 := by
    apply Subtype.ext
    change π (star (x*a)*(x*a))=0
    simp [map_mul,map_star,hS x hx]
  rw [hz,map_zero]

lemma exists_annihilator_norming_pullback [Nontrivial B] (π : A →⋆ₐ[ℂ] B)
    (S : Set A) (hS : ∀ x ∈ S,π x=0) (b : A) (hb : 0 ≤ b) :
    ∃ f ∈ annihilatorStates S,f ⟨b,hb.isSelfAdjoint⟩=‖π b‖ := by
  obtain ⟨g,hg,hgb⟩ := exists_norming_real_state (π b) (map_nonneg π hb)
  refine ⟨realStatePullback π g,realStatePullback_annihilator π hg S hS,?_⟩
  exact hgb

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PrimitiveCompactness
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

open scoped ComplexOrder InnerProductSpace Topology

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_state_annihilating_family {ι : Type w} (x : ι → A) (b : selfAdjoint A) (α : ℝ)
    (h : ∀ F : Finset ι,∃ f ∈ realStateSpace A,α ≤ f b ∧
      ∀ i ∈ F,∀ a : A,f ⟨star (x i*a)*(x i*a),(star_mul_self_nonneg (x i*a)).isSelfAdjoint⟩=0) :
    ∃ f ∈ annihilatorStates (Set.range x), α ≤ f b := by
  let C := {f ∈ realStateSpace A | α ≤ f b}
  let T : ι → Set (WeakDual ℝ (selfAdjoint A)) := fun i =>
    {f | ∀ a : A,f ⟨star (x i*a)*(x i*a),(star_mul_self_nonneg (x i*a)).isSelfAdjoint⟩=0}
  have hC : IsCompact C := (realStateSpace_isCompact A).inter_right
    (isClosed_le continuous_const (WeakDual.eval_continuous b))
  have hT : ∀ i,IsClosed (T i) := by
    intro i
    simp only [T,Set.ofPred_forall]
    exact isClosed_iInter (fun a => isClosed_eq (WeakDual.eval_continuous _) continuous_const)
  obtain ⟨f,hfC,hfT⟩ := hC.inter_iInter_nonempty T hT (by
    intro F
    obtain ⟨g,hg,hgb,hgT⟩ := h F
    refine ⟨g,⟨hg,hgb⟩,?_⟩
    simpa only [Set.mem_iInter,T,Set.mem_ofPred_eq] using hgT)
  refine ⟨f,⟨hfC.1,?_⟩,hfC.2⟩
  rintro _ ⟨i,rfl⟩ a
  exact (Set.mem_iInter.mp hfT i) a

theorem finite_norm_support_cover {ι : Type w} (x : ι → A) (b : A) (hb : 0 ≤ b)
    (α : ℝ) (hα : 0 < α)
    (hcover : ∀ (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ (realStateSpace A).extremePoints ℝ),
      α ≤ ‖(realStateComplexification f hf.1).gnsStarAlgHom b‖ →
        ∃ i, (realStateComplexification f hf.1).gnsStarAlgHom (x i) ≠ 0) :
    ∃ F : Finset ι,∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),α ≤ ‖π b‖ → ∃ i ∈ F,π (x i) ≠ 0 := by
  classical
  by_contra! hn
  have hfinite : ∀ F : Finset ι,∃ f ∈ realStateSpace A,α ≤ f ⟨b,hb.isSelfAdjoint⟩ ∧
      ∀ i ∈ F,∀ a : A,f ⟨star (x i*a)*(x i*a),(star_mul_self_nonneg (x i*a)).isSelfAdjoint⟩=0 := by
    intro F
    obtain ⟨H,hH,hI,hC,π,hπ,hF⟩ := hn F
    have hbn : π b ≠ 0 := by
      intro hz
      rw [hz,norm_zero] at hπ
      exact (not_le_of_gt hα) hπ
    let : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne (π b) 0 hbn
    obtain ⟨f,hf,hfb⟩ := exists_annihilator_norming_pullback π (x '' (F : Set ι))
      (by rintro _ ⟨i,hi,rfl⟩; exact hF i hi) b hb
    refine ⟨f,hf.1,by rwa [hfb],?_⟩
    intro i hi a
    exact hf.2 (x i) ⟨i,hi,rfl⟩ a
  obtain ⟨g,hg,hgb⟩ := exists_state_annihilating_family x ⟨b,hb.isSelfAdjoint⟩ α hfinite
  obtain ⟨f,hf,hfS,hfb⟩ := exists_extreme_annihilator_state hg ⟨b,hb.isSelfAdjoint⟩
  let Φ := realStateComplexification f hf.1
  have he : f ⟨b,hb.isSelfAdjoint⟩ ≤ ‖Φ.gnsStarAlgHom b‖ := by
    let Ω := gnsCyclicVector Φ
    have hΩ : ‖Ω‖=1 := norm_gnsCyclicVector Φ (realStateComplexification_one f hf.1)
    have hv := DFunLike.congr_fun (gns_vectorFunctional_eq f hf.1) ⟨b,hb.isSelfAdjoint⟩
    change (inner ℂ Ω (Φ.gnsStarAlgHom b Ω)).re=f ⟨b,hb.isSelfAdjoint⟩ at hv
    calc
      _ = (inner ℂ Ω (Φ.gnsStarAlgHom b Ω)).re := hv.symm
      _ ≤ ‖inner ℂ Ω (Φ.gnsStarAlgHom b Ω)‖ := Complex.re_le_norm _
      _ ≤ ‖Ω‖*‖Φ.gnsStarAlgHom b Ω‖ := norm_inner_le_norm _ _
      _ ≤ ‖Ω‖*(‖Φ.gnsStarAlgHom b‖*‖Ω‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖Φ.gnsStarAlgHom b‖ := by rw [hΩ,one_mul,mul_one]
  obtain ⟨i,hi⟩ := hcover f hf (hgb.trans (hfb.trans he))
  exact hi (annihilatorStates_gns_zero hfS ⟨i,rfl⟩)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteSelection
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

open scoped CStarAlgebra Topology

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finite_norm_support_cover_nonunital {ι : Type w} (x : ι → A) (b : A) (hb : 0 ≤ b)
    (α : ℝ) (hα : 0 < α)
    (hcover : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),NonUnitalRepresentationIrreducible π →
        α ≤ ‖π b‖ → ∃ i,π (x i) ≠ 0) :
    ∃ F : Finset ι,∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),α ≤ ‖π b‖ → ∃ i ∈ F,π (x i) ≠ 0 := by
  let ιA := Unitization.inrNonUnitalStarAlgHom ℂ A
  obtain ⟨F,hF⟩ := finite_norm_support_cover (fun i => ιA (x i)) (ιA b) (map_nonneg ιA hb) α hα (by
    intro f hf hfb
    let Φ := realStateComplexification f hf.1
    let π := Φ.gnsStarAlgHom.toNonUnitalStarAlgHom.comp ιA
    exact hcover Φ.GNS π
      (irreducible_restrict_unitization Φ.gnsStarAlgHom (extreme_real_state_gns_irreducible f hf)) hfb)
  refine ⟨F,?_⟩
  intro H _ _ _ π hπ
  have hb' : α ≤ ‖(Unitization.starLift π) (ιA b)‖ := by
    change α ≤ ‖(Unitization.starLift π) (b : Unitization ℂ A)‖
    rwa [starLift_inr_apply]
  obtain ⟨i,hi,hin⟩ := hF H (Unitization.starLift π) hb'
  refine ⟨i,hi,?_⟩
  change (Unitization.starLift π) (x i : Unitization ℂ A) ≠ 0 at hin
  rwa [starLift_inr_apply] at hin

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SelectedCoupling
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

theorem exists_selected_finite_coupling_of_gap_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    (b : A) (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α) (Q : A → A → Prop)
    (hloc : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → α ≤ ‖π b‖ →
      ∃ F : OrthogonalPerturbationData A n,F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q ∧
        π (positiveCut F.α F.c) ≠ 0) :
    ∃ (F : Finset {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q})
      (U : A),U ∈ D ∧ IsSelfAdjoint U ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π b‖ → ∃ i ∈ F,π (i.val.p*U*i.val.q) ≠ 0 := by
  let I := {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q}
  obtain ⟨F,hF⟩ := finite_norm_support_cover_nonunital
    (fun i : I => positiveCut i.val.α i.val.c) b hb α hα (by
      intro H _ _ _ π hπ hπb
      let H' : ComplexHilbert.{u} := ⟨H⟩
      obtain ⟨i,hiD,hjD,hQ,hin⟩ := hloc H' π hπ hπb
      exact ⟨⟨i,hiD,hjD,hQ⟩,hin⟩)
  obtain ⟨U,hUD,hUsa,ε,hε,hU⟩ := exists_finite_coupling_of_gap_any hσ hσγ hgap hA hn hpi
    D hD (fun i : I => i.val) F (fun i _ => ⟨i.property.1,i.property.2.1⟩)
  refine ⟨F,U,hUD,hUsa,?_⟩
  intro H π hπb
  obtain ⟨i,hi,hin⟩ := hF H π hπb
  have hci := norm_lt_of_positiveCut_image_ne_zero π i.val.nonneg_c i.val.pos_α.le hin
  refine ⟨i,hi,?_⟩
  intro hz
  have he := hU i hi H π hci.le
  rw [hz,norm_zero] at he
  exact (not_le_of_gt hε) he

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SquareZero
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

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma image_hereditary_corner_zero (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    {a b p q x : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hp : p ∈ hereditarySubalgebra a ha) (hq : q ∈ hereditarySubalgebra b hb)
    (hz : π (a*x*b)=0) : π (p*x*q)=0 := by
  have hc : IsClosed {p : A | π (p*x*q)=0} := isClosed_eq (by fun_prop) continuous_const
  apply closure_minimal _ hc hp
  rintro _ ⟨c,rfl⟩
  have hc' : IsClosed {q : A | π ((a*c*a)*x*q)=0} := isClosed_eq (by fun_prop) continuous_const
  apply closure_minimal _ hc' hq
  rintro _ ⟨d,rfl⟩
  change π ((a*c*a)*x*(b*d*b))=0
  have he : (a*c*a)*x*(b*d*b)=(a*c)*(a*x*b)*(d*b) := by noncomm_ring
  rw [he,map_mul,map_mul,hz,mul_zero,zero_mul]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FirstCoupling
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

open scoped CStarAlgebra Topology

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_first_coupling_on_norm_slice_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ U ∈ D,IsSelfAdjoint U ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ →
        ∃ p ∈ D,∃ q ∈ D,0 ≤ p ∧ 0 ≤ q ∧ p*q=0 ∧ π (p*U*q) ≠ 0 := by
  obtain ⟨F,U,hUD,hU,hUF⟩ := exists_selected_finite_coupling_of_gap_any hσ hσγ hgap hA hn hpi
    D hD b hb hα (fun _ _ => True) (by
      intro H π hπ hπb
      obtain ⟨c,hcD,hc,hcn⟩ := hlocal H π hπ hπb
      obtain ⟨u,huD,v,hvD,hu,hv,huv,hun,hvn⟩ := exists_orthogonal_detected_pair hn hpi π hc hcn
      obtain ⟨F,hFu,hFv,hFn⟩ := exists_core_perturbationData hn hpi hπ hu hv huv hun hvn
      have huD' : u ∈ D := hereditarySubalgebra_le_of_mem hD hc.isSelfAdjoint hcD huD
      have hvD' : v ∈ D := hereditarySubalgebra_le_of_mem hD hc.isSelfAdjoint hcD hvD
      exact ⟨F,hereditarySubalgebra_le_of_mem hD hu.isSelfAdjoint huD' hFu,
        hereditarySubalgebra_le_of_mem hD hv.isSelfAdjoint hvD' hFv,True.intro,hFn⟩)
  refine ⟨U,hUD,hU,?_⟩
  intro H π hπb
  obtain ⟨i,_,hin⟩ := hUF H π hπb
  exact ⟨i.val.p,i.property.1,i.val.q,i.property.2.1,i.val.nonneg_p,i.val.nonneg_q,
    i.val.orthogonal,hin⟩

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparatedSpectralWindows
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

open scoped CStarAlgebra Topology

lemma tent_support_subset (t r : ℝ) (hr : 0 < r) :
    ∀ x,spectralTent t r x ≠ 0 → x ∈ Metric.closedBall t r := by
  intro x hx
  have he : |x-t| < r := lt_of_not_ge (fun h => hx (spectralTent_zero hr h))
  simpa only [Metric.mem_closedBall,Real.dist_eq] using he.le

lemma separated_closedBalls (s t r : ℝ) :
    ∀ x ∈ Metric.closedBall s r,∀ y ∈ Metric.closedBall t r,
      dist s t-2*r ≤ dist x y := by
  intro x hx y hy
  have hx' : dist x s ≤ r := hx
  have hy' : dist y t ≤ r := hy
  have ht1 := dist_triangle s x t
  have ht2 := dist_triangle x y t
  rw [dist_comm s x] at ht1
  linarith

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

lemma exists_windows_of_two_nonzero_spectral_values
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₐ[ℂ] B) {U : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    {s t : ℝ} (hs : s ∈ spectrum ℝ (π U)) (ht : t ∈ spectrum ℝ (π U))
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hst : s ≠ t) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧ ContinuouslySupported U u S ∧
        ContinuouslySupported U v T ∧ (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  let r := min (min |s| |t|) (dist s t)/4
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (lt_min (lt_min (abs_pos.mpr hs0) (abs_pos.mpr ht0)) (dist_pos.mpr hst)) (by norm_num)
  have hrs : r ≤ |s| := by
    have := (min_le_left (min |s| |t|) (dist s t)).trans (min_le_left |s| |t|)
    dsimp [r] <;> linarith [abs_nonneg s]
  have hrt : r ≤ |t| := by
    have := (min_le_left (min |s| |t|) (dist s t)).trans (min_le_right |s| |t|)
    dsimp [r] <;> linarith [abs_nonneg t]
  have hrst : 2*r < dist s t := by
    have := min_le_right (min |s| |t|) (dist s t)
    dsimp [r] at hr ⊢ <;> linarith
  let f : C(ℝ,ℝ) := ⟨spectralTent s r,spectralTent_continuous s r⟩
  let g : C(ℝ,ℝ) := ⟨spectralTent t r,spectralTent_continuous t r⟩
  have hf0 : f 0=0 := spectralTent_zero hr (by simpa using hrs)
  have hg0 : g 0=0 := spectralTent_zero hr (by simpa using hrt)
  have hfg : cfc f U*cfc g U=0 := by
    rw [← cfc_mul f g U f.continuous.continuousOn g.continuous.continuousOn]
    calc
      cfc (fun x => f x*g x) U=cfc (0 : ℝ → ℝ) U := by
        apply cfc_congr
        intro x _
        change f x*g x=0
        by_cases hfx : f x=0
        · rw [hfx,zero_mul]
        by_cases hgx : g x=0
        · rw [hgx,mul_zero]
        have hx := separated_closedBalls s t r x (tent_support_subset s r hr x hfx)
          x (tent_support_subset t r hr x hgx)
        rw [dist_self] at hx
        exfalso; linarith
      _ = 0 := cfc_zero ℝ U
  refine ⟨cfc f U,cfc_mem_of_zero D hUD f hf0,cfc g U,cfc_mem_of_zero D hUD g hg0,
    cfc_nonneg (fun x _ => spectralTent_nonneg s r x),
    cfc_nonneg (fun x _ => spectralTent_nonneg t r x),hfg,
    cfc_nonzero_of_spectral_value π hU f hs ?_,
    cfc_nonzero_of_spectral_value π hU g ht ?_,Metric.closedBall s r,Metric.closedBall t r,
    dist s t-2*r,sub_pos.mpr hrst,continuouslySupported_cfc U f _ (tent_support_subset s r hr),
    continuouslySupported_cfc U g _ (tent_support_subset t r hr),separated_closedBalls s t r⟩
  · change spectralTent s r s ≠ 0
    rw [spectralTent_center]; exact one_ne_zero
  · change spectralTent t r t ≠ 0
    rw [spectralTent_center]; exact one_ne_zero

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralResidual
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
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma residual_eq_unital (e h : A) : residual e h=(1-e)*h*(1-e) := by
  unfold residual
  noncomm_ring

lemma exists_windows_of_single_nonzero_spectral_value
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₐ[ℂ] B) {U p q : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    (hp : IsSelfAdjoint p) (hpD : p ∈ D) (hpq : p*q=0) (hc : π (p*U*q) ≠ 0)
    {t : ℝ} (ht : t ∈ spectrum ℝ (π U)) (ht0 : t ≠ 0)
    (honly : ∀ s ∈ spectrum ℝ (π U),s=0 ∨ s=t) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧ ContinuouslySupported U u S ∧
        ContinuouslySupported U v T ∧ (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  let r := |t|/4
  have hr : 0 < r := by dsimp [r]; exact div_pos (abs_pos.mpr ht0) (by norm_num)
  let f : C(ℝ,ℝ) := ⟨spectralTent t (r/2),spectralTent_continuous t (r/2)⟩
  let E : C(ℝ,ℝ) := ⟨spectralPlateau t r,spectralPlateau_continuous t r⟩
  have hf0 : f 0=0 := spectralTent_zero (by positivity) (by dsimp [r] <;> simp <;> linarith [abs_nonneg t])
  have hE0 : E 0=0 := spectralPlateau_zero hr (by dsimp [r] <;> simp <;> linarith [abs_nonneg t])
  have hEt : E t=1 := spectralPlateau_one hr (by simp; exact hr.le)
  let e := cfc E U
  have heSA : IsSelfAdjoint e := cfc_predicate E U
  let u := cfc f U
  let v := residual e (p*p)
  have heD : e ∈ D := cfc_mem_of_zero D hUD E hE0
  have hp2 : p*p ∈ D := D.mul_mem hpD hpD
  have hvD : v ∈ D := D.add_mem (D.sub_mem (D.sub_mem hp2 (D.mul_mem heD hp2))
    (D.mul_mem hp2 heD)) (D.mul_mem (D.mul_mem heD hp2) heD)
  have hUe : π U=t • π e := by
    dsimp only [e]
    rw [π.map_cfc E U E.continuous.continuousOn (by fun_prop) hU (hU.map π),
      ← cfc_const_mul t E (π U) E.continuous.continuousOn]
    calc
      π U=cfc (fun s : ℝ => s) (π U) := (cfc_id' ℝ _ (hU.map π)).symm
      _ = cfc (fun s => t*E s) (π U) := by
        apply cfc_congr
        intro s hs
        change s=t*E s
        rcases honly s hs with rfl | rfl
        · rw [hE0,mul_zero]
        · rw [hEt,mul_one]
  have hvn : π v ≠ 0 := by
    intro hz
    have he : π ((1-e)*p)=0 := by
      apply (CStarRing.mul_star_self_eq_zero_iff _).mp
      have hv : ((1-e)*p)*star ((1-e)*p)=v := by
        dsimp only [v]
        rw [residual_eq_unital]
        simp only [star_mul,hp.star_eq,star_sub,star_one,heSA.star_eq]
        noncomm_ring
      rw [← map_star,← map_mul,hv,hz]
    have hep : π e*π p=π p := by
      rw [map_mul,map_sub,map_one,sub_mul,one_mul] at he
      exact (sub_eq_zero.mp he).symm
    have hpe : π p*π e=π p := by
      have hh := congrArg star hep
      simpa only [star_mul,← map_star,hp.star_eq,heSA.star_eq] using hh
    apply hc
    rw [map_mul,map_mul,hUe,mul_smul_comm,smul_mul_assoc,hpe,← map_mul,hpq,map_zero,smul_zero]
  have hfE : u*(1-e)=0 ∧ (1-e)*u=0 := by
    have hf : ContinuouslySupported U u (Metric.closedBall t (r/2)) :=
      continuouslySupported_cfc U f _ (tent_support_subset t (r/2) (by positivity))
    let g : C(ℝ,ℝ) := 1-E
    have hgf : ∀ x ∈ Metric.closedBall t (r/2),g x=0 := by
      intro x hx
      change 1-spectralPlateau t r x=0
      rw [spectralPlateau_one hr (by
        have hx' : |x-t| ≤ r/2 := by simpa only [Metric.mem_closedBall,Real.dist_eq] using hx
        linarith),sub_self]
    have hh := hf g hgf
    have hg : cfc g U=1-e := by
      change cfc (fun x => 1-E x) U=1-e
      rw [cfc_sub (fun _ : ℝ => 1) E U continuousOn_const E.continuous.continuousOn,
        cfc_const_one ℝ U hU]
    rwa [hg] at hh
  have huv : u*v=0 := by
    dsimp only [v]
    rw [residual_eq_unital,← mul_assoc,← mul_assoc,hfE.1,zero_mul,zero_mul]
  have hvS : ContinuouslySupported U v {s : ℝ | r ≤ dist s t} := by
    intro g hg
    have hEg : (1-e)*cfc g U=0 ∧ cfc g U*(1-e)=0 := by
      have hzero : (fun s : ℝ => (1-E s)*g s)=(0 : ℝ → ℝ) := by
        funext s
        change (1-E s)*g s=0
        by_cases hs : r ≤ dist s t
        · rw [hg s hs,mul_zero]
        · have hs' : |s-t| ≤ r := by simpa only [Real.dist_eq] using (le_of_lt (lt_of_not_ge hs))
          change (1-spectralPlateau t r s)*g s=0
          rw [spectralPlateau_one hr hs',sub_self,zero_mul]
      have hmap : cfc (fun s : ℝ => 1-E s) U=1-e := by
        rw [cfc_sub (fun _ : ℝ => 1) E U continuousOn_const E.continuous.continuousOn,
          cfc_const_one ℝ U hU]
      constructor
      · rw [← hmap,← cfc_mul (fun s : ℝ => 1-E s) g U
          (by fun_prop) g.continuous.continuousOn,hzero,cfc_zero ℝ U]
      · rw [← hmap,← cfc_mul g (fun s : ℝ => 1-E s) U
          g.continuous.continuousOn (by fun_prop)]
        have heq : (fun s : ℝ => g s*(1-E s))=(0 : ℝ → ℝ) := by
          simpa only [mul_comm] using hzero
        rw [heq,cfc_zero ℝ U]
    constructor
    · dsimp only [v]
      rw [residual_eq_unital,mul_assoc,hEg.1,mul_zero]
    · dsimp only [v]
      rw [residual_eq_unital,← mul_assoc,← mul_assoc,hEg.2,zero_mul,zero_mul]
  refine ⟨u,cfc_mem_of_zero D hUD f hf0,v,hvD,
    cfc_nonneg (fun x _ => spectralTent_nonneg t (r/2) x),
    residual_nonneg e (p*p) (cfc_predicate E U) (by simpa only [hp.star_eq] using star_mul_self_nonneg p),
    huv,cfc_nonzero_of_spectral_value π hU f ht ?_,hvn,
    Metric.closedBall t (r/2),{s : ℝ | r ≤ dist s t},r/2,by positivity,
    continuouslySupported_cfc U f _ (tent_support_subset t (r/2) (by positivity)),hvS,?_⟩
  · change spectralTent t (r/2) t ≠ 0
    rw [spectralTent_center]; exact one_ne_zero
  · intro x hx y hy
    have hx' : dist x t ≤ r/2 := hx
    have hy' : r ≤ dist y t := hy
    have hh := dist_triangle y x t
    rw [dist_comm y x] at hh
    linarith

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalSpectralTools
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
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

section Unital

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

lemma exists_separated_spectral_windows
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₐ[ℂ] B) {U p q : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    (hp : IsSelfAdjoint p) (hpD : p ∈ D) (hpq : p*q=0) (hc : π (p*U*q) ≠ 0) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧ ContinuouslySupported U u S ∧
        ContinuouslySupported U v T ∧ (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  have hn : π U ≠ 0 := by
    intro hz
    apply hc
    rw [map_mul,map_mul,hz,mul_zero,zero_mul]
  obtain ⟨t,ht,ht0⟩ := exists_nonzero_spectral_value (hU.map π) hn
  by_cases htwo : ∃ s ∈ spectrum ℝ (π U),s ≠ 0 ∧ s ≠ t
  · obtain ⟨s,hs,hs0,hst⟩ := htwo
    exact exists_windows_of_two_nonzero_spectral_values D π hU hUD hs ht hs0 ht0 hst
  · apply exists_windows_of_single_nonzero_spectral_value D π hU hUD hp hpD hpq hc ht ht0
    intro s hs
    by_cases hs0 : s=0
    · exact Or.inl hs0
    · exact Or.inr (by by_contra hst; exact htwo ⟨s,hs,hs0,hst⟩)

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type*} [CStarAlgebra B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma starLift_inr_apply_general (π : A →⋆ₙₐ[ℂ] B) (a : A) :
    (Unitization.starLift π) (a : Unitization ℂ A)=π a :=
  congrArg (fun f : A →⋆ₙₐ[ℂ] B => f a) (Equiv.symm_apply_apply Unitization.starLift π)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitization_subalgebra_closed (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A)) :
    IsClosed ((NonUnitalStarSubalgebra.map (Unitization.inrNonUnitalStarAlgHom ℂ A) D :
      NonUnitalStarSubalgebra ℂ (Unitization ℂ A)) : Set (Unitization ℂ A)) := by
  rw [NonUnitalStarSubalgebra.coe_map]
  exact Unitization.isometry_inr.isClosedEmbedding.isClosedMap _ hD

lemma exists_nonunital_separated_spectral_windows
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A))
    (π : A →⋆ₙₐ[ℂ] B) {U p q : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    (hp : IsSelfAdjoint p) (hpD : p ∈ D) (hpq : p*q=0) (hc : π (p*U*q) ≠ 0) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧
        ContinuouslySupported (U : Unitization ℂ A) (u : Unitization ℂ A) S ∧
        ContinuouslySupported (U : Unitization ℂ A) (v : Unitization ℂ A) T ∧
        (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  let E := NonUnitalStarSubalgebra.map ι D
  let : IsClosed (E : Set (Unitization ℂ A)) := unitization_subalgebra_closed D hD
  have hEc : (Unitization.starLift π) (ι p*ι U*ι q) ≠ 0 := by
    rw [← map_mul,← map_mul]
    change (Unitization.starLift π) ((p*U*q : A) : Unitization ℂ A) ≠ 0
    rwa [starLift_inr_apply_general]
  obtain ⟨u,hu,v,hv,hu0,hv0,huv,hun,hvn,S,T,ρ,hρ,huS,hvT,hST⟩ :=
    exists_separated_spectral_windows E (Unitization.starLift π)
      (hU.map ι) (NonUnitalStarSubalgebra.mem_map.mpr ⟨U,hUD,rfl⟩)
      (hp.map ι) (NonUnitalStarSubalgebra.mem_map.mpr ⟨p,hpD,rfl⟩)
      (by rw [← map_mul,hpq,map_zero]) hEc
  obtain ⟨u₀,hu₀,rfl⟩ := NonUnitalStarSubalgebra.mem_map.mp hu
  obtain ⟨v₀,hv₀,rfl⟩ := NonUnitalStarSubalgebra.mem_map.mp hv
  refine ⟨u₀,hu₀,v₀,hv₀,Unitization.inr_nonneg_iff.mp hu0,
    Unitization.inr_nonneg_iff.mp hv0,?_,?_,?_,S,T,ρ,hρ,huS,hvT,hST⟩
  · apply Unitization.inr_injective (R := ℂ)
    change ι (u₀*v₀)=ι 0
    rw [map_mul,map_zero]
    exact huv
  · change (Unitization.starLift π) (u₀ : Unitization ℂ A) ≠ 0 at hun
    rwa [starLift_inr_apply_general] at hun
  · change (Unitization.starLift π) (v₀ : Unitization ℂ A) ≠ 0 at hvn
    rwa [starLift_inr_apply_general] at hvn

end NonUnital

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SecondCoupling
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

open scoped CStarAlgebra Topology

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_second_coupling_on_norm_slice_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ U ∈ D,∃ V ∈ D,IsSelfAdjoint U ∧ IsSelfAdjoint V ∧ ∃ ρ : ℝ,0 < ρ ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ →
        ∃ p q : A,∃ S T : Set ℝ,
          ContinuouslySupported (U : Unitization ℂ A) (p : Unitization ℂ A) S ∧
          ContinuouslySupported (U : Unitization ℂ A) (q : Unitization ℂ A) T ∧
          (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) ∧ π (p*V*q) ≠ 0 := by
  classical
  obtain ⟨U,hUD,hU,hUc⟩ := exists_first_coupling_on_norm_slice_any hσ hσγ hgap hA hn hpi D hD hb hα hlocal
  let Q : A → A → Prop := fun p q => ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧
    ContinuouslySupported (U : Unitization ℂ A) (p : Unitization ℂ A) S ∧
    ContinuouslySupported (U : Unitization ℂ A) (q : Unitization ℂ A) T ∧
    (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y)
  obtain ⟨F,V,hVD,hV,hVc⟩ := exists_selected_finite_coupling_of_gap_any hσ hσγ hgap hA hn hpi
    D hD b hb hα Q (by
      intro H π hπ hπb
      obtain ⟨p,hpD,q,_,hp,_,hpq,hpc⟩ := hUc H π hπb
      obtain ⟨u,huD,v,hvD,hu,hv,huv,hun,hvn,S,T,ρ,hρ,huS,hvT,hST⟩ :=
        exists_nonunital_separated_spectral_windows D hD.1 π hU hUD hp.isSelfAdjoint hpD hpq hpc
      obtain ⟨i,hip,hiq,hin⟩ := exists_core_perturbationData hn hpi hπ hu hv huv hun hvn
      refine ⟨i,hereditarySubalgebra_le_of_mem hD hu.isSelfAdjoint huD hip,
        hereditarySubalgebra_le_of_mem hD hv.isSelfAdjoint hvD hiq,?_,hin⟩
      exact ⟨S,T,ρ,hρ,continuouslySupported_hereditary_nonunital U u hu.isSelfAdjoint S huS hip,
        continuouslySupported_hereditary_nonunital U v hv.isSelfAdjoint T hvT hiq,hST⟩)
  let I := {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q}
  choose S T r hr hp hq hsep using fun i : I => i.property.2.2
  have hmin : ∃ ρ : ℝ,0 < ρ ∧ ∀ i ∈ F,ρ ≤ r i := by
    clear hVc
    induction F using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i F _ ih =>
      obtain ⟨ρ,hρ,hρF⟩ := ih
      refine ⟨min (r i) ρ,lt_min (hr i) hρ,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hρF j hj)
  obtain ⟨ρ,hρ,hρF⟩ := hmin
  refine ⟨U,hUD,V,hVD,hU,hV,ρ,hρ,?_⟩
  intro H π hπb
  obtain ⟨i,hi,hin⟩ := hVc H π hπb
  exact ⟨i.val.p,i.val.q,S i,T i,hp i,hq i,
    fun x hx y hy => (hρF i hi).trans (hsep i x hx y hy),hin⟩

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SquareZero4
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
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma map_posPart (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : IsSelfAdjoint a) : π a⁺=(π a)⁺ := by
  rw [CFC.posPart_def,CFC.posPart_def]
  exact π.map_cfcₙ (·⁺ : ℝ → ℝ) a (by fun_prop) (by simp) (by fun_prop) ha (ha.map π)

lemma map_negPart (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : IsSelfAdjoint a) : π a⁻=(π a)⁻ := by
  rw [CFC.negPart_def,CFC.negPart_def]
  exact π.map_cfcₙ (·⁻ : ℝ → ℝ) a (by fun_prop) (by simp) (by fun_prop) ha (ha.map π)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_DetectedSigns
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

open scoped CStarAlgebra Topology

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_detected_both_signs_on_norm_slice_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ h ∈ D,IsSelfAdjoint h ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ →
        π h⁺ ≠ 0 ∧ π h⁻ ≠ 0 := by
  obtain ⟨U,hUD,V,hVD,hU,hV,ρ,hρ,hc⟩ :=
    exists_second_coupling_on_norm_slice_any hσ hσγ hgap hA hn hpi D hD hb hα hlocal
  obtain ⟨h,hhD,hh,m,e,he,hs,hd,hcorners⟩ :=
    exists_hereditary_continuous_deletion D hD.1 U V hUD hVD hU hV hρ
  refine ⟨h,hhD,hh,?_⟩
  intro H π hπb
  obtain ⟨p,q,S,T,hp,hq,hST,hpn⟩ := hc H π hπb
  have hhn : π h ≠ 0 := by
    intro hz
    apply hpn
    rw [← hcorners p q S T hp hq hST,map_mul,map_mul,hz,mul_zero,zero_mul]
  have hhn' : (Unitization.starLift π) (h : Unitization ℂ A) ≠ 0 := by
    rwa [starLift_inr_apply]
  have hsigns := both_signs_in_image_of_partition_diagonals (Unitization.starLift π)
    (hh.map (Unitization.inrNonUnitalStarAlgHom ℂ A)) hhn' e he hs hd
  change ((Unitization.starLift π) (h : Unitization ℂ A))⁺ ≠ 0 ∧
    ((Unitization.starLift π) (h : Unitization ℂ A))⁻ ≠ 0 at hsigns
  rw [starLift_inr_apply] at hsigns
  simpa only [map_posPart π hh,map_negPart π hh] using hsigns

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniverseSquareZero
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

open scoped CStarAlgebra Topology

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_square_zero_on_norm_slice_of_gap_any_oai
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ x ∈ D,x*x=0 ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ → π x ≠ 0 := by
  obtain ⟨h,hhD,hh,hhn⟩ := exists_detected_both_signs_on_norm_slice_any hσ hσγ hgap hA hn hpi D hD hb hα hlocal
  let : IsClosed (D : Set A) := hD.1
  have hpD : h⁺ ∈ D := cfcₙ_mem (·⁺ : ℝ → ℝ) hhD
  have hqD : h⁻ ∈ D := cfcₙ_mem (·⁻ : ℝ → ℝ) hhD
  let Q : A → A → Prop := fun p q =>
    p ∈ hereditarySubalgebra h⁺ (CFC.posPart_nonneg h).isSelfAdjoint ∧
    q ∈ hereditarySubalgebra h⁻ (CFC.negPart_nonneg h).isSelfAdjoint
  obtain ⟨F,z,hzD,_,hzc⟩ := exists_selected_finite_coupling_of_gap_any hσ hσγ hgap hA hn hpi
    D hD b hb hα Q (by
      intro H π hπ hπb
      obtain ⟨hpn,hqn⟩ := hhn H π hπb
      obtain ⟨i,hip,hiq,hin⟩ := exists_core_perturbationData hn hpi hπ
        (CFC.posPart_nonneg h) (CFC.negPart_nonneg h) (CFC.posPart_mul_negPart h) hpn hqn
      exact ⟨i,hereditarySubalgebra_le_of_mem hD (CFC.posPart_nonneg h).isSelfAdjoint hpD hip,
        hereditarySubalgebra_le_of_mem hD (CFC.negPart_nonneg h).isSelfAdjoint hqD hiq,⟨hip,hiq⟩,hin⟩)
  refine ⟨h⁺*z*h⁻,hD.2 h⁺ hpD h⁻ hqD z,?_,?_⟩
  · calc
      (h⁺*z*h⁻)*(h⁺*z*h⁻)=(h⁺*z)*(h⁻*h⁺)*(z*h⁻) := by noncomm_ring
      _ = 0 := by rw [CFC.negPart_mul_posPart,mul_zero,zero_mul]
  · intro H π hπb hnz
    obtain ⟨i,_,hin⟩ := hzc H π hπb
    exact hin (image_hereditary_corner_zero π (CFC.posPart_nonneg h).isSelfAdjoint
      (CFC.negPart_nonneg h).isSelfAdjoint i.property.2.2.1 i.property.2.2.2 hnz)

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u} : type_of% @OAI.WeakPureInfiniteness.exists_square_zero_on_norm_slice_of_gap_any_oai.{u} := @OAI.WeakPureInfiniteness.exists_square_zero_on_norm_slice_of_gap_any_oai.{u}
