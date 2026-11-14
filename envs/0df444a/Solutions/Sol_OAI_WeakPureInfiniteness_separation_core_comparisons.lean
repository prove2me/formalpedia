-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.separation_core_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:17:20.792199+00:00
-- url     : https://prove2.me/submissions/f83d34fd-e726-4919-b075-07e10a3efea0

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003

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
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ColumnNormalization
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

open scoped Topology CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma continuous_columnCoreFunction (τ : ℝ) : Continuous (columnCoreFunction τ) := by
  unfold columnCoreFunction
  fun_prop

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ColumnCoreNorm
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

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma norm_column_core (D : B) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖cfc (columnCoreFunction τ) (star D*D)‖=max (‖D‖-τ) 0 := by
  obtain hB | hB := subsingleton_or_nontrivial B
  · have hD : D=0 := Subsingleton.elim _ _
    have hz : cfc (columnCoreFunction τ) (star D*D)=0 := Subsingleton.elim _ _
    rw [hz,norm_zero,hD,norm_zero]
    simp only [zero_sub,max_eq_right (neg_nonpos.mpr hτ)]
  let : Nontrivial B := hB
  apply le_antisymm
  · apply norm_cfc_le (le_max_right _ _)
    intro s hs
    have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg D) hs
    have hsn := (Real.le_norm_self s).trans (spectrum.norm_le_norm_of_mem hs)
    rw [CStarRing.norm_star_mul_self] at hsn
    have hsr : Real.sqrt s ≤ ‖D‖ := by
      nlinarith [Real.sq_sqrt hs0,Real.sqrt_nonneg s,norm_nonneg D]
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (by linarith) le_rfl
  · have he := norm_apply_le_norm_cfc (columnCoreFunction τ) (star D*D)
      (CStarAlgebra.norm_mem_spectrum_of_nonneg (a := star D * D) (star_mul_self_nonneg D))
      (continuous_columnCoreFunction τ).continuousOn (IsSelfAdjoint.star_mul_self D)
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),CStarRing.norm_star_mul_self] at he
    simpa only [columnCoreFunction,Real.sqrt_mul_self (norm_nonneg D)] using he

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CompressedStates
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

open scoped Topology ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_compressed_real_state {b g : A} (hb : 0 ≤ b) (hg : IsSelfAdjoint g)
    (hgn : ‖g‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδb : δ ≤ ‖g*b*g‖) :
    ∃ f ∈ realStateSpace A,δ ≤ f ⟨b,hb.isSelfAdjoint⟩ ∧
      ∀ c : A, f ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩ ≤
        (‖b‖/δ)*‖c*g‖^2 := by
  have hgbg : 0 ≤ g*b*g := by simpa only [hg.star_eq] using star_right_conjugate_nonneg hb g
  have hgbgn : g*b*g ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hδb
    exact (not_le_of_gt hδ) hδb
  let : Nontrivial A := nontrivial_of_ne _ _ hgbgn
  obtain ⟨f,hf,hfb⟩ := exists_norming_real_state (g*b*g) hgbg
  let Φ := realStateComplexification f hf
  let π := Φ.gnsStarAlgHom
  let Ω := gnsCyclicVector Φ
  let ξ := π g Ω
  have hΩ : ‖Ω‖=1 := norm_gnsCyclicVector Φ (realStateComplexification_one f hf)
  have hvec : representationVectorFunctional π ξ ⟨b,hb.isSelfAdjoint⟩=‖g*b*g‖ := by
    have he := DFunLike.congr_fun (gns_vectorFunctional_eq f hf) ⟨g*b*g,hgbg.isSelfAdjoint⟩
    change (inner ℂ Ω (π (g*b*g) Ω)).re=f ⟨g*b*g,hgbg.isSelfAdjoint⟩ at he
    rw [hfb] at he
    change (inner ℂ (π g Ω) (π b (π g Ω))).re=_
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hs : (π g).adjoint=π g := by
      change star (π g)=π g
      rw [← map_star,hg.star_eq]
    rw [hs]
    simpa only [map_mul,mul_apply_eq_comp] using he
  have hξle : ‖ξ‖ ≤ 1 := calc
    ‖ξ‖ ≤ ‖π g‖*‖Ω‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖g‖*‖Ω‖ := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom g
    _ ≤ 1 := by rw [hΩ,mul_one]; exact hgn
  have hξ : ξ ≠ 0 := by
    intro hz
    change ‖g*b*g‖ ≥ δ at hδb
    have he : representationVectorFunctional π ξ ⟨b,hb.isSelfAdjoint⟩=0 := by
      simp [representationVectorFunctional,hz]
    rw [hvec] at he
    exact (not_le_of_gt hδ) (he ▸ hδb)
  have ht : 0 < ‖ξ‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  have htone : ‖ξ‖^2 ≤ 1 := by nlinarith [norm_nonneg ξ]
  have hbnd : ‖g*b*g‖ ≤ ‖ξ‖^2*‖b‖ := by
    have he := (representationVectorFunctional π ξ).le_opNorm ⟨b,hb.isSelfAdjoint⟩
    rw [hvec,norm_norm] at he
    exact he.trans (mul_le_mul_of_nonneg_right (representationVectorFunctional_norm_le π ξ) (norm_nonneg b))
  have hinv : (‖ξ‖^2)⁻¹ ≤ ‖b‖/δ := by
    apply (le_div_iff₀ hδ).mpr
    apply (inv_mul_le_iff₀ ht).mpr
    nlinarith
  let F := StrongDual.toWeakDual ((‖ξ‖^2)⁻¹ • representationVectorFunctional π ξ)
  refine ⟨F,normalized_vector_mem_realStateSpace π hξ,?_,?_⟩
  · change δ ≤ (‖ξ‖^2)⁻¹*representationVectorFunctional π ξ ⟨b,hb.isSelfAdjoint⟩
    rw [hvec]
    apply (le_inv_mul_iff₀ ht).mpr
    exact (mul_le_of_le_one_left hδ.le htone).trans hδb
  · intro c
    change (‖ξ‖^2)⁻¹*representationVectorFunctional π ξ ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩ ≤ _
    rw [representationVectorFunctional_square]
    have hc : ‖π c ξ‖ ≤ ‖c*g‖ := calc
      _ = ‖π (c*g) Ω‖ := by rw [map_mul]; rfl
      _ ≤ ‖π (c*g)‖*‖Ω‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖c*g‖*‖Ω‖ := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _
      _ = ‖c*g‖ := by rw [hΩ,mul_one]
    exact mul_le_mul hinv (by nlinarith [norm_nonneg (π c ξ),norm_nonneg (c*g)])
      (sq_nonneg _) (div_nonneg (norm_nonneg b) hδ.le)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ElementaryComparison
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

open scoped NNReal

open Filter Topology

section ElementaryComparison

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m k : Type*} [Fintype m] [Fintype k]

lemma zero_cuntzSubequiv (b : CStarMatrix k k A) :
    CuntzSubequiv (0 : CStarMatrix m m A) b := by
  intro ε hε
  refine ⟨0, ?_⟩
  simpa using hε

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] in
lemma continuous_matrix_mul {l : Type*} [Fintype l] :
    Continuous (fun p : CStarMatrix m k A × CStarMatrix k l A => p.1 * p.2) := by
  change Continuous ((CStarMatrix.ofMatrixL : Matrix m l A ≃L[ℂ] CStarMatrix m l A) ∘
    fun p : CStarMatrix m k A × CStarMatrix k l A =>
      (CStarMatrix.ofMatrixL.symm p.1) * (CStarMatrix.ofMatrixL.symm p.2))
  apply Continuous.comp (ContinuousLinearEquiv.continuous _)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Matrix.mul_apply]
  fun_prop

omit [PartialOrder A] [StarOrderedRing A] in
lemma continuous_matrix_sandwich (v : CStarMatrix k m A) :
    Continuous (fun b : CStarMatrix k k A => v.conjTranspose * b * v) := by
  exact continuous_matrix_mul.comp <|
    (continuous_matrix_mul.comp (continuous_const.prodMk continuous_id)).prodMk continuous_const

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] in
lemma matrix_mul_assoc {l o : Type*} [Fintype l] [Fintype o]
    (a : CStarMatrix m k A) (b : CStarMatrix k l A) (c : CStarMatrix l o A) :
    a * b * c = a * (b * c) := Matrix.mul_assoc _ _ _

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] in
lemma matrix_conjTranspose_mul {l : Type*} [Fintype l]
    (a : CStarMatrix m k A) (b : CStarMatrix k l A) :
    (a * b).conjTranspose = b.conjTranspose * a.conjTranspose :=
  Matrix.conjTranspose_mul _ _

lemma cuntzSubequiv_iff_mem_closure {a : CStarMatrix m m A} {b : CStarMatrix k k A} :
    CuntzSubequiv a b ↔
      a ∈ closure (Set.range fun v : CStarMatrix k m A => v.conjTranspose * b * v) := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨v, hv⟩ := h ε hε
    exact ⟨_, ⟨v, rfl⟩, by simpa [dist_eq_norm, norm_sub_rev] using hv⟩
  · intro h ε hε
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h ε hε
    exact ⟨v, by simpa [dist_eq_norm, norm_sub_rev] using hv⟩

lemma CuntzSubequiv.trans {l : Type*} [Fintype l]
    {a : CStarMatrix m m A} {b : CStarMatrix k k A} {c : CStarMatrix l l A}
    (hab : CuntzSubequiv a b) (hbc : CuntzSubequiv b c) : CuntzSubequiv a c := by
  intro ε hε
  obtain ⟨v, hv⟩ := hab (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_matrix_sandwich v).continuousAt (ε / 2) (by positivity)
  obtain ⟨w, hw⟩ := hbc δ hδ
  refine ⟨w * v, ?_⟩
  have heq : (w * v).conjTranspose * c * (w * v) =
      v.conjTranspose * (w.conjTranspose * c * w) * v := by
    rw [matrix_conjTranspose_mul]
    simp only [matrix_mul_assoc]
  rw [heq]
  have ht := hcont (by simpa only [dist_eq_norm] using hw)
  have hnorm := norm_sub_le_norm_sub_add_norm_sub
    (v.conjTranspose * (w.conjTranspose * c * w) * v) (v.conjTranspose * b * v) a
  simp only [dist_eq_norm] at ht
  linarith

lemma cuntzSubequiv_refl (a : CStarMatrix m m A) : CuntzSubequiv a a := by
  let au := CStarAlgebra.increasingApproximateUnit (CStarMatrix m m A)
  intro ε hε
  have hl := Metric.tendsto_nhds.mp (au.tendsto_mul_left a) (ε / 2) (by positivity)
  have hr := Metric.tendsto_nhds.mp (au.tendsto_mul_right a) (ε / 2) (by positivity)
  obtain ⟨u, hleft, hright, hstar, hnorm⟩ :=
    (hl.and (hr.and (au.eventually_star_eq.and au.eventually_norm))).exists
  refine ⟨u, ?_⟩
  rw [← CStarMatrix.star_eq_conjTranspose, hstar]
  have heq : u * a * u - a = (u * a - a) * u + (a * u - a) := by noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖(u * a - a) * u‖ + ‖a * u - a‖ := norm_add_le _ _
    _ ≤ ‖u * a - a‖ * ‖u‖ + ‖a * u - a‖ := add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ ‖u * a - a‖ + ‖a * u - a‖ := by
      have hbound : ‖u * a - a‖ * ‖u‖ ≤ ‖u * a - a‖ := by
        nlinarith [norm_nonneg (u * a - a)]
      exact add_le_add hbound le_rfl
    _ < ε := by simp only [dist_eq_norm] at hleft hright <;> linarith

end ElementaryComparison

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CuntzCopies
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

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] [Fintype l] in
lemma continuous_blockSum : Continuous (fun p : CStarMatrix m m A × CStarMatrix n n A => blockSum p.1 p.2) := by
  change Continuous (fun p : Matrix m m A × Matrix n n A => Matrix.fromBlocks p.1 0 0 p.2)
  exact continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd

lemma CuntzSubequiv.blockSum {a : CStarMatrix m m A} {b : CStarMatrix n n A}
    {c : CStarMatrix k k A} {d : CStarMatrix l l A}
    (hab : CuntzSubequiv a b) (hcd : CuntzSubequiv c d) :
    CuntzSubequiv (blockSum a c) (blockSum b d) := by
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_blockSum (m := m) (n := k) (A := A)).continuousAt ε hε
  obtain ⟨v, hv⟩ := hab δ hδ
  obtain ⟨w, hw⟩ := hcd δ hδ
  let V : CStarMatrix (n ⊕ l) (m ⊕ k) A := Matrix.fromBlocks v 0 0 w
  refine ⟨V, ?_⟩
  have he : V.conjTranspose*WeakPureInfiniteness.blockSum b d*V = WeakPureInfiniteness.blockSum (v.conjTranspose*b*v) (w.conjTranspose*d*w) := by
    change (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm v) 0 0 (CStarMatrix.ofMatrix.symm w)).conjTranspose *
      Matrix.fromBlocks (CStarMatrix.ofMatrix.symm b) 0 0 (CStarMatrix.ofMatrix.symm d) * Matrix.fromBlocks (CStarMatrix.ofMatrix.symm v) 0 0 (CStarMatrix.ofMatrix.symm w) =
        Matrix.fromBlocks ((CStarMatrix.ofMatrix.symm v).conjTranspose*(CStarMatrix.ofMatrix.symm b)*(CStarMatrix.ofMatrix.symm v)) 0 0
          ((CStarMatrix.ofMatrix.symm w).conjTranspose*(CStarMatrix.ofMatrix.symm d)*(CStarMatrix.ofMatrix.symm w))
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [he]
  have hp : dist (v.conjTranspose*b*v, w.conjTranspose*d*w) (a,c) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (by simpa only [dist_eq_norm] using hv) (by simpa only [dist_eq_norm] using hw)
  simpa only [dist_eq_norm] using hcont hp

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] [Fintype l] in
lemma continuous_matrixSubmatrix (e : m → n) (f : k → l) : Continuous (matrixSubmatrix (A := A) e f) := by
  change Continuous (fun M : Matrix n l A => M.submatrix e f)
  fun_prop

lemma CuntzSubequiv.submatrix_left {a : CStarMatrix n n A} {b : CStarMatrix k k A}
    (hab : CuntzSubequiv a b) (e : m → n) : CuntzSubequiv (matrixSubmatrix e e a) b := by
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_matrixSubmatrix (A := A) e e).continuousAt ε hε
  obtain ⟨v, hv⟩ := hab δ hδ
  refine ⟨matrixSubmatrix id e v, ?_⟩
  have he : (matrixSubmatrix id e v).conjTranspose*b*matrixSubmatrix id e v =
      matrixSubmatrix e e (v.conjTranspose*b*v) := by
    ext i j
    simp only [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply, matrixSubmatrix, id_eq]
  rw [he]
  simpa only [dist_eq_norm] using hcont (by simpa only [dist_eq_norm] using hv)

omit [PartialOrder A] [StarOrderedRing A] in
lemma diagonalCopies_submatrix (a : A) {d r : ℕ} (e : Fin d → Fin r)
    (he : Function.Injective e) : matrixSubmatrix e e (diagonalCopies r a) = diagonalCopies d a := by
  ext i j
  simp only [matrixSubmatrix, diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply]
  simp only [he.eq_iff]

lemma diagonalCopies_cuntzSubequiv (a : A) {d r : ℕ} (hdr : d ≤ r) :
    CuntzSubequiv (diagonalCopies d a) (diagonalCopies r a) := by
  have h := (cuntzSubequiv_refl (diagonalCopies r a)).submatrix_left (Fin.castLE hdr)
  rwa [diagonalCopies_submatrix a _ (Fin.castLE_injective hdr)] at h

omit [PartialOrder A] [StarOrderedRing A] in
lemma diagonalCopies_double (a : A) (r : ℕ) :
    matrixSubmatrix (finSumFinEquiv.symm : Fin (r+r) → Fin r ⊕ Fin r)
      finSumFinEquiv.symm (blockSum (diagonalCopies r a) (diagonalCopies r a)) =
        diagonalCopies (r+r) a := by
  classical
  change (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin r => a)) 0 0
    (Matrix.diagonal (fun _ : Fin r => a))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      Matrix.diagonal (fun _ : Fin (r+r) => a)
  rw [Matrix.fromBlocks_diagonal]
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  cases finSumFinEquiv.symm i <;> rfl

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Hereditary
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeSpatialAmbientMemNonUnitalStarSubalgebraComplexMinimalTensor _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

lemma square_mem_hereditary (h : A) (hh : IsSelfAdjoint h) :
    h*h ∈ hereditarySubalgebra h hh := by
  have ht : Tendsto (fun e : A => h*e*h) (CStarAlgebra.approximateUnit A) (𝓝 (h*h)) :=
    ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const h
  exact (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto ht
    (Eventually.of_forall (fun e => sandwich_mem h e hh))

lemma sqrt_mem_hereditary (h x : A) (hh : IsSelfAdjoint h)
    (hx : x ∈ hereditarySubalgebra h hh) (hxpos : 0 ≤ x) :
    CFC.sqrt x ∈ hereditarySubalgebra h hh := by
  rw [CFC.sqrt_eq_real_sqrt x hxpos]
  exact cfcₙ_mem Real.sqrt hx

lemma self_mem_hereditary (h : A) (hh : 0 ≤ h) :
    h ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  convert sqrt_mem_hereditary h (h*h) hh.isSelfAdjoint
    (square_mem_hereditary h hh.isSelfAdjoint) (by simpa only [hh.star_eq] using star_mul_self_nonneg h) using 1
  all_goals try with_reducible_and_instances rfl
  exact (CFC.sqrt_mul_self h hh).symm

omit [PartialOrder A] [StarOrderedRing A] in
lemma principalRightIdeal_mul_mem (h a b : A) (ha : a ∈ principalRightIdeal h) :
    a*b ∈ principalRightIdeal h := by
  have hc : IsClosed {a : A | a*b ∈ principalRightIdeal h} :=
    (Submodule.isClosed_topologicalClosure _).preimage (continuous_id.mul_const b)
  apply closure_minimal _ hc ha
  rintro _ ⟨c, rfl⟩
  exact Submodule.le_topologicalClosure _ ⟨c*b, by change h*(c*b) = (h*c)*b; simp only [mul_assoc]⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_le_rightIdeal (h : A) (hh : IsSelfAdjoint h) :
    (hereditarySubalgebra h hh : Set A) ⊆ principalRightIdeal h := by
  apply closure_minimal _ (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨b, rfl⟩
  exact Submodule.le_topologicalClosure _ ⟨b*h, by change h*(b*h) = h*b*h; simp only [mul_assoc]⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma rightIdeal_square_mem_hereditary (h a : A) (hh : IsSelfAdjoint h)
    (ha : a ∈ principalRightIdeal h) : a * star a ∈ hereditarySubalgebra h hh := by
  have hc : IsClosed {a : A | a * star a ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc ha
  rintro _ ⟨b, rfl⟩
  change (h*b)*star (h*b) ∈ hereditarySubalgebra h hh
  convert sandwich_mem h (b*star b) hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [star_mul, hh.star_eq, mul_assoc]

lemma residual_nonneg (e h : A) (he : IsSelfAdjoint e) (hh : 0 ≤ h) :
    0 ≤ residual e h := by
  have hs : CFC.sqrt h * CFC.sqrt h = h := CFC.sqrt_mul_sqrt_self h hh
  convert mul_star_self_nonneg (CFC.sqrt h-e*CFC.sqrt h) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [residual, star_sub, star_mul, (CFC.sqrt_nonneg h).star_eq, he.star_eq]
  rw [show (CFC.sqrt h-e*CFC.sqrt h) * (CFC.sqrt h-CFC.sqrt h*e) =
    CFC.sqrt h*CFC.sqrt h-e*(CFC.sqrt h*CFC.sqrt h) -
      (CFC.sqrt h*CFC.sqrt h)*e+e*(CFC.sqrt h*CFC.sqrt h)*e by noncomm_ring, hs]

lemma residual_mono (e : A) (he : IsSelfAdjoint e) {h k : A} (hkh : h ≤ k) :
    residual e h ≤ residual e k := by
  apply sub_nonneg.mp
  convert residual_nonneg e (k-h) he (sub_nonneg.mpr hkh) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [residual]
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma residual_square (e a : A) (he : IsSelfAdjoint e) :
    residual e (a*star a) = (a-e*a)*star (a-e*a) := by
  simp only [residual, star_sub, star_mul, he.star_eq]
  noncomm_ring

lemma norm_sub_left_mul_sq_le (e h a : A) (he : IsSelfAdjoint e)
    (ha : a*star a ≤ h) : ‖a-e*a‖^2 ≤ ‖residual e h‖ := by
  have hb := CStarAlgebra.norm_le_norm_of_le_of_nonneg (residual_mono e he ha)
    (residual_nonneg e (a*star a) he (mul_star_self_nonneg a))
  rw [residual_square e a he, CStarRing.norm_self_mul_star] at hb
  simpa only [pow_two] using hb

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_residual_le (e h : A) (he : ‖e‖ ≤ 1) :
    ‖residual e h‖ ≤ 2 * ‖h-e*h‖ := by
  have hr : residual e h = (h-e*h) - (h-e*h)*e := by
    simp only [residual]
    noncomm_ring
  rw [hr]
  calc
    ‖(h-e*h) - (h-e*h)*e‖ ≤ ‖h-e*h‖ + ‖(h-e*h)*e‖ := norm_sub_le _ _
    _ ≤ ‖h-e*h‖ + ‖h-e*h‖*‖e‖ := add_le_add le_rfl (norm_mul_le _ _)
    _ ≤ ‖h-e*h‖ + ‖h-e*h‖*1 := by gcongr
    _ = 2*‖h-e*h‖ := by ring

lemma norm_sub_left_mul_le_sqrt (e h a : A) (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : a*star a ≤ h) : ‖a-e*a‖ ≤ Real.sqrt (2*‖h-e*h‖) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  exact (norm_sub_left_mul_sq_le e h a he ha).trans (norm_residual_le e h hen)

lemma principalRightIdeal_of_square_le (h a : A) (hh : 0 ≤ h) (ha : a*star a ≤ h) :
    a ∈ principalRightIdeal h := by
  let S := hereditarySubalgebra h hh.isSelfAdjoint
  let := CStarAlgebra.spectralOrder S
  let := CStarAlgebra.spectralOrderedRing S
  let h₀ : S := ⟨h, self_mem_hereditary h hh⟩
  let F := CStarAlgebra.approximateUnit S
  have hF := CStarAlgebra.increasingApproximateUnit S
  have ht : Tendsto (fun e : S => (e:A)*h) F (𝓝 h) := by
    exact (continuous_subtype_val.tendsto h₀).comp (hF.tendsto_mul_right h₀)
  have hd : Tendsto (fun e : S => ‖h-(e:A)*h‖) F (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : S => h) F (𝓝 h)).sub ht).norm
  have hb : Tendsto (fun e : S => Real.sqrt (2*‖h-(e:A)*h‖)) F (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using (hd.const_mul 2).sqrt
  have hn : Tendsto (fun e : S => ‖a-(e:A)*a‖) F (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
    filter_upwards [hF.eventually_isSelfAdjoint, hF.eventually_norm] with e he hen
    exact norm_sub_left_mul_le_sqrt (e:A) h a
      (show IsSelfAdjoint (e:A) from congrArg Subtype.val he) hen ha
  have ht' : Tendsto (fun e : S => (e:A)*a) F (𝓝 a) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [norm_sub_rev] using hn
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht'
    (Eventually.of_forall (fun e => principalRightIdeal_mul_mem h (e:A) a
      (hereditary_le_rightIdeal h hh.isSelfAdjoint e.property)))

omit [PartialOrder A] [StarOrderedRing A] in
lemma principalRightIdeal_le_of_mem {h a : A} (ha : a ∈ principalRightIdeal h) :
    principalRightIdeal a ≤ principalRightIdeal h := by
  intro x hx
  apply closure_minimal _ (Submodule.isClosed_topologicalClosure _) hx
  rintro _ ⟨b, rfl⟩
  exact principalRightIdeal_mul_mem h a b ha

omit [PartialOrder A] [StarOrderedRing A] in
lemma principalRightIdeal_smul_le (h : A) (c : ℝ) :
    principalRightIdeal (c•h) ≤ principalRightIdeal h := by
  intro x hx
  apply closure_minimal _ (Submodule.isClosed_topologicalClosure _) hx
  rintro _ ⟨b, rfl⟩
  exact Submodule.le_topologicalClosure _ ⟨c•b, by
    change h*(c•b) = (c•h)*b
    simp only [mul_smul_comm, smul_mul_assoc]⟩

lemma principalRightIdeal_of_square_le_smul (h a : A) (hh : 0 ≤ h)
    {c : ℝ} (hc : 0 ≤ c) (ha : a*star a ≤ c•h) : a ∈ principalRightIdeal h :=
  principalRightIdeal_smul_le h c (principalRightIdeal_of_square_le (c•h) a
    (smul_nonneg hc hh) ha)

lemma mem_hereditary_of_le_smul (h x : A) (hh : 0 ≤ h) (hx : 0 ≤ x)
    {c : ℝ} (hc : 0 ≤ c) (hxh : x ≤ c•h) :
    x ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  have hs : CFC.sqrt x * star (CFC.sqrt x) = x := by
    rw [(CFC.sqrt_nonneg x).star_eq, CFC.sqrt_mul_sqrt_self x hx]
  rw [← hs]
  exact rightIdeal_square_mem_hereditary h _ hh.isSelfAdjoint
    (principalRightIdeal_of_square_le_smul h _ hh hc (by rwa [hs]))

lemma principalRightIdeal_sqrt (h : A) (hh : 0 ≤ h) :
    principalRightIdeal (CFC.sqrt h) = principalRightIdeal h := by
  apply le_antisymm
  · apply principalRightIdeal_le_of_mem
    exact hereditary_le_rightIdeal h hh.isSelfAdjoint
      (sqrt_mem_hereditary h h hh.isSelfAdjoint (self_mem_hereditary h hh) hh)
  · apply principalRightIdeal_le_of_mem
    have hs : CFC.sqrt h*CFC.sqrt h ∈ principalRightIdeal (CFC.sqrt h) :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ (CFC.sqrt h))
    simpa only [CFC.sqrt_mul_sqrt_self h hh] using hs

lemma exists_comparison_of_rightIdeal (h a : A) (hh : 0 ≤ h)
    (ha : a ∈ principalRightIdeal h) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖star v*h*v - star a*a‖ < ε := by
  have ha' : a ∈ principalRightIdeal (CFC.sqrt h) := by
    rwa [principalRightIdeal_sqrt h hh]
  let F : Set A := closure (Set.range (fun v : A => star v*h*v))
  have hc : IsClosed {a : A | star a*a ∈ F} :=
    isClosed_closure.preimage (by fun_prop)
  have hamem : star a*a ∈ F := by
    apply closure_minimal _ hc ha'
    rintro _ ⟨v, rfl⟩
    apply subset_closure
    refine ⟨v, ?_⟩
    change star v*h*v = star (CFC.sqrt h*v)*(CFC.sqrt h*v)
    rw [star_mul, (CFC.sqrt_nonneg h).star_eq]
    calc
      star v*h*v = star v*(CFC.sqrt h*CFC.sqrt h)*v := by
        rw [CFC.sqrt_mul_sqrt_self h hh]
      _ = star v*CFC.sqrt h*(CFC.sqrt h*v) := by noncomm_ring
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hamem ε hε
  exact ⟨v, by simpa only [dist_eq_norm, norm_sub_rev] using hv⟩

lemma exists_comparison_of_hereditary (h x : A) (hh : 0 ≤ h) (hx : 0 ≤ x)
    (hmem : x ∈ hereditarySubalgebra h hh.isSelfAdjoint) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖star v*h*v-x‖ < ε := by
  have hs : star (CFC.sqrt x)*CFC.sqrt x = x := by
    rw [(CFC.sqrt_nonneg x).star_eq, CFC.sqrt_mul_sqrt_self x hx]
  have ha := hereditary_le_rightIdeal h hh.isSelfAdjoint
    (sqrt_mem_hereditary h x hh.isSelfAdjoint hmem hx)
  simpa only [hs] using exists_comparison_of_rightIdeal h (CFC.sqrt x) hh ha ε hε

lemma exists_comparison_of_star_mul (u : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖star v*(u*star u)*v - star u*u‖ < ε :=
  exists_comparison_of_rightIdeal (u*star u) u (mul_star_self_nonneg u)
    (principalRightIdeal_of_square_le (u*star u) u (mul_star_self_nonneg u) le_rfl) ε hε

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralCut
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

open scoped Topology CStarAlgebra

lemma continuous_spectralRamp (θ : ℝ) : Continuous (spectralRamp θ) := by
  unfold spectralRamp
  fun_prop

lemma spectralRamp_nonneg (θ s : ℝ) : 0 ≤ spectralRamp θ s :=
  le_min zero_le_one (le_max_left _ _)

lemma spectralRamp_le_one (θ s : ℝ) : spectralRamp θ s ≤ 1 := min_le_left _ _

lemma spectralRamp_eq_zero {θ s : ℝ} (hθ : 0 < θ) (hs : s ≤ θ) :
    spectralRamp θ s = 0 := by
  unfold spectralRamp
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hθ.le)]
  exact min_eq_right zero_le_one

lemma spectralRamp_eq_one {θ s : ℝ} (hθ : 0 < θ) (hs : 2*θ ≤ s) :
    spectralRamp θ s = 1 := by
  unfold spectralRamp
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  rw [le_div_iff₀ hθ]
  linarith

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PerturbationRows
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

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleton_diagonal (x : A) : matrixSingletonHom (diagonalCopies 1 x)=x := rfl

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalConnection
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

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma elementCuntzSubequiv_iff {a b : A} : ElementCuntzSubequiv a b ↔
    ∀ ε : ℝ,0 < ε → ∃ v : A,‖star v*b*v-a‖ < ε := by
  constructor
  · intro hab ε hε
    obtain ⟨v,hv⟩ := hab ε hε
    refine ⟨matrixSingletonHom v,?_⟩
    have he := NonUnitalStarAlgHom.norm_apply_le (matrixSingletonHom (A := A))
      (star v*diagonalCopies 1 b*v-diagonalCopies 1 a)
    simp only [map_sub,map_mul,map_star,singleton_diagonal] at he
    exact he.trans_lt hv
  · intro hab ε hε
    obtain ⟨v,hv⟩ := hab ε hε
    refine ⟨diagonalCopies 1 v,?_⟩
    have he := NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 1) (star v*b*v-a)
    simp only [map_sub,map_mul,map_star,CStarMatrix.star_eq_conjTranspose] at he
    exact he.trans_lt hv

lemma elementCuntzSubequiv_of_hereditary {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : a ∈ hereditarySubalgebra b hb.isSelfAdjoint) : ElementCuntzSubequiv a b :=
  elementCuntzSubequiv_iff.mpr (exists_comparison_of_hereditary b a hb ha hm)

lemma element_initial_cuntz_range (z : A) : ElementCuntzSubequiv (star z*z) (z*star z) :=
  elementCuntzSubequiv_iff.mpr (exists_comparison_of_star_mul z)

lemma element_range_cuntz_initial (z : A) : ElementCuntzSubequiv (z*star z) (star z*z) := by
  simpa only [star_star] using element_initial_cuntz_range (star z)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularComparison
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

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

lemma CuntzSubequiv.sandwich_left {x : CStarMatrix n n A} {h : CStarMatrix m m A}
    (hxh : CuntzSubequiv x h) (v : CStarMatrix n k A) :
    CuntzSubequiv (v.conjTranspose*x*v) h := by
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_matrix_sandwich v).continuousAt ε hε
  obtain ⟨w,hw⟩ := hxh δ hδ
  refine ⟨w*v, ?_⟩
  rw [rectangular_star_mul]
  have he : (v.conjTranspose*w.conjTranspose)*h*(w*v) =
      v.conjTranspose*(w.conjTranspose*h*w)*v := by
    simp only [rectangular_mul_assoc]
  rw [he]
  simpa only [dist_eq_norm] using hcont (by simpa only [dist_eq_norm] using hw)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_IdealComparison
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

open Filter

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma elementCuntzSubequiv_of_le_smul {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {c : ℝ} (hc : 0 ≤ c) (hab : a ≤ c • b) : ElementCuntzSubequiv a b :=
  elementCuntzSubequiv_of_hereditary ha hb (mem_hereditary_of_le_smul b a hb ha hc hab)

omit [PartialOrder A] [StarOrderedRing A] in
lemma blockSum_one_sandwich (a b e : A) :
    (oneBlockColumn e).conjTranspose * blockSum (diagonalCopies 1 a) (diagonalCopies 1 b) *
      oneBlockColumn e = diagonalCopies 1 (star e*(a+b)*e) := by
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  simp only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,oneBlockColumn,
    Fintype.sum_sum_type,Fin.sum_univ_one,blockSum,diagonalCopies,
    CStarMatrix.ofMatrix_apply,Equiv.symm_apply_apply,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.diagonal_apply_eq,
    Matrix.zero_apply,mul_zero,zero_add,add_zero]
  noncomm_ring

lemma sum_two_cuntz_block (a b : A) :
    CuntzSubequiv (diagonalCopies 1 (a+b)) (blockSum (diagonalCopies 1 a) (diagonalCopies 1 b)) := by
  intro ε hε
  obtain ⟨v,hv⟩ := elementCuntzSubequiv_iff.mp
    (cuntzSubequiv_refl (diagonalCopies 1 (a+b))) ε hε
  refine ⟨oneBlockColumn v,?_⟩
  rw [blockSum_one_sandwich]
  have hn := NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 1)
    (star v*(a+b)*v-(a+b))
  rw [map_sub] at hn
  exact hn.trans_lt hv

lemma star_add_mul_add_le (x y : A) :
    star (x+y)*(x+y) ≤ (2 : ℝ) • (star x*x+star y*y) := by
  have h := star_mul_self_nonneg (x-y)
  have he : (2 : ℝ) • (star x*x+star y*y)-star (x+y)*(x+y)=star (x-y)*(x-y) := by
    simp only [two_smul,star_sub,star_add]
    noncomm_ring
  exact sub_nonneg.mp (he.symm ▸ h)

lemma star_mul_product_cuntz (a z : A) :
    ElementCuntzSubequiv (star (a*z)*(a*z)) (star z*z) := by
  
  apply (element_initial_cuntz_range (a*z)).trans
  have hc := (cuntzSubequiv_refl (diagonalCopies 1 (z*star z))).sandwich_left (diagonalCopies 1 (star a))
  have he : (diagonalCopies 1 (star a)).conjTranspose*diagonalCopies 1 (z*star z)*diagonalCopies 1 (star a)=
      diagonalCopies 1 ((a*z)*star (a*z)) := by
    change star ((diagonalHom 1) (star a))*(diagonalHom 1) (z*star z)*(diagonalHom 1) (star a)=
      (diagonalHom 1) ((a*z)*star (a*z))
    rw [← map_star,← map_mul,← map_mul,star_star]
    apply congrArg (diagonalHom (A := A) 1)
    rw [star_mul]
    noncomm_ring
  rw [he] at hc
  exact hc.trans (element_range_cuntz_initial z)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_IdealSpan
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

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraicIdealSpan_mul_right (h a : A) {x : A} (hx : x ∈ algebraicIdealSpan h) :
    x*a ∈ algebraicIdealSpan h := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨c,d⟩,rfl⟩ := hy
    exact Submodule.subset_span ⟨(c,d*a),by simp only [mul_assoc]⟩
  | zero => simpa only [zero_mul] using (algebraicIdealSpan h).zero_mem
  | add y z _ _ hy hz => simpa only [add_mul] using (algebraicIdealSpan h).add_mem hy hz
  | smul c y _ hy => simpa only [smul_mul_assoc] using (algebraicIdealSpan h).smul_mem c hy

omit [PartialOrder A] [StarOrderedRing A] in
lemma generatedClosedIdeal_mul_left (h a : A) (hh : IsSelfAdjoint h) {x : A}
    (hx : x ∈ generatedClosedIdeal h hh) : a*x ∈ generatedClosedIdeal h hh := by
  apply closure_minimal _ ((NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
    (continuous_const.mul continuous_id)) hx
  intro y hy
  exact (algebraicIdealSubalgebra h hh).le_topologicalClosure (algebraicIdealSpan_mul_left h a hy)

omit [PartialOrder A] [StarOrderedRing A] in
lemma generatedClosedIdeal_mul_right (h a : A) (hh : IsSelfAdjoint h) {x : A}
    (hx : x ∈ generatedClosedIdeal h hh) : x*a ∈ generatedClosedIdeal h hh := by
  apply closure_minimal _ ((NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
    (continuous_id.mul continuous_const)) hx
  intro y hy
  exact (algebraicIdealSubalgebra h hh).le_topologicalClosure (algebraicIdealSpan_mul_right h a hy)

lemma hereditary_le_generatedClosedIdeal (h : A) (hh : IsSelfAdjoint h) :
    hereditarySubalgebra h hh ≤ generatedClosedIdeal h hh := by
  intro x hx
  apply closure_minimal _ (NonUnitalStarSubalgebra.isClosed_topologicalClosure _) hx
  rintro _ ⟨a,rfl⟩
  have ht : Filter.Tendsto (fun e : A => (h*a)*h*e) (CStarAlgebra.approximateUnit A)
      (𝓝 (h*a*h)) := (CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left _
  exact (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun e => (algebraicIdealSubalgebra h hh).le_topologicalClosure
      (Submodule.subset_span ⟨(h*a,e),rfl⟩)))

lemma self_mem_generatedClosedIdeal (h : A) (hh : 0 ≤ h) :
    h ∈ generatedClosedIdeal h hh.isSelfAdjoint :=
  hereditary_le_generatedClosedIdeal h hh.isSelfAdjoint (self_mem_hereditary h hh)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_IdealComparison2
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma CuntzSubequiv.copies_of_properlyInfinite_right
    {m : Type*} [Fintype m] {a : A} {H : CStarMatrix m m A}
    (haH : CuntzSubequiv (diagonalCopies 1 a) H) (hH : ProperlyInfinite H) (k : ℕ) :
    CuntzSubequiv (diagonalCopies k a) H := by
  have hp : ∀ j : ℕ,CuntzSubequiv (diagonalCopies (2^j) a) H := by
    intro j
    induction j with
    | zero => exact haH
    | succ j ih =>
      have h := ((ih.blockSum ih).trans hH).submatrix_left
        (finSumFinEquiv.symm : Fin (2^j+2^j) → Fin (2^j) ⊕ Fin (2^j))
      rw [diagonalCopies_double] at h
      have he : 2^(j+1)=2^j+2^j := by rw [pow_succ,Nat.mul_two]
      rw [he]
      exact h
  exact (diagonalCopies_cuntzSubequiv a (Nat.lt_two_pow_self (n := k)).le).trans (hp k)

lemma algebraicIdealSpan_square_cuntz {h : A} (hh : 0 ≤ h) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ProperlyInfinite (diagonalCopies n h)) {x : A} (hx : x ∈ algebraicIdealSpan h) :
    CuntzSubequiv (diagonalCopies 1 (star x*x)) (diagonalCopies n h) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hy
    have hc : ElementCuntzSubequiv (star (a*h*b)*(a*h*b)) (star (h*b)*(h*b)) := by
      simpa only [mul_assoc] using star_mul_product_cuntz a (h*b)
    apply hc.trans ((element_initial_cuntz_range (h*b)).trans _)
    apply (elementCuntzSubequiv_of_hereditary (mul_star_self_nonneg (h*b)) hh ?_).trans
      (diagonalCopies_cuntzSubequiv h hn)
    have he : (h*b)*star (h*b)=h*(b*star b)*h := by rw [star_mul,hh.star_eq]; noncomm_ring
    rw [he]
    exact sandwich_mem h (b*star b) hh.isSelfAdjoint
  | zero =>
    have he : diagonalCopies 1 (star (0 : A)*0)=0 := by ext i j; simp [diagonalCopies]
    rw [he]
    exact zero_cuntzSubequiv _
  | add x y _ _ hx hy =>
    apply (elementCuntzSubequiv_of_le_smul (star_mul_self_nonneg (x+y))
      (add_nonneg (star_mul_self_nonneg x) (star_mul_self_nonneg y)) (by norm_num : (0 : ℝ) ≤ 2)
      (star_add_mul_add_le x y)).trans
    exact (sum_two_cuntz_block (star x*x) (star y*y)).trans ((hx.blockSum hy).trans hpi)
  | smul c x _ hx =>
    apply (elementCuntzSubequiv_of_hereditary (star_mul_self_nonneg (c•x))
      (star_mul_self_nonneg x) ?_).trans hx
    have hm := (hereditarySubalgebra (star x*x) (star_mul_self_nonneg x).isSelfAdjoint).smul_mem
      (c*star c) (self_mem_hereditary (star x*x) (star_mul_self_nonneg x))
    simp only [star_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
    exact hm

theorem generatedClosedIdeal_copies_cuntz {h x : A} (hh : 0 ≤ h) (hx : 0 ≤ x)
    {n : ℕ} (hn : 1 ≤ n) (hpi : ProperlyInfinite (diagonalCopies n h))
    (hm : x ∈ generatedClosedIdeal h hh.isSelfAdjoint) (k : ℕ) :
    CuntzSubequiv (diagonalCopies k x) (diagonalCopies n h) := by
  have hs : CFC.sqrt x ∈ generatedClosedIdeal h hh.isSelfAdjoint := by
    rw [CFC.sqrt_eq_real_sqrt x hx]
    exact cfcₙ_mem Real.sqrt hm
  have hclosed : IsClosed {a : A | CuntzSubequiv
      (diagonalCopies 1 (star a*a)) (diagonalCopies n h)} := by
    simp only [cuntzSubequiv_iff_mem_closure]
    exact isClosed_closure.preimage
      ((map_continuous (diagonalHom (A := A) 1)).comp (continuous_star.mul continuous_id))
  have hc : CuntzSubequiv (diagonalCopies 1 (star (CFC.sqrt x)*CFC.sqrt x))
      (diagonalCopies n h) :=
    closure_minimal (fun a ha => algebraicIdealSpan_square_cuntz hh hn hpi ha) hclosed hs
  rw [(CFC.sqrt_nonneg x).star_eq,CFC.sqrt_mul_sqrt_self x hx] at hc
  exact hc.copies_of_properlyInfinite_right hpi k

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_IdealSeparation
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeSpatialAmbientMemNonUnitalStarSubalgebraComplexMinimalTensor _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped Topology ComplexOrder InnerProductSpace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_annihilator_state_of_not_mem
    (I : NonUnitalStarSubalgebra ℂ A) (hI : IsClosed (I : Set A))
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I)
    {b : A} (hb : 0 ≤ b) (hbI : b ∉ I) :
    ∃ f ∈ annihilatorStates (I : Set A),0 < f ⟨b,hb.isSelfAdjoint⟩ := by
  classical
  let : IsClosed (I : Set A) := hI
  let : CompleteSpace I := hI.isComplete.completeSpace_coe
  let := CStarAlgebra.spectralOrder I
  let := CStarAlgebra.spectralOrderedRing I
  let L := CStarAlgebra.approximateUnit I
  have hL := CStarAlgebra.increasingApproximateUnit I
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hI.isOpen_compl.mem_nhds hbI)
  have hdist : ∀ y ∈ I,δ ≤ ‖b-y‖ := by
    intro y hy
    by_contra! hn
    have hyb : y ∈ Metric.ball b δ := by
      rw [Metric.mem_ball,dist_eq_norm,norm_sub_rev]
      exact hn
    exact hball hyb hy
  have hb0 : b ≠ 0 := fun hz => hbI (hz ▸ I.zero_mem)
  let : Nontrivial A := nontrivial_of_ne _ _ hb0
  obtain ⟨f₀,hf₀,_⟩ := exists_norming_real_state b hb
  let Good : I → Prop := fun e => 0 ≤ (e : A) ∧ ‖(e : A)‖ ≤ 1
  have hgood : ∀ᶠ e in L,Good e := by
    filter_upwards [hL.eventually_nonneg,hL.eventually_norm] with e he hen
    have heq : (e : A)=star ((CFC.sqrt e : I) : A)*((CFC.sqrt e : I) : A) := by
      have hh : e=star (CFC.sqrt e)*CFC.sqrt e := by
        rw [(CFC.sqrt_nonneg e).star_eq,CFC.sqrt_mul_sqrt_self e he]
      exact congrArg (fun x : I => (x : A)) hh
    exact ⟨heq.symm ▸ star_mul_self_nonneg (((CFC.sqrt e : I) : A)),hen⟩
  have hex : ∀ e : I,∃ f ∈ realStateSpace A,Good e →
      δ ≤ f ⟨b,hb.isSelfAdjoint⟩ ∧ ∀ c : A,
        f ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩ ≤
          (‖b‖/δ)*‖c*(1-(e : A))‖^2 := by
    intro e
    by_cases he : Good e
    · have heone : (e : A) ≤ 1 := (CStarAlgebra.mem_Icc_iff_norm_le_one.mpr he).2
      have hgn : ‖1-(e : A)‖ ≤ 1 :=
        (CStarAlgebra.mem_Icc_iff_norm_le_one.mp
          ⟨sub_nonneg.mpr heone,sub_le_self _ he.1⟩).2
      have hresI : b-(1-(e : A))*b*(1-(e : A)) ∈ I := by
        have heq : b-(1-(e : A))*b*(1-(e : A))=
            (e : A)*b+b*(e : A)-(e : A)*b*(e : A) := by noncomm_ring
        rw [heq]
        exact I.sub_mem (I.add_mem (hIR e e.property b) (hIL e e.property b))
          (hIR (e*b) (hIR e e.property b) e)
      have hdb : δ ≤ ‖(1-(e : A))*b*(1-(e : A))‖ := by
        simpa only [sub_sub_cancel] using hdist _ hresI
      obtain ⟨f,hf,hfb,hfc⟩ := exists_compressed_real_state hb
        (by change star (1-(e:A))=1-(e:A); rw [star_sub,star_one,he.1.star_eq]) hgn hδ hdb
      exact ⟨f,hf,fun _ => ⟨hfb,hfc⟩⟩
    · exact ⟨f₀,hf₀,fun hh => (he hh).elim⟩
  choose f hf hfb using hex
  let C := {g ∈ realStateSpace A | δ ≤ g ⟨b,hb.isSelfAdjoint⟩}
  have hC : IsCompact C := (realStateSpace_isCompact A).inter_right
    (isClosed_le continuous_const (WeakDual.eval_continuous _))
  have hfC : ∀ᶠ e in L,f e ∈ C := by
    filter_upwards [hgood] with e he
    exact ⟨hf e,(hfb e he).1⟩
  obtain ⟨g,hg,hcluster⟩ := hC.exists_mapClusterPt (u := f) (f := L) (le_principal_iff.mpr hfC)
  refine ⟨g,⟨hg.1,?_⟩,hδ.trans_le hg.2⟩
  intro x hx a
  let c : A := x*a
  have hcI : c ∈ I := hIR x hx a
  let cI : I := ⟨c,hcI⟩
  have ht : Tendsto (fun e : I => c*(e : A)) L (𝓝 c) :=
    (continuous_subtype_val.tendsto cI).comp (hL.tendsto_mul_left cI)
  have hzero : Tendsto (fun e : I => (‖b‖/δ)*‖c*(1-(e : A))‖^2) L (𝓝 0) := by
    have hh := (((tendsto_const_nhds : Tendsto (fun _ : I => c) L (𝓝 c)).sub ht).norm.pow 2).const_mul (‖b‖/δ)
    simpa only [mul_sub,mul_one,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] using hh
  let q : selfAdjoint A := ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩
  have htq : Tendsto (fun e : I => f e q) L (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun e => realState_nonneg (hf e) (star_mul_self_nonneg c))) _ hzero
    filter_upwards [hgood] with e he
    exact (hfb e he).2 c
  have hcq : MapClusterPt (g q) L (fun e => f e q) :=
    hcluster.continuousAt_comp (WeakDual.eval_continuous q).continuousAt
  exact eq_of_nhds_neBot (hcq.clusterPt.mono htq)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PrimitiveIdealTest
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped Topology ComplexOrder InnerProductSpace CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationClosedIdeal_isClosed (I : NonUnitalStarSubalgebra ℂ A)
    (hI : IsClosed (I : Set A)) : IsClosed (unitizationClosedIdeal I : Set (Unitization ℂ A)) :=
  (isClosed_eq Unitization.continuous_fst continuous_const).inter
    (hI.preimage Unitization.continuous_snd)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationClosedIdeal_mul_left (I : NonUnitalStarSubalgebra ℂ A)
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) {x : Unitization ℂ A}
    (hx : x ∈ unitizationClosedIdeal I) (a : Unitization ℂ A) :
    a*x ∈ unitizationClosedIdeal I := by
  refine ⟨by simp only [Unitization.fst_mul,hx.1,mul_zero],?_⟩
  simp only [Unitization.snd_mul,hx.1,zero_smul,add_zero]
  exact I.add_mem (I.smul_mem a.fst hx.2) (hIL x.snd hx.2 a.snd)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationClosedIdeal_mul_right (I : NonUnitalStarSubalgebra ℂ A)
    (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I) {x : Unitization ℂ A}
    (hx : x ∈ unitizationClosedIdeal I) (a : Unitization ℂ A) :
    x*a ∈ unitizationClosedIdeal I := by
  refine ⟨by simp only [Unitization.fst_mul,hx.1,zero_mul],?_⟩
  simp only [Unitization.snd_mul,hx.1,zero_smul,zero_add]
  exact I.add_mem (I.smul_mem a.fst hx.2) (hIR x.snd hx.2 a.snd)

theorem exists_irreducible_separating_closed_ideal
    (I : NonUnitalStarSubalgebra ℂ A) (hI : IsClosed (I : Set A))
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I)
    {b : A} (hb : 0 ≤ b) (hbI : b ∉ I) :
    ∃ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π ∧ (∀ x ∈ I,π x=0) ∧ π b ≠ 0 := by
  let J := unitizationClosedIdeal I
  let u : Unitization ℂ A := (b : Unitization ℂ A)
  have hu : 0 ≤ u := map_nonneg (Unitization.inrNonUnitalStarAlgHom ℂ A) hb
  have huJ : u ∉ J := fun h => hbI h.2
  obtain ⟨g,hg,hgb⟩ := exists_annihilator_state_of_not_mem J
    (unitizationClosedIdeal_isClosed I hI)
    (fun x hx a => unitizationClosedIdeal_mul_left I hIL hx a)
    (fun x hx a => unitizationClosedIdeal_mul_right I hIR hx a) hu huJ
  obtain ⟨f,hf,hfJ,hgf⟩ := exists_extreme_annihilator_state hg ⟨u,hu.isSelfAdjoint⟩
  let Φ := realStateComplexification f hf.1
  let π := Φ.gnsStarAlgHom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let H : ComplexHilbert.{u} := { Carrier := Φ.GNS }
  refine ⟨H,π,irreducible_restrict_unitization Φ.gnsStarAlgHom
    (extreme_real_state_gns_irreducible f hf),?_,?_⟩
  · intro x hx
    exact annihilatorStates_gns_zero hfJ (show (x : Unitization ℂ A) ∈ J from ⟨rfl,hx⟩)
  · intro hz
    have he := DFunLike.congr_fun (gns_vectorFunctional_eq f hf.1) ⟨u,hu.isSelfAdjoint⟩
    change (inner ℂ (gnsCyclicVector Φ) (Φ.gnsStarAlgHom u (gnsCyclicVector Φ))).re =
      f ⟨u,hu.isSelfAdjoint⟩ at he
    change Φ.gnsStarAlgHom u=0 at hz
    rw [hz,zero_apply,inner_zero_right,Complex.zero_re] at he
    linarith

theorem mem_closed_ideal_of_irreducible_test
    (I : NonUnitalStarSubalgebra ℂ A) (hI : IsClosed (I : Set A))
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I)
    {b : A} (hb : 0 ≤ b)
    (htest : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → (∀ x ∈ I,π x=0) → π b=0) : b ∈ I := by
  by_contra hn
  obtain ⟨H,π,hπ,hπI,hπb⟩ := exists_irreducible_separating_closed_ideal I hI hIL hIR hb hn
  exact hπb (htest H π hπ hπI)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FinalAssembly
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.contractionEvaluation_generator _root_.OAI.WeakPureInfiniteness.contractionEvaluation_smul _root_.OAI.WeakPureInfiniteness.contractionEvaluation_star _root_.OAI.WeakPureInfiniteness.contractionEvaluation_word _root_.OAI.WeakPureInfiniteness.fullGroupEvaluation_element _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
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

open scoped Topology CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma elementCuntz_of_primitive_support
    (hpi : ∀ x : A,0 ≤ x → ProperlyInfinite (diagonalCopies 1 x))
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupp : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → π a ≠ 0 → π b ≠ 0) :
    ElementCuntzSubequiv a b := by
  apply generatedClosedIdeal_copies_cuntz hb ha (by norm_num : 1 ≤ 1) (hpi b hb) (k := 1)
  apply mem_closed_ideal_of_irreducible_test (generatedClosedIdeal b hb.isSelfAdjoint)
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _)
    (fun x hx c => generatedClosedIdeal_mul_left b c hb.isSelfAdjoint hx)
    (fun x hx c => generatedClosedIdeal_mul_right b c hb.isSelfAdjoint hx) ha
  intro H π hπ hI
  by_contra hn
  exact hsupp H π hπ hn (hI b (self_mem_generatedClosedIdeal b hb))

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationCores
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

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma columnCoreFunction_zero {τ : ℝ} (hτ : 0 ≤ τ) : columnCoreFunction τ 0=0 := by
  simp only [columnCoreFunction,Real.sqrt_zero,zero_sub]
  exact max_eq_right (neg_nonpos.mpr hτ)

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationScalar
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

lemma continuous_separationG (l : ℝ) : Continuous (separationG l) :=
  (continuous_spectralRamp l).comp Real.continuous_sqrt

lemma continuous_separationN (l : ℝ) : Continuous (separationN l) :=
  (continuous_spectralRamp (4*l)).comp Real.continuous_sqrt

lemma separationG_zero {l : ℝ} (hl : 0 < l) : separationG l 0=0 := by
  exact spectralRamp_eq_zero hl (by simpa using hl.le)

lemma separationN_zero {l : ℝ} (hl : 0 < l) : separationN l 0=0 := by
  exact spectralRamp_eq_zero (by positivity) (by simpa using (show 0 ≤ 4*l by positivity))

lemma separationGN {l : ℝ} (hl : 0 < l) (s : ℝ) :
    separationG l s*separationN l s=separationN l s := by
  by_cases h : Real.sqrt s ≤ 4*l
  · rw [show separationN l s=0 from spectralRamp_eq_zero (by positivity) h,mul_zero]
  · rw [show separationG l s=1 from spectralRamp_eq_one hl (by linarith [lt_of_not_ge h]),one_mul]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationCoreSelection
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

universe u v

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma map_column_core_norm (π : A →⋆ₙₐ[ℂ] B) (D : A) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖π (cfcₙ (columnCoreFunction τ) (star D*D))‖=max (‖π D‖-τ) 0 := by
  rw [π.map_cfcₙ (columnCoreFunction τ) (star D*D)
    (continuous_columnCoreFunction τ).continuousOn (columnCoreFunction_zero hτ)
    (by fun_prop) (IsSelfAdjoint.star_mul_self D)
    ((IsSelfAdjoint.star_mul_self D).map π)]
  rw [map_mul,map_star,cfcₙ_eq_cfc (continuous_columnCoreFunction τ).continuousOn (columnCoreFunction_zero hτ)]
  exact norm_column_core _ hτ

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationCoverage
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

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma separationN_eq_zero_of_norm_le (X : B) {l : ℝ} (hl : 0 < l) (hX : ‖X‖ ≤ 4*l) :
    cfc (separationN l) (star X*X)=0 := by
  nontriviality B
  rw [← cfc_zero ℝ (star X*X)]
  apply cfc_congr
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  have hn : s ≤ ‖X‖^2 := by
    have h := spectrum.norm_le_norm_of_mem hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg hs0,CStarRing.norm_star_mul_self,pow_two] using h
  exact spectralRamp_eq_zero (by positivity) (by nlinarith [Real.sq_sqrt hs0,Real.sqrt_nonneg s,norm_nonneg X])

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationSupport
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

universe u v

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_separationN (π : A →⋆ₙₐ[ℂ] B) (X : A) {l : ℝ} (hl : 0 < l) :
    π (cfcₙ (separationN l) (star X*X))=cfc (separationN l) (star (π X)*π X) := by
  rw [π.map_cfcₙ (separationN l) (star X*X) (continuous_separationN l).continuousOn
    (separationN_zero hl) (by fun_prop) (IsSelfAdjoint.star_mul_self X) ((IsSelfAdjoint.star_mul_self X).map π),
    map_mul,map_star,cfcₙ_eq_cfc (continuous_separationN l).continuousOn (separationN_zero hl)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonunital_separationGN (X : A) {l : ℝ} (hl : 0 < l) :
    cfcₙ (separationG l) (star X*X)*cfcₙ (separationN l) (star X*X)=
      cfcₙ (separationN l) (star X*X) := by
  rw [← cfcₙ_mul _ _ _ (continuous_separationG l).continuousOn (separationG_zero hl)
    (continuous_separationN l).continuousOn (separationN_zero hl)]
  exact cfcₙ_congr (fun s _ => separationGN hl s)

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonunital_norm_separationN (X : A) (l : ℝ) :
    ‖cfcₙ (separationN l) (star X*X)‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro s _
  change ‖spectralRamp (4*l) (Real.sqrt s)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg _ _)]
  exact spectralRamp_le_one _ _

lemma separation_core_comparisons_oai
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    (X C k : A) (hk : 0 ≤ k) {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ)
    (hkdet : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),4*l ≤ ‖π X‖ → π k ≠ 0) :
    let g := cfcₙ (separationG l) (star X*X)
    let N := cfcₙ (separationN l) (star X*X)
    let h := cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g))
    let d := cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N))
    ElementCuntzSubequiv d h ∧ ElementCuntzSubequiv d k := by
  dsimp only
  let g := cfcₙ (separationG l) (star X*X)
  let N := cfcₙ (separationN l) (star X*X)
  let h := cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g))
  let d := cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N))
  have hh : 0 ≤ h := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  have hd : 0 ≤ d := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  have hnlt (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπd : π d ≠ 0) :
      2*τ < ‖π (C*N)‖ := by
    have hn := norm_pos_iff.mpr hπd
    rw [show d=cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N)) from rfl,
      map_column_core_norm π (C*N) (by positivity)] at hn
    exact sub_pos.mp ((lt_max_iff.mp hn).resolve_right (lt_irrefl 0))
  constructor
  · apply elementCuntz_of_primitive_support hpi hd hh
    intro H π _ hπd
    have hlt := hnlt H π hπd
    have hn : ‖π (C*N)‖ ≤ ‖π (C*g)‖ := by
      have he : C*N=(C*g)*N := by rw [mul_assoc,nonunital_separationGN X hl]
      rw [he,map_mul]
      have hN : ‖π N‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le π _).trans (nonunital_norm_separationN X l)
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (π (C*g))])
    apply norm_pos_iff.mp
    rw [show h=cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g)) from rfl,
      map_column_core_norm π (C*g) hτ.le]
    exact lt_of_lt_of_le (by linarith : 0 < ‖π (C*g)‖-τ) (le_max_left _ _)
  · apply elementCuntz_of_primitive_support hpi hd hk
    intro H π _ hπd
    apply hkdet H π
    by_contra hn
    have hN : π N=0 := by
      rw [show N=cfcₙ (separationN l) (star X*X) from rfl,map_separationN π X hl]
      exact separationN_eq_zero_of_norm_le _ hl (le_of_lt (lt_of_not_ge hn))
    have hnlt' := hnlt H π hπd
    rw [map_mul,hN,mul_zero,norm_zero] at hnlt'
    linarith

end

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u} : type_of% @OAI.WeakPureInfiniteness.separation_core_comparisons_oai.{u} := @OAI.WeakPureInfiniteness.separation_core_comparisons_oai.{u}
