-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.exists_finite_coupling_of_gap_any
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:09.245429+00:00
-- url     : https://prove2.me/submissions/ab822135-4e18-4f4c-87e7-53d472b383c5

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_separated_supported_model_any

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
lemma principalRightMap_dense (a : A) : DenseRange (principalRightMap a) := by
  have h : DenseRange (Set.inclusion (show Set.range (fun b : A => a*b) ⊆
      closure (Set.range (fun b : A => a*b)) from subset_closure) ∘
      Set.rangeFactorization (fun b : A => a*b)) :=
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  exact h

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

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularCStar
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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


open scoped CStarAlgebra InnerProductSpace NNReal

open CStarMatrix CStarModule ContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [Fintype k] in
lemma rectangular_toCLM_mul (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    toCLM (M*N) = (toCLM N).comp (toCLM M) := by
  ext v i
  simp only [toCLM_apply, comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v M N).symm i

lemma rectangular_norm_mul_le (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    ‖M*N‖ ≤ ‖M‖*‖N‖ := by
  rw [CStarMatrix.norm_def, rectangular_toCLM_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

lemma rectangular_norm_conjTranspose_le (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  apply CStarMatrix.norm_le_of_forall_inner_le (C := ‖M‖₊)
  intro v w
  refine (congrArg (fun a : A => ‖a‖)
    (inner_toCLM_conjTranspose_right (M := M) (v := w) (w := v))).trans_le ?_
  calc
    ‖⟪toCLM M w, v⟫_A‖ ≤ ‖toCLM M w‖*‖v‖ := norm_inner_le (WithCStarModule A (n → A))
    _ ≤ (‖M‖*‖w‖)*‖v‖ := by
      gcongr
      exact le_opNorm _ _
    _ = ‖M‖₊*‖v‖*‖w‖ := by simp only [coe_nnnorm] <;> ring

lemma rectangular_norm_conjTranspose (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ := by
  apply le_antisymm (rectangular_norm_conjTranspose_le M)
  simpa only [rectangular_conjTranspose_conjTranspose] using
    rectangular_norm_conjTranspose_le M.conjTranspose

lemma rectangular_norm_sq_le_range (M : CStarMatrix m n A) :
    ‖M‖^2 ≤ ‖M*M.conjTranspose‖ := by
  have hmain : ‖M‖ ≤ Real.sqrt ‖M*M.conjTranspose‖ := by
    change ‖toCLM M‖ ≤ Real.sqrt ‖M*M.conjTranspose‖
    rw [opNorm_le_iff (by positivity)]
    intro v
    rw [norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
    have h₁ : ‖⟪v, (toCLM M.conjTranspose) ((toCLM M) v)⟫_A‖ ≤
        ‖M*M.conjTranspose‖ * ‖v‖^2 := calc
      _ ≤ ‖v‖ * ‖(toCLM M.conjTranspose) ((toCLM M) v)‖ := norm_inner_le (WithCStarModule A (m → A))
      _ ≤ ‖v‖ * (‖(toCLM M.conjTranspose).comp (toCLM M)‖ * ‖v‖) := by
        gcongr
        exact le_opNorm ((toCLM M.conjTranspose).comp (toCLM M)) v
      _ = ‖M*M.conjTranspose‖*‖v‖^2 := by
        rw [← rectangular_toCLM_mul, ← CStarMatrix.norm_def]
        ring
    conv_rhs => rw [show ‖v‖ = Real.sqrt (‖v‖^2) by simp]
    rw [← Real.sqrt_mul (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h₁
  exact (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp hmain

lemma rectangular_norm_range (M : CStarMatrix m n A) :
    ‖M*M.conjTranspose‖ = ‖M‖^2 := by
  apply le_antisymm _ (rectangular_norm_sq_le_range M)
  simpa only [rectangular_norm_conjTranspose, pow_two] using
    rectangular_norm_mul_le M M.conjTranspose

lemma rectangular_norm_initial (M : CStarMatrix m n A) :
    ‖M.conjTranspose*M‖ = ‖M‖^2 := by
  simpa only [rectangular_conjTranspose_conjTranspose, rectangular_norm_conjTranspose] using
    rectangular_norm_range M.conjTranspose

lemma rectangular_initial_nonneg (M : CStarMatrix m n A) : 0 ≤ M.conjTranspose*M := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have : M.conjTranspose*M = 0 := by ext i j; exact hn.false i |>.elim
    rw [this]
  | inr hn =>
    let i₀ : n := Classical.choice hn
    let R (i : m) : CStarMatrix n n A := fun j k => if j = i₀ then M i k else 0
    have hrows (T : m → n → A) :
        Matrix.conjTranspose (Matrix.of T) * Matrix.of T = ∑ i : m,
          Matrix.conjTranspose (Matrix.of (fun j k : n => if j = i₀ then T i k else 0)) *
            Matrix.of (fun j k : n => if j = i₀ then T i k else 0) := by
      ext j k
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.of_apply]
      simp
    have he : M.conjTranspose*M = ∑ i : m, star (R i)*R i :=
      hrows (Matrix.of.symm (CStarMatrix.ofMatrix.symm M))
    rw [he]
    exact Finset.sum_nonneg (fun i _ => star_mul_self_nonneg (R i))


end WeakPureInfiniteness

end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularPolar
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

section RectangularPolar

open scoped Topology CStarAlgebra

open Filter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] [Fintype k] in
lemma rectangular_continuous_conjTranspose :
    Continuous (fun M : CStarMatrix m n A => M.conjTranspose) := by
  change Continuous (fun M : Matrix m n A => M.conjTranspose)
  fun_prop

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype k] in
lemma rectangular_continuous_mul :
    Continuous (fun p : CStarMatrix m n A × CStarMatrix n k A => p.1*p.2) := by
  change Continuous (fun p : Matrix m n A × Matrix n k A => p.1*p.2)
  fun_prop

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_initial_mul (u : CStarMatrix m n A) (b : CStarMatrix n n A) :
    (u*b).conjTranspose*(u*b) = star b*(u.conjTranspose*u)*b := by
  rw [rectangular_star_mul]
  simp only [rectangular_mul_assoc, CStarMatrix.star_eq_conjTranspose]

attribute [local instance] OAI.WeakPureInfiniteness.matrixRealModule
lemma rectangular_norm_mul_sqrt (u : CStarMatrix m n A) (b : CStarMatrix n n A) :
    ‖CFC.sqrt (u.conjTranspose*u)*b‖ = ‖u*b‖ := by
  have heq : star (CFC.sqrt (u.conjTranspose*u)*b)*(CFC.sqrt (u.conjTranspose*u)*b) =
      (u*b).conjTranspose*(u*b) := by
    rw [rectangular_initial_mul, star_mul, (CFC.sqrt_nonneg (u.conjTranspose*u)).star_eq]
    calc
      star b * CFC.sqrt (u.conjTranspose * u) * (CFC.sqrt (u.conjTranspose * u) * b) =
          star b * (CFC.sqrt (u.conjTranspose * u) * CFC.sqrt (u.conjTranspose * u)) * b := by
        noncomm_ring
      _ = star b*(u.conjTranspose*u)*b := by
        rw [CFC.sqrt_mul_sqrt_self _ (rectangular_initial_nonneg u)]
  have hn := congrArg norm heq
  rw [CStarRing.norm_star_mul_self, rectangular_norm_initial] at hn
  nlinarith [norm_nonneg (CFC.sqrt (u.conjTranspose*u)*b), norm_nonneg (u*b)]

lemma rectangularPolar_apply_mul (u : CStarMatrix m n A) (b : CStarMatrix n n A) :
    rectangularPolar u (principalRightMap (CFC.sqrt (u.conjTranspose*u)) b) = u*b := by
  apply LinearMap.extendOfNorm_eq (principalRightMap_dense _)
  refine ⟨1, fun c => ?_⟩
  change ‖u*c‖ ≤ 1*‖CFC.sqrt (u.conjTranspose*u)*c‖
  rw [one_mul, rectangular_norm_mul_sqrt]

lemma rectangularPolar_initial_square (u : CStarMatrix m n A)
    (a : principalRightIdeal (CFC.sqrt (u.conjTranspose*u))) :
    (rectangularPolar u a).conjTranspose*rectangularPolar u a = star (a : CStarMatrix n n A)*(a : CStarMatrix n n A) := by
  refine (principalRightMap_dense (CFC.sqrt (u.conjTranspose*u))).induction_on a ?_ ?_
  · apply isClosed_eq
    · exact rectangular_continuous_mul.comp
        ((rectangular_continuous_conjTranspose.comp (rectangularPolar u).continuous).prodMk
          (rectangularPolar u).continuous)
    · fun_prop
  · intro b
    rw [rectangularPolar_apply_mul]
    change (u*b).conjTranspose*(u*b) =
      star (CFC.sqrt (u.conjTranspose*u)*b)*(CFC.sqrt (u.conjTranspose*u)*b)
    rw [rectangular_initial_mul, star_mul, (CFC.sqrt_nonneg (u.conjTranspose*u)).star_eq]
    calc
      star b*(u.conjTranspose*u)*b =
          star b * (CFC.sqrt (u.conjTranspose*u)*CFC.sqrt (u.conjTranspose*u))*b := by
        rw [CFC.sqrt_mul_sqrt_self _ (rectangular_initial_nonneg u)]
      _ = star b*CFC.sqrt (u.conjTranspose*u)*(CFC.sqrt (u.conjTranspose*u)*b) := by
        noncomm_ring

lemma rectangularPolar_mem_rightIdeal (u : CStarMatrix m n A)
    (a : principalRightIdeal (CFC.sqrt (u.conjTranspose*u))) :
    rectangularPolar u a ∈ rectangularRightIdeal u := by
  refine (principalRightMap_dense (CFC.sqrt (u.conjTranspose*u))).induction_on a ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (rectangularPolar u).continuous
  · intro b
    rw [rectangularPolar_apply_mul]
    exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ b)

lemma rectangular_exact_initial_of_domination (u : CStarMatrix m n A)
    (d : CStarMatrix n n A) (hd : 0 ≤ d) {c : ℝ} (hc : 0 ≤ c)
    (hdu : d ≤ c • (u.conjTranspose*u)) :
    ∃ r : CStarMatrix m n A, r.conjTranspose*r = d ∧ r ∈ rectangularRightIdeal u := by
  let a := CFC.sqrt d
  have ha : a*star a = d := by
    dsimp only [a]
    rw [(CFC.sqrt_nonneg d).star_eq, CFC.sqrt_mul_sqrt_self d hd]
  have hamem : a ∈ principalRightIdeal (CFC.sqrt (u.conjTranspose*u)) := by
    rw [principalRightIdeal_sqrt _ (rectangular_initial_nonneg u)]
    exact principalRightIdeal_of_square_le_smul _ a
      (rectangular_initial_nonneg u) hc (by rwa [ha])
  let a₀ : principalRightIdeal (CFC.sqrt (u.conjTranspose*u)) := ⟨a, hamem⟩
  refine ⟨rectangularPolar u a₀, ?_, rectangularPolar_mem_rightIdeal u a₀⟩
  rw [rectangularPolar_initial_square]
  change star a*a = d
  rw [show star a = a from (CFC.sqrt_nonneg d).star_eq]
  exact CFC.sqrt_mul_sqrt_self d hd

end RectangularPolar

section RectangularHereditary

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n : Type*} [Fintype m] [Fintype n]

omit [PartialOrder A] [StarOrderedRing A] in
lemma rightIdeal_sandwich_mem_hereditary (h a b : A) (hh : IsSelfAdjoint h)
    (ha : a ∈ principalRightIdeal h) : a*b*star a ∈ hereditarySubalgebra h hh := by
  have hc : IsClosed {a : A | a*b*star a ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc ha
  rintro _ ⟨y, rfl⟩
  change (h*y)*b*star (h*y) ∈ hereditarySubalgebra h hh
  rw [star_mul, hh.star_eq]
  have he : (h*y)*b*(star y*h) = h*(y*b*star y)*h := by noncomm_ring
  rw [he]
  exact sandwich_mem h _ hh

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_range_mul (a : CStarMatrix m m A) (V : CStarMatrix m n A) :
    (a*V)*(a*V).conjTranspose = a*(V*V.conjTranspose)*star a := by
  rw [rectangular_star_mul]
  simp only [rectangular_mul_assoc, CStarMatrix.star_eq_conjTranspose]

lemma rectangularRightIdeal_range_mem_hereditary (h a : CStarMatrix m m A)
    (V : CStarMatrix m n A) (hh : IsSelfAdjoint h) (ha : a ∈ principalRightIdeal h)
    (r : CStarMatrix m n A) (hr : r ∈ rectangularRightIdeal (a*V)) :
    r*r.conjTranspose ∈ hereditarySubalgebra h hh := by
  have hcont : Continuous (fun r : CStarMatrix m n A => r*r.conjTranspose) :=
    rectangular_continuous_mul.comp (continuous_id.prodMk rectangular_continuous_conjTranspose)
  have hc : IsClosed {r : CStarMatrix m n A | r*r.conjTranspose ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage hcont
  apply closure_minimal _ hc hr
  rintro _ ⟨b, rfl⟩
  change ((a*V)*b)*((a*V)*b).conjTranspose ∈ hereditarySubalgebra h hh
  rw [rectangular_mul_assoc a V b, rectangular_range_mul]
  exact rightIdeal_sandwich_mem_hereditary h a _ hh ha

attribute [local instance] OAI.WeakPureInfiniteness.matrixRealModule
lemma rectangular_exact_initial_hereditary (h : CStarMatrix m m A)
    (V : CStarMatrix m n A) (d : CStarMatrix n n A) (hh : 0 ≤ h) (hd : 0 ≤ d)
    {c : ℝ} (hc : 0 ≤ c)
    (hdu : d ≤ c • ((CFC.sqrt h*V).conjTranspose*(CFC.sqrt h*V))) :
    ∃ r : CStarMatrix m n A, r.conjTranspose*r = d ∧
      r*r.conjTranspose ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  obtain ⟨r, hr, hrmem⟩ := rectangular_exact_initial_of_domination (CFC.sqrt h*V) d hd hc hdu
  refine ⟨r, hr, rectangularRightIdeal_range_mem_hereditary h (CFC.sqrt h) V
    hh.isSelfAdjoint ?_ r hrmem⟩
  exact hereditary_le_rightIdeal h hh.isSelfAdjoint
    (sqrt_mem_hereditary h h hh.isSelfAdjoint (self_mem_hereditary h hh) hh)

end RectangularHereditary

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralCut
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

lemma spectralRamp_coercive {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    θ*(spectralRamp θ s*spectralRamp θ s) ≤ spectralRamp θ s*s*spectralRamp θ s := by
  by_cases hs : s ≤ θ
  · rw [spectralRamp_eq_zero hθ hs]
    simp
  · have h : θ ≤ s := le_of_lt (lt_of_not_ge hs)
    nlinarith [mul_le_mul_of_nonneg_right h (mul_self_nonneg (spectralRamp θ s))]

lemma spectralRamp_dominates {θ L : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L)
    (f : ℝ → ℝ) (hzero : ∀ s, s ≤ 2*θ → f s = 0)
    (hbound : ∀ s, f s ≤ L) (s : ℝ) :
    f s ≤ L*(spectralRamp θ s*spectralRamp θ s) := by
  by_cases hs : s ≤ 2*θ
  · rw [hzero s hs]
    exact mul_nonneg hL (mul_self_nonneg _)
  · rw [spectralRamp_eq_one hθ (le_of_lt (lt_of_not_ge hs)), one_mul, mul_one]
    exact hbound s

section Algebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma conjugate_perturbation_lower (x y z : A) (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) (hz : IsSelfAdjoint z) {δ : ℝ}
    (hclose : ‖x-y‖ ≤ δ) : z*x*z - δ • (z*z) ≤ z*y*z := by
  have hsq : 0 ≤ z*z := by simpa only [hz.star_eq] using star_mul_self_nonneg z
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul (a := z) (b := x - y) (hx.sub hy)
  rw [hz.star_eq] at h
  have h' : z*(x-y)*z ≤ δ • (z*z) := h.trans (smul_le_smul_of_nonneg_right hclose hsq)
  have he : z*(x-y)*z = z*x*z-z*y*z := by noncomm_ring
  rw [he] at h'
  exact sub_le_iff_le_add.mpr ((sub_le_iff_le_add.mp h').trans_eq (add_comm _ _))

lemma spectralRamp_algebra_coercive (x : A) (hx : 0 ≤ x) {θ : ℝ} (hθ : 0 < θ) :
    θ • (cfcₙ (spectralRamp θ) x*cfcₙ (spectralRamp θ) x) ≤
      cfcₙ (spectralRamp θ) x*x*cfcₙ (spectralRamp θ) x := by
  have hg := (continuous_spectralRamp θ).continuousOn (s := quasispectrum ℝ x)
  have hg0 : spectralRamp θ 0 = 0 := spectralRamp_eq_zero hθ hθ.le
  have hm := cfcₙ_mono (a := x) (fun s _ => spectralRamp_coercive hθ s)
    (by fun_prop) (by fun_prop) (by simp [hg0]) (by simp [hg0])
  rw [cfcₙ_const_mul θ (fun s => spectralRamp θ s*spectralRamp θ s) x
      (by fun_prop) (by simp [hg0]),
    cfcₙ_mul (spectralRamp θ) (spectralRamp θ) x hg hg0 hg hg0,
    cfcₙ_mul (fun s => spectralRamp θ s*s) (spectralRamp θ) x
      (by fun_prop) (by simp [hg0]) hg hg0,
    cfcₙ_mul (spectralRamp θ) (fun s : ℝ => s) x hg hg0 continuousOn_id rfl,
    cfcₙ_id' ℝ x hx.isSelfAdjoint] at hm
  exact hm

lemma spectralRamp_algebra_dominates (x : A) {θ L : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0)
    (hzero : ∀ s, s ≤ 2*θ → f s = 0) (hbound : ∀ s, f s ≤ L) :
    cfcₙ f x ≤ L • (cfcₙ (spectralRamp θ) x*cfcₙ (spectralRamp θ) x) := by
  have hg := (continuous_spectralRamp θ).continuousOn (s := quasispectrum ℝ x)
  have hg0 : spectralRamp θ 0 = 0 := spectralRamp_eq_zero hθ hθ.le
  have hm := cfcₙ_mono (a := x) (fun s _ => spectralRamp_dominates hθ hL f hzero hbound s)
    hf.continuousOn (by fun_prop) hf0 (by simp [hg0])
  rw [cfcₙ_const_mul L (fun s => spectralRamp θ s*spectralRamp θ s) x
      (by fun_prop) (by simp [hg0]),
    cfcₙ_mul (spectralRamp θ) (spectralRamp θ) x hg hg0 hg hg0] at hm
  exact hm

lemma spectralRamp_domination (x y : A) (hx : 0 ≤ x) (hy : 0 ≤ y)
    {θ L : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L) (hclose : ‖y-x‖ ≤ θ/2)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0)
    (hzero : ∀ s, s ≤ 2*θ → f s = 0) (hbound : ∀ s, f s ≤ L) :
    cfcₙ f x ≤ (2*L/θ) • (cfcₙ (spectralRamp θ) x*y*cfcₙ (spectralRamp θ) x) := by
  let z := cfcₙ (spectralRamp θ) x
  have hz : 0 ≤ z := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg θ s)
  have hclose' : ‖x-y‖ ≤ θ/2 := by rwa [norm_sub_rev]
  have hp := conjugate_perturbation_lower x y z hx.isSelfAdjoint hy.isSelfAdjoint hz.isSelfAdjoint hclose'
  have hp' : (θ/2) • (z*z) ≤ z*y*z := by
    have hco : θ • (z*z) ≤ z*x*z := spectralRamp_algebra_coercive x hx hθ
    calc
      (θ/2) • (z*z) = θ • (z*z) - (θ/2) • (z*z) := by
        rw [← sub_smul]; congr 1; ring
      _ ≤ z*x*z - (θ/2) • (z*z) := sub_le_sub_right hco _
      _ ≤ z*y*z := hp
  have hc : 0 ≤ 2*L/θ := by positivity
  calc
    cfcₙ f x ≤ L • (z*z) := spectralRamp_algebra_dominates x hθ hL f hf hf0 hzero hbound
    _ = (2*L/θ) • ((θ/2) • (z*z)) := by
      rw [smul_smul]
      congr 1
      field_simp
    _ ≤ (2*L/θ) • (z*y*z) := smul_le_smul_of_nonneg_left hp' hc

end Algebra

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CutImplementation
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

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n : Type*} [Fintype m] [Fintype n]

attribute [local instance] OAI.WeakPureInfiniteness.matrixRealModuleCut
omit [Fintype n] in
lemma rectangular_sqrt_initial (h : CStarMatrix m m A) (V : CStarMatrix m n A)
    (hh : 0 ≤ h) :
    (CFC.sqrt h*V).conjTranspose*(CFC.sqrt h*V) = V.conjTranspose*h*V := by
  rw [rectangular_star_mul, ← CStarMatrix.star_eq_conjTranspose,
    (CFC.sqrt_nonneg h).star_eq]
  calc
    (V.conjTranspose*CFC.sqrt h)*(CFC.sqrt h*V) =
        V.conjTranspose*(CFC.sqrt h*CFC.sqrt h)*V := by
      simp only [rectangular_mul_assoc]
    _ = V.conjTranspose*h*V := by rw [CFC.sqrt_mul_sqrt_self h hh]

lemma rectangular_sandwich_nonneg (h : CStarMatrix m m A) (V : CStarMatrix m n A)
    (hh : 0 ≤ h) : 0 ≤ V.conjTranspose*h*V := by
  rw [← rectangular_sqrt_initial h V hh]
  exact rectangular_initial_nonneg _

lemma CuntzSubequiv.exact_spectralRamp {x : CStarMatrix n n A}
    {h : CStarMatrix m m A} (hx : 0 ≤ x) (hh : 0 ≤ h) (hxh : CuntzSubequiv x h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : CStarMatrix m n A,
      R.conjTranspose*R = cfcₙ (spectralRamp δ) x ∧
      R*R.conjTranspose ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ ‖R‖ ≤ 1 := by
  let θ := δ/2
  have hθ : 0 < θ := by dsimp only [θ] <;> positivity
  obtain ⟨V, hV⟩ := hxh (θ/2) (by positivity)
  let y := V.conjTranspose*h*V
  let z := cfcₙ (spectralRamp θ) x
  have hz : 0 ≤ z := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg θ s)
  have hd : 0 ≤ cfcₙ (spectralRamp δ) x := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg δ s)
  have hzero : ∀ s, s ≤ 2*θ → spectralRamp δ s = 0 := by
    intro s hs
    apply spectralRamp_eq_zero hδ
    dsimp only [θ] at hs
    linarith
  have hdom : cfcₙ (spectralRamp δ) x ≤ (2*1/θ) • (z*y*z) :=
    spectralRamp_domination x y hx (rectangular_sandwich_nonneg h V hh) hθ zero_le_one hV.le
      (spectralRamp δ) (continuous_spectralRamp δ) (spectralRamp_eq_zero hδ hδ.le)
      hzero (spectralRamp_le_one δ)
  have he : (CFC.sqrt h*(V*z)).conjTranspose*(CFC.sqrt h*(V*z)) = z*y*z := by
    rw [← rectangular_mul_assoc (CFC.sqrt h) V z, rectangular_initial_mul,
      rectangular_sqrt_initial h V hh, hz.star_eq]
  obtain ⟨R, hR, hRher⟩ := rectangular_exact_initial_hereditary h (V*z)
    (cfcₙ (spectralRamp δ) x) hh hd (show 0 ≤ 2*1/θ by positivity) (by rwa [he])
  refine ⟨R, hR, hRher, ?_⟩
  have hn : ‖cfcₙ (spectralRamp δ) x‖ ≤ 1 := by
    apply norm_cfcₙ_le
    intro s _
    rw [Real.norm_eq_abs, abs_of_nonneg (spectralRamp_nonneg δ s)]
    exact spectralRamp_le_one δ s
  rw [← hR, rectangular_norm_initial] at hn
  nlinarith [norm_nonneg R]

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

lemma IsClosedInner.symmetrized_corner_mem {D : NonUnitalStarSubalgebra ℂ A}
    (hD : IsClosedInner D) {p q : A} (hp : p ∈ D) (hq : q ∈ D) (x : A) :
    p*x*q+star (p*x*q) ∈ D :=
  D.add_mem (hD.2 p hp q hq x) (star_mem (s := D) (hD.2 p hp q hq x))

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_MatrixCutToolkit
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

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] OAI.WeakPureInfiniteness.matrixRealModuleToolkit
lemma diagonalCopies_cfc (n : ℕ) (a : A) (ha : IsSelfAdjoint a)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    diagonalCopies n (cfcₙ f a) = cfcₙ f (diagonalCopies n a) :=
  (diagonalHom n).map_cfcₙ f a hf.continuousOn hf0 (by fun_prop) ha (ha.map (diagonalHom n))

omit [PartialOrder A] [StarOrderedRing A] in
lemma left_identity_on_hereditary (e h : A) (hh : IsSelfAdjoint h) (he : e*h=h)
    {x : A} (hx : x ∈ hereditarySubalgebra h hh) : e*x=x := by
  have hclosed : IsClosed {x : A | e*x=x} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal ?_ hclosed hx
  rintro _ ⟨b,rfl⟩
  change e*(h*b*h)=h*b*h
  rw [← mul_assoc, ← mul_assoc, he]

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_sub_mul {m n k : Type*} [Fintype n]
    (u v : CStarMatrix m n A) (w : CStarMatrix n k A) : (u-v)*w=u*w-v*w :=
  Matrix.sub_mul _ _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_mul_sub {m n k : Type*} [Fintype n]
    (u : CStarMatrix m n A) (v w : CStarMatrix n k A) : u*(v-w)=u*v-u*w :=
  Matrix.mul_sub _ _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_star_sub {m n : Type*} (u v : CStarMatrix m n A) :
    (u-v).conjTranspose=u.conjTranspose-v.conjTranspose := Matrix.conjTranspose_sub _ _

lemma rectangular_left_identity_of_range {m n : Type*} [Fintype m] [Fintype n]
    (e : CStarMatrix m m A) (u : CStarMatrix m n A)
    (he : e*(u*u.conjTranspose)=u*u.conjTranspose) : e*u=u := by
  let v := e*u-u
  have hvu : v*u.conjTranspose=0 := by
    change (e*u-u)*u.conjTranspose=0
    rw [rectangular_sub_mul, rectangular_mul_assoc, he, sub_self]
  have hv : v*v.conjTranspose=0 := by
    change v*(e*u-u).conjTranspose=0
    rw [rectangular_star_sub, rectangular_star_mul, rectangular_mul_sub,
      ← rectangular_mul_assoc, hvu]
    simp only [sub_zero]
    exact Matrix.zero_mul _
  have hn := rectangular_norm_range v
  rw [hv, norm_zero] at hn
  have hh : ‖v‖=0 := by nlinarith [norm_nonneg v]
  exact sub_eq_zero.mp (norm_eq_zero.mp hh)

lemma rectangular_left_identity_of_hereditary_range {m n : Type*} [Fintype m] [Fintype n]
    (e h : CStarMatrix m m A) (u : CStarMatrix m n A) (hh : IsSelfAdjoint h)
    (he : e*h=h) (hu : u*u.conjTranspose ∈ hereditarySubalgebra h hh) : e*u=u :=
  rectangular_left_identity_of_range e u (left_identity_on_hereditary e h hh he hu)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FixedRows
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

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance matrixRealModuleRows_rdadd45_1 {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _
lemma exists_fixed_comparison_row {n : ℕ} (c h : A) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hch : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h))
    {α : ℝ} (hα : 0 < α) :
    ∃ R : CStarMatrix (Fin 1) (Fin n) A,
      R.conjTranspose*R=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c) ∧
      R*R.conjTranspose∈hereditarySubalgebra (diagonalCopies 1 h)
        (diagonalCopies_nonneg 1 hh).isSelfAdjoint ∧ ‖R‖≤1 := by
  obtain ⟨R,hR,hRh,hRn⟩ := hch.exact_spectralRamp
    (diagonalCopies_nonneg n hc) (diagonalCopies_nonneg 1 hh) (α/4) (by positivity)
  refine ⟨R,?_,hRh,hRn⟩
  rw [hR, diagonalCopies_cfc n c hc.isSelfAdjoint (spectralRamp (α/4))
    (continuous_spectralRamp _) (spectralRamp_eq_zero (by positivity) (by positivity))]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectralRamp_mul_ramp (c : A) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 2*θ ≤ δ) :
    cfcₙ (spectralRamp θ) c*cfcₙ (spectralRamp δ) c=cfcₙ (spectralRamp δ) c := by
  have hd : 0 < δ := lt_of_lt_of_le (by linarith : 0 < 2*θ) hδ
  by_cases hc : IsSelfAdjoint c
  · rw [← cfcₙ_mul (spectralRamp θ) (spectralRamp δ) c
      (continuous_spectralRamp _).continuousOn (spectralRamp_eq_zero hθ (by positivity))
      (continuous_spectralRamp _).continuousOn (spectralRamp_eq_zero hd (by positivity))]
    apply cfcₙ_congr
    intro s hs
    dsimp only
    by_cases hsd : s ≤ δ
    · rw [spectralRamp_eq_zero hd hsd, mul_zero]
    · rw [spectralRamp_eq_one hθ (hδ.trans (le_of_lt (lt_of_not_ge hsd))), one_mul]
  · simp only [cfcₙ_apply_of_not_predicate c hc, mul_zero]

lemma fixed_row_shallow_support {n : ℕ} (c : A)
    {α : ℝ} (hα : 0 < α) (R : CStarMatrix (Fin 1) (Fin n) A)
    (hR : R.conjTranspose*R=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)) :
    diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)*R.conjTranspose=R.conjTranspose := by
  apply rectangular_left_identity_of_range
  rw [rectangular_conjTranspose_conjTranspose, hR]
  change diagonalHom n (cfcₙ (spectralRamp (α/16)) c)*
    diagonalHom n (cfcₙ (spectralRamp (α/4)) c)=diagonalHom n (cfcₙ (spectralRamp (α/4)) c)
  rw [← map_mul, spectralRamp_mul_ramp c (by positivity : 0 < α/16) (by linarith)]

lemma fixed_row_partial_isometry {n : ℕ} (p h : A) (hh : 0 ≤ h)
    (hph : star p*p*h=h) (R : CStarMatrix (Fin 1) (Fin n) A)
    (hR : R*R.conjTranspose∈hereditarySubalgebra (diagonalCopies 1 h)
      (diagonalCopies_nonneg 1 hh).isSelfAdjoint) :
    diagonalCopies 1 (star p*p)*R=R := by
  apply rectangular_left_identity_of_hereditary_range _ _ R
    (diagonalCopies_nonneg 1 hh).isSelfAdjoint _ hR
  change diagonalHom 1 (star p*p)*diagonalHom 1 h=diagonalHom 1 h
  rw [← map_mul, hph]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_MatrixMaps
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

open scoped CStarAlgebra ComplexOrder

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype m] [Fintype k] in
lemma rectangularMap_mul (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    rectangularMap φ (M*N)=rectangularMap φ M*rectangularMap φ N := by
  ext i j
  simp only [rectangularMap_apply, CStarMatrix.mul_apply, map_sum, map_mul]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype m] [Fintype n] in
lemma rectangularMap_star (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) :
    rectangularMap φ M.conjTranspose=(rectangularMap φ M).conjTranspose := by
  ext i j
  simp only [rectangularMap_apply, CStarMatrix.conjTranspose_apply, map_star]

lemma rectangularMap_norm_le (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix m n A) :
    ‖rectangularMap φ M‖ ≤ ‖M‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le (CStarMatrix.mapₙₐ φ) (M.conjTranspose*M)
  change ‖rectangularMap φ (M.conjTranspose*M)‖ ≤ ‖M.conjTranspose*M‖ at h
  rw [rectangularMap_mul, rectangularMap_star, rectangular_norm_initial, rectangular_norm_initial] at h
  nlinarith [norm_nonneg M, norm_nonneg (rectangularMap φ M)]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SupportedCorner
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

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma matrixSingletonHom_injective : Function.Injective (matrixSingletonHom (A := A)) := by
  intro x y h
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  exact h

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PerturbationRows
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

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

omit [PartialOrder A] [StarOrderedRing A] in
lemma diagonal_singleton (X : CStarMatrix (Fin 1) (Fin 1) A) :
    diagonalCopies 1 (matrixSingletonHom X)=X := by
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleton_diagonal (x : A) : matrixSingletonHom (diagonalCopies 1 x)=x := rfl

lemma norm_diagonalCopies_le (m : ℕ) (x : A) : ‖diagonalCopies m x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (diagonalHom m) x

lemma norm_row_test_le (R S : CStarMatrix (Fin 1) (Fin n) A)
    (w : CStarMatrix (Fin n) (Fin n) A) (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖matrixSingletonHom (-(R*w*S.conjTranspose))‖ ≤ 1 := by
  apply (NonUnitalStarAlgHom.norm_apply_le (matrixSingletonHom (A := A)) _).trans
  rw [norm_neg]
  calc
    ‖R*w*S.conjTranspose‖ ≤ (‖R‖*‖w‖)*‖S.conjTranspose‖ :=
      (rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (rectangular_norm_mul_le R w) (norm_nonneg _))
    _ ≤ (1*1)*1 := by rw [rectangular_norm_conjTranspose]; gcongr
    _ = 1 := by norm_num

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_neg_mul_perturb {m k l : Type*} [Fintype k]
    (L : CStarMatrix m k A) (R : CStarMatrix k l A) : (-L)*R=-(L*R) := Matrix.neg_mul L R

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_mul_neg_perturb {m k l : Type*} [Fintype k]
    (L : CStarMatrix m k A) (R : CStarMatrix k l A) : L*(-R)=-(L*R) := Matrix.mul_neg L R

omit [PartialOrder A] [StarOrderedRing A] in
lemma compress_row_test (L : CStarMatrix (Fin n) (Fin 1) A)
    (K R S : CStarMatrix (Fin 1) (Fin n) A)
    (P Q : CStarMatrix (Fin 1) (Fin 1) A) (E w : CStarMatrix (Fin n) (Fin n) A)
    (hL : L*P*R=E) (hK : S.conjTranspose*Q*K=E) (hw : E*w*E=w) :
    L*(P*(-(R*w*S.conjTranspose))*Q)*K= -w := by
  rw [rectangular_mul_neg_perturb, rectangular_neg_mul_perturb,
    rectangular_mul_neg_perturb, rectangular_neg_mul_perturb]
  congr 1
  calc
    L*(P*(R*w*S.conjTranspose)*Q)*K = (L*P*R)*w*(S.conjTranspose*Q*K) := by
      simp only [rectangular_mul_assoc]
    _ = w := by rw [hL,hK,hw]

lemma norm_representation_compression_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (L : CStarMatrix (Fin n) (Fin 1) A) (K : CStarMatrix (Fin 1) (Fin n) A)
    (X : CStarMatrix (Fin 1) (Fin 1) A) (hL : ‖L‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    ‖matrixRepresentation π (Fin n) (L*X*K)‖ ≤ ‖π (matrixSingletonHom X)‖ := by
  have hX : ‖rectangularMap π X‖ = ‖π (matrixSingletonHom X)‖ := by
    have hh := NonUnitalStarAlgHom.norm_map matrixSingletonHom matrixSingletonHom_injective
      (rectangularMap π X)
    exact hh.symm
  calc
    _ ≤ ‖rectangularMap π (L*X*K)‖ := NonUnitalStarAlgHom.norm_apply_le (matrixActionHom (n := Fin n) (H := H)) (rectangularMap π (L*X*K))
    _ = ‖rectangularMap π L*rectangularMap π X*rectangularMap π K‖ := by rw [rectangularMap_mul, rectangularMap_mul]
    _ ≤ ‖rectangularMap π L‖*‖rectangularMap π X‖*‖rectangularMap π K‖ :=
      (rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (rectangular_norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*‖π (matrixSingletonHom X)‖*1 := by
      rw [hX]
      gcongr
      · exact (rectangularMap_norm_le π L).trans hL
      · exact (rectangularMap_norm_le π K).trans hK
    _ = ‖π (matrixSingletonHom X)‖ := by ring

lemma supported_testing_element (c : A) {α : ℝ} (hα : 0 < α)
    (R S : CStarMatrix (Fin 1) (Fin n) A)
    (hR : R.conjTranspose*R=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c))
    (hS : S.conjTranspose*S=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c))
    (X : CStarMatrix (Fin 1) (Fin 1) A) (z : ℂ) :
    let e := diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)
    e*(z • (R.conjTranspose*X*S))=z • (R.conjTranspose*X*S) ∧
      (z • (R.conjTranspose*X*S))*e=z • (R.conjTranspose*X*S) := by
  dsimp only
  have hl := fixed_row_shallow_support c hα R hR
  have hr := congrArg CStarMatrix.conjTranspose (fixed_row_shallow_support c hα S hS)
  have he : IsSelfAdjoint (diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)) := by
    exact (cfcₙ_predicate (spectralRamp (α/16)) c).map (diagonalHom n)
  rw [rectangular_star_mul, rectangular_conjTranspose_conjTranspose] at hr
  change S*star (diagonalCopies n (cfcₙ (spectralRamp (α/16)) c))=S at hr
  rw [he.star_eq] at hr
  constructor
  · rw [mul_smul_comm, ← rectangular_mul_assoc, ← rectangular_mul_assoc, hl]
  · rw [smul_mul_assoc, rectangular_mul_assoc, hr]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_OrthogonalPerturbation
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

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma norm_selfadjoint_of_square_zero (x : A) (hx : x*x=0) :
    ‖x+star x‖=‖x‖ := by
  have hxs : star x*star x=0 := by
    simpa only [star_mul,star_zero] using congrArg star hx
  have hsa : IsSelfAdjoint (x+star x) := by
    show star (x+star x)=x+star x
    rw [star_add,star_star,add_comm]
  have horth : (star x*x)*(x*star x)=0 := by
    calc
      (star x*x)*(x*star x)=star x*(x*x)*star x := by noncomm_ring
      _ = 0 := by rw [hx,mul_zero,zero_mul]
  have hsum : (x+star x)*(x+star x)=star x*x+x*star x := by
    noncomm_ring [hx,hxs]
  have hn := (CStarRing.norm_star_mul_self (x := x+star x))
  rw [hsa.star_eq] at hn
  rw [hsum] at hn
  rw [(IsSelfAdjoint.star_mul_self x).norm_add_eq_max
    (IsSelfAdjoint.mul_star_self x) horth] at hn
  rw [CStarRing.norm_star_mul_self,CStarRing.norm_self_mul_star,max_self] at hn
  nlinarith [norm_nonneg (x+star x),norm_nonneg x]

lemma isSelfAdjoint_add_star (x : A) : IsSelfAdjoint (x+star x) := by
  show star (x+star x)=x+star x
  rw [star_add,star_star,add_comm]

variable [PartialOrder A] [StarOrderedRing A]

lemma orthogonal_selfadjoint_test (p q y : A) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p*q=0) (hpn : ‖p‖ ≤ 1) (hqn : ‖q‖ ≤ 1) (hyn : ‖y‖ ≤ 1) :
    ‖p*y*q+star (p*y*q)‖ ≤ 1 ∧
      p*(p*y*q+star (p*y*q))*q=(p*p)*y*(q*q) := by
  have hqp : q*p=0 := by
    simpa only [star_mul,hp.star_eq,hq.star_eq,star_zero] using congrArg star hpq
  have hz : (p*y*q)*(p*y*q)=0 := by
    calc
      (p*y*q)*(p*y*q)=p*y*(q*p)*y*q := by noncomm_ring
      _ = 0 := by rw [hqp,mul_zero,zero_mul,zero_mul]
  constructor
  · rw [norm_selfadjoint_of_square_zero _ hz]
    calc
      ‖p*y*q‖ ≤ (‖p‖*‖y‖)*‖q‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*1)*1 := by gcongr
      _ = 1 := by norm_num
  · have hc : p*star (p*y*q)*q=0 := by
      rw [star_mul,star_mul,hp.star_eq,hq.star_eq]
      calc
        p*(q*(star y*p))*q=(p*q)*star y*(p*q) := by noncomm_ring
        _ = 0 := by rw [hpq,zero_mul,zero_mul]
    rw [mul_add,add_mul,hc,add_zero]
    noncomm_ring

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteCoupling
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

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_corner_le_one (p q y : A) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖p*y*q‖ ≤ 1 := by
  calc
    ‖p*y*q‖ ≤ (‖p‖*‖y‖)*‖q‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*1)*1 := by gcongr
    _ = 1 := by norm_num

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_add_smul (p q U y : A) (z : ℂ) :
    p*(U+z • y)*q=p*U*q+z • (p*y*q) := by
  rw [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversePerturbation
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

open scoped CStarAlgebra ComplexOrder

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem uniform_perturbation_of_gap_any
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (p q h k c : A) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hph : star p*p*h=h) (hqk : q*star q*k=k)
    (hch : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h))
    (hck : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k))
    (T : A) {η α : ℝ} (hη : 0 < η) (hα : 0 < α) :
    ∃ y : A, ‖y‖ ≤ 1 ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖ := by
  obtain ⟨R,hR,hRh,hRn⟩ := exists_fixed_comparison_row c h hc hh hch hα
  obtain ⟨S,hS,hSk,hSn⟩ := exists_fixed_comparison_row c k hc hk hck hα
  obtain ⟨U,hU,_,_⟩ := exists_fixed_comparison_row c h hc hh hch (α := α/4) (by positivity)
  let E := diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)
  let e := diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)
  have he : IsSelfAdjoint e := by
    have hcself : IsSelfAdjoint (cfcₙ (spectralRamp (α/16)) c) := cfcₙ_predicate _ _
    exact hcself.map (diagonalHom n)
  have hUe : U.conjTranspose*U=e := by
    have hd : α/4/4=α/16 := by ring
    simpa only [hd] using hU
  let P := diagonalCopies 1 p
  let Q := diagonalCopies 1 q
  let X := diagonalCopies 1 T
  let L := R.conjTranspose*star P
  let K := star Q*S
  have hPR : star P*P*R=R := by
    change (star (diagonalHom 1 p)*diagonalHom 1 p)*R=R
    rw [← map_star,← map_mul]
    exact fixed_row_partial_isometry p h hh hph R hRh
  have hQS : Q*star Q*S=S := by
    have hhq : star (star q)*star q*k=k := by simpa only [star_star] using hqk
    change diagonalHom 1 q*star (diagonalHom 1 q)*S=S
    rw [← map_star,← map_mul]
    rw [show diagonalHom 1 (q*star q)=diagonalCopies 1 (q*star q) from rfl]
    simpa only [star_star] using fixed_row_partial_isometry (star q) k hk hhq S hSk
  have hLPR : L*P*R=E := by
    dsimp only [L]
    rw [rectangular_mul_assoc, rectangular_mul_assoc, ← rectangular_mul_assoc (star P), hPR]
    exact hR
  have hSQK : S.conjTranspose*Q*K=E := by
    dsimp only [K]
    rw [rectangular_mul_assoc, ← rectangular_mul_assoc Q, hQS]
    exact hS
  have hLn : ‖L‖ ≤ 1 := by
    calc
      ‖L‖ ≤ ‖R.conjTranspose‖*‖star P‖ := rectangular_norm_mul_le _ _
      _ = ‖R‖*‖P‖ := by rw [rectangular_norm_conjTranspose,norm_star]
      _ ≤ 1*1 := by gcongr; exact (norm_diagonalCopies_le 1 p).trans hp
      _ = 1 := one_mul _
  have hKn : ‖K‖ ≤ 1 := by
    calc
      ‖K‖ ≤ ‖star Q‖*‖S‖ := rectangular_norm_mul_le _ _
      _ = ‖Q‖*‖S‖ := by rw [norm_star]
      _ ≤ 1*1 := by gcongr; exact (norm_diagonalCopies_le 1 q).trans hq
      _ = 1 := one_mul _
  let Vval := (η : ℂ)⁻¹ • (R.conjTranspose*(star P*X*star Q)*S)
  let V : supportedAlgebra e he := ⟨Vval,supported_testing_element c hα R S hR hS _ _⟩
  obtain ⟨w,hwn,hEw,hsep⟩ := exists_separated_supported_model_any hσ hσγ hgap hA hn hpi c hc hα e he U hUe V
  let y := matrixSingletonHom (-(R*w*S.conjTranspose))
  have hyn : ‖y‖ ≤ 1 := norm_row_test_le R S w hRn hSn hwn
  have hy : diagonalCopies 1 y= -(R*w*S.conjTranspose) := diagonal_singleton _
  have hcompy : L*(P*(diagonalCopies 1 y)*Q)*K= -w := by
    rw [hy]
    exact compress_row_test L K R S P Q E w hLPR hSQK hEw
  have hcη : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hη)
  have hηV : (η : ℂ) • Vval=L*X*K := by
    dsimp only [Vval]
    rw [smul_smul, mul_inv_cancel₀ hcη, one_smul]
    dsimp only [L,K]
    simp only [rectangular_mul_assoc]
  have hcomp : L*diagonalCopies 1 (T+(η : ℂ) • (p*y*q))*K=(η : ℂ) • (Vval-w) := by
    change L*(diagonalHom 1 (T+(η : ℂ) • (p*y*q)))*K= _
    rw [map_add,map_smul,map_mul,map_mul]
    change L*(X+(η : ℂ) • (P*diagonalCopies 1 y*Q))*K= _
    rw [rectangular_mul_add_support,rectangular_add_mul_support,
      rectangular_mul_smul_support,rectangular_smul_mul_support,hcompy,
      smul_sub,hηV,smul_neg,sub_eq_add_neg]
  refine ⟨y,hyn,?_⟩
  intro H π hπc
  have hs := hsep H π hπc
  have hb := norm_representation_compression_le π L K
    (diagonalCopies 1 (T+(η : ℂ) • (p*y*q))) hLn hKn
  rw [hcomp,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη,
    singleton_diagonal] at hb
  exact (by nlinarith : σ*η ≤ η*‖matrixRepresentation π (Fin n) (Vval-w)‖).trans hb

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniverseSelfadjoint
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

theorem selfadjoint_uniform_perturbation_of_gap_any
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (p q h k c : A) (hpn : ‖p‖ ≤ 1) (hqn : ‖q‖ ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p*q=0)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hph : star p*p*h=h) (hqk : q*star q*k=k)
    (hch : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h))
    (hck : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k))
    (T : A) {η α : ℝ} (hη : 0 < η) (hα : 0 < α) :
    ∃ y : A, ‖y‖ ≤ 1 ∧ IsSelfAdjoint y ∧
      (∃ z : A, y=p*z*q+star (p*z*q)) ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖ := by
  have hpp : p*p*h=h := by simpa only [hp.star_eq] using hph
  have hqq : q*q*k=k := by simpa only [hq.star_eq] using hqk
  have hp4 : star (p*p)*(p*p)*h=h := by
    rw [star_mul,hp.star_eq]
    calc
      (p*p)*(p*p)*h=(p*p)*(p*p*h) := by noncomm_ring
      _ = h := by rw [hpp,hpp]
  have hq4 : (q*q)*star (q*q)*k=k := by
    rw [star_mul,hq.star_eq]
    calc
      (q*q)*(q*q)*k=(q*q)*(q*q*k) := by noncomm_ring
      _ = k := by rw [hqq,hqq]
  have hppn : ‖p*p‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg p])
  have hqqn : ‖q*q‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg q])
  obtain ⟨z,hzn,hz⟩ := uniform_perturbation_of_gap_any hσ hσγ hgap hA hn hpi
    (p*p) (q*q) h k c hppn hqqn hh hk hc hp4 hq4 hch hck T hη hα
  have hy := orthogonal_selfadjoint_test p q z hp hq hpq hpn hqn hzn
  refine ⟨p*z*q+star (p*z*q),hy.1,isSelfAdjoint_add_star _,⟨z,rfl⟩,?_⟩
  intro H π hπc
  rw [hy.2]
  exact hz H π hπc

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniverseCoupling
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

theorem exists_finite_coupling_of_gap_any_oai
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {ι : Type*} (F : ι → OrthogonalPerturbationData A n) :
    ∀ s : Finset ι, (∀ i ∈ s, (F i).p ∈ D ∧ (F i).q ∈ D) →
    ∃ U : A, U ∈ D ∧ IsSelfAdjoint U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ i ∈ s, ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        (F i).α ≤ ‖π (F i).c‖ → ε ≤ ‖π ((F i).p*U*(F i).q)‖ := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨0,D.zero_mem,IsSelfAdjoint.zero A,1,zero_lt_one,?_⟩
      simp
  | @insert i s hi ih =>
      intro hmem
      obtain ⟨U,hUD,hUsa,ε,hε,hU⟩ := ih (fun j hj => hmem j (Finset.mem_insert_of_mem hj))
      let δ := ε/4
      have hδ : 0 < δ := by dsimp [δ] <;> positivity
      have hph : star (F i).p*(F i).p*(F i).h=(F i).h := by
        rw [(F i).nonneg_p.star_eq,mul_assoc,(F i).support_h,(F i).support_h]
      have hqk : (F i).q*star (F i).q*(F i).k=(F i).k := by
        rw [(F i).nonneg_q.star_eq,mul_assoc,(F i).support_k,(F i).support_k]
      obtain ⟨y,hyn,hysa,⟨z,hz⟩,hnew⟩ := selfadjoint_uniform_perturbation_of_gap_any
        hσ.le hσγ hgap hA hn hpi (F i).p (F i).q (F i).h (F i).k (F i).c
        (F i).norm_p (F i).norm_q (F i).nonneg_p (F i).nonneg_q (F i).orthogonal
        (F i).nonneg_h (F i).nonneg_k (F i).nonneg_c hph hqk
        (F i).compare_h (F i).compare_k ((F i).p*U*(F i).q) hδ (F i).pos_α
      have hyD : y ∈ D := by
        rw [hz]
        exact hD.symmetrized_corner_mem (hmem i (Finset.mem_insert_self ..)).1
          (hmem i (Finset.mem_insert_self ..)).2 z
      let U' := U+(δ : ℂ) • y
      have hU'D : U' ∈ D := D.add_mem hUD (D.smul_mem _ hyD)
      have hU'sa : IsSelfAdjoint U' := by
        show star (U+(δ : ℂ) • y)=U+(δ : ℂ) • y
        simp only [star_add,star_smul,hUsa.star_eq,hysa.star_eq,Complex.star_def,Complex.conj_ofReal]
      refine ⟨U',hU'D,hU'sa,min (ε/2) (σ*δ),lt_min (by positivity) (mul_pos hσ hδ),?_⟩
      intro j hj H π hπc
      rcases Finset.mem_insert.mp hj with rfl | hj
      · apply (min_le_right _ _).trans
        dsimp only [U']
        rw [corner_add_smul]
        exact hnew H π hπc
      · have hold := hU j hj H π hπc
        have herr : ‖π ((δ : ℂ) • ((F j).p*y*(F j).q))‖ ≤ δ := by
          calc
            _ ≤ ‖(δ : ℂ) • ((F j).p*y*(F j).q)‖ := NonUnitalStarAlgHom.norm_apply_le π _
            _ = δ*‖(F j).p*y*(F j).q‖ := by
              rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
            _ ≤ δ*1 := mul_le_mul_of_nonneg_left
              (norm_corner_le_one _ _ _ (F j).norm_p (F j).norm_q hyn) hδ.le
            _ = δ := mul_one _
        have hdiff : π ((F j).p*U*(F j).q)-π ((F j).p*U'*(F j).q)=
            -π ((δ : ℂ) • ((F j).p*y*(F j).q)) := by
          dsimp only [U']
          rw [corner_add_smul,map_add]
          abel
        have ht := norm_le_norm_add_norm_sub' (π ((F j).p*U*(F j).q))
          (π ((F j).p*U'*(F j).q))
        rw [hdiff,norm_neg] at ht
        apply (min_le_left _ _).trans
        dsimp only [δ] at herr
        linarith

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u, u_1} : type_of% @OAI.WeakPureInfiniteness.exists_finite_coupling_of_gap_any_oai.{u, u_1} := @OAI.WeakPureInfiniteness.exists_finite_coupling_of_gap_any_oai.{u, u_1}
