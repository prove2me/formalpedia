-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.exists_orthogonal_detected_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:14:28.1632+00:00
-- url     : https://prove2.me/submissions/02d9ddae-86a5-4318-b678-4c6e38586a3f

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W001

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
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeSpatialAmbientMemNonUnitalStarSubalgebraComplexMinimalTensor _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalSplitting
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

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma spectrum_dichotomy_of_no_orthogonal
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₙₐ[ℂ] B)
    (hno : ∀ a ∈ D,∀ b ∈ D,0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {c : A} (hc : c ∈ D) (hc0 : 0 ≤ c) {s : ℝ} (hs : s ∈ spectrum ℝ (π c)) :
    s=0 ∨ s=‖π c‖ := by
  by_contra! hn
  obtain hB | hB := subsingleton_or_nontrivial B
  · have he : spectrum ℝ (π c)=∅ := spectrum.of_subsingleton (π c)
    rw [he] at hs
    exact hs
  let : Nontrivial B := hB
  have hπc : 0 ≤ π c := map_nonneg π hc0
  have hs0 : 0 < s := lt_of_le_of_ne
    (NonnegSpectrumClass.nonneg_of_mem_quasispectrum hπc (spectrum_subset_quasispectrum ℝ (π c) hs)) hn.1.symm
  have hsN : s < ‖π c‖ := lt_of_le_of_ne
    ((Real.le_norm_self s).trans (spectrum.norm_le_norm_of_mem hs)) hn.2
  let t : ℝ := (s+‖π c‖)/2
  have hst : s < t := by dsimp [t] <;> linarith
  have htN : t < ‖π c‖ := by dsimp [t] <;> linarith
  have ht0 : 0 < t := hs0.trans hst
  let f : ℝ → ℝ := fun x => x*max (t-x) 0
  let g : ℝ → ℝ := fun x => max (x-t) 0
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hf0 : f 0=0 := by simp [f]
  have hg0 : g 0=0 := by dsimp [g]; rw [max_eq_right (by linarith)]
  have hfg : cfcₙ f c*cfcₙ g c=0 := by
    rw [← cfcₙ_mul f g c hf.continuousOn hf0 hg.continuousOn hg0]
    calc
      cfcₙ (fun x => f x*g x) c=cfcₙ (0 : ℝ → ℝ) c := by
        apply cfcₙ_congr
        intro x _
        change x*max (t-x) 0*max (x-t) 0=0
        rcases le_total x t with hx | hx
        · rw [max_eq_right (by linarith : x-t ≤ 0),mul_zero]
        · rw [max_eq_right (by linarith : t-x ≤ 0),mul_zero,zero_mul]
      _ = 0 := cfcₙ_zero ℝ c
  have hfa : 0 ≤ cfcₙ f c := cfcₙ_nonneg (fun x hx =>
    mul_nonneg (NonnegSpectrumClass.nonneg_of_mem_quasispectrum hc0 hx) (le_max_right _ _))
  have hga : 0 ≤ cfcₙ g c := cfcₙ_nonneg (fun _ _ => le_max_right _ _)
  have hfπ : π (cfcₙ f c)=cfcₙ f (π c) :=
    π.map_cfcₙ f c hf.continuousOn hf0 (by fun_prop) hc0.isSelfAdjoint hπc.isSelfAdjoint
  have hgπ : π (cfcₙ g c)=cfcₙ g (π c) :=
    π.map_cfcₙ g c hg.continuousOn hg0 (by fun_prop) hc0.isSelfAdjoint hπc.isSelfAdjoint
  obtain hz | hz := hno (cfcₙ f c) (cfcₙ_mem f hc) (cfcₙ g c) (cfcₙ_mem g hc) hfa hga hfg
  · rw [hfπ] at hz
    have hh := norm_apply_le_norm_cfcₙ f (π c)
      (spectrum_subset_quasispectrum ℝ (π c) hs) hf.continuousOn hf0 hπc.isSelfAdjoint
    rw [hz,norm_zero] at hh
    have hpos : 0 < f s := by dsimp [f]; rw [max_eq_left (by linarith)]; positivity
    exact (not_le_of_gt (norm_pos_iff.mpr (ne_of_gt hpos))) hh
  · rw [hgπ] at hz
    have hcn : π c ≠ 0 := by intro he; rw [he,norm_zero] at htN; linarith
    let : Nontrivial B := nontrivial_of_ne (π c) 0 hcn
    have hh := norm_apply_le_norm_cfcₙ g (π c)
      (spectrum_subset_quasispectrum ℝ (π c) (CStarAlgebra.norm_mem_spectrum_of_nonneg (a := π c) hπc))
      hg.continuousOn hg0 hπc.isSelfAdjoint
    rw [hz,norm_zero] at hh
    have hpos : 0 < g ‖π c‖ := by dsimp [g]; rw [max_eq_left (by linarith)]; linarith
    exact (not_le_of_gt (norm_pos_iff.mpr (ne_of_gt hpos))) hh

lemma square_eq_norm_smul_of_no_orthogonal
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₙₐ[ℂ] B)
    (hno : ∀ a ∈ D,∀ b ∈ D,0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {c : A} (hc : c ∈ D) (hc0 : 0 ≤ c) : π c*π c=‖π c‖ • π c := by
  have hπc : IsSelfAdjoint (π c) := (map_nonneg π hc0).isSelfAdjoint
  calc
    π c*π c=cfcₙ (fun x : ℝ => x*x) (π c) := by rw [cfcₙ_mul (fun x : ℝ => x) (fun x : ℝ => x) (π c),cfcₙ_id' ℝ _ hπc]
    _ = cfcₙ (fun x : ℝ => ‖π c‖*x) (π c) := by
      apply cfcₙ_congr
      intro x hx
      rcases (mem_quasispectrum_iff.mp hx) with rfl | hx
      · simp
      rcases spectrum_dichotomy_of_no_orthogonal D π hno hc hc0 hx with rfl | rfl <;> simp
    _ = ‖π c‖ • π c := cfcₙ_const_mul_id _ _ hπc

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ScalarHereditary
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped CStarAlgebra Topology ComplexStarModule

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_mul_of_hereditary_square (π : A →⋆ₙₐ[ℂ] B) {h : A} (hh : IsSelfAdjoint h)
    {l : ℝ} (he : π h*π h=l • π h) {b : A} (hb : b ∈ hereditarySubalgebra h hh) :
    π h*π b=l • π b := by
  have hc : IsClosed {x : A | π h*π x=l • π x} := isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal _ hc hb
  rintro _ ⟨x,rfl⟩
  change π h*π (h*x*h)=l • π (h*x*h)
  simp only [map_mul]
  rw [← mul_assoc,← mul_assoc,he,smul_mul_assoc,smul_mul_assoc]

lemma exists_real_scalar_of_no_orthogonal (π : A →⋆ₙₐ[ℂ] B)
    {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0)
    (hno : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {b : A} (hb : b ∈ hereditarySubalgebra h hh.isSelfAdjoint) (hb0 : 0 ≤ b) :
    ∃ r : ℝ,π b=r • π h := by
  let l := ‖π h‖
  let μ := ‖π b‖
  let r := ‖π (h+b)‖
  have hl : 0 < l := norm_pos_iff.mpr hhn
  have hsqh : π h*π h=l • π h := square_eq_norm_smul_of_no_orthogonal _ π hno
    (self_mem_hereditary h hh) hh
  have hsqb : π b*π b=μ • π b := square_eq_norm_smul_of_no_orthogonal _ π hno hb hb0
  have hsql : π h*π b=l • π b := map_mul_of_hereditary_square π hh.isSelfAdjoint hsqh hb
  have hsqr : π b*π h=l • π b := by
    have he := congrArg star hsql
    simpa only [star_mul,(map_nonneg π hh).star_eq,(map_nonneg π hb0).star_eq,
      star_smul,star_trivial] using he
  have hsum := square_eq_norm_smul_of_no_orthogonal _ π hno
    ((hereditarySubalgebra h hh.isSelfAdjoint).add_mem (self_mem_hereditary h hh) hb) (add_nonneg hh hb0)
  have hprod : π (h+b)*π (h+b)=l • π h+(2*l+μ) • π b := by
    simp only [map_add,mul_add,add_mul,hsqh,hsqb,hsql,hsqr]
    module
  rw [hprod] at hsum
  change l • π h+(2*l+μ) • π b=r • π (h+b) at hsum
  rw [map_add,smul_add] at hsum
  have hr : r ≤ l+μ := by dsimp [r,l,μ]; rw [map_add]; exact norm_add_le _ _
  have hd : 0 < 2*l+μ-r := by linarith
  have he : (2*l+μ-r) • π b=(r-l) • π h := by
    convert congrArg (fun z : B => z-l • π h-r • π b) hsum using 1 <;> first | (with_reducible_and_instances rfl) | (module)
  refine ⟨(2*l+μ-r)⁻¹*(r-l),?_⟩
  calc
    π b=(2*l+μ-r)⁻¹ • ((2*l+μ-r) • π b) := by
      rw [smul_smul,inv_mul_cancel₀ (ne_of_gt hd),one_smul]
    _ = (2*l+μ-r)⁻¹ • ((r-l) • π h) := by rw [he]
    _ = _ := by rw [smul_smul]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ComplexScalar
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped CStarAlgebra Topology ComplexStarModule

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma exists_scalar_of_positive_scalars (D : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (D : Set A)] (π : A →⋆ₙₐ[ℂ] B) (k : B)
    (hp : ∀ b ∈ D,0 ≤ b → ∃ r : ℝ,π b=r • k) {x : A} (hx : x ∈ D) :
    ∃ z : ℂ,π x=z • k := by
  have hsa : ∀ b ∈ D,IsSelfAdjoint b → ∃ r : ℝ,π b=r • k := by
    intro b hb hbs
    obtain ⟨r,hr⟩ := hp b⁺ (cfcₙ_mem (·⁺ : ℝ → ℝ) hb) (CFC.posPart_nonneg b)
    obtain ⟨s,hs⟩ := hp b⁻ (cfcₙ_mem (·⁻ : ℝ → ℝ) hb) (CFC.negPart_nonneg b)
    refine ⟨r-s,?_⟩
    calc
      π b=π (b⁺-b⁻) := congrArg π (CFC.posPart_sub_negPart b hbs).symm
      _ = π b⁺-π b⁻ := map_sub π _ _
      _ = (r-s) • k := by rw [hr,hs]; module
  have hre : (ℜ x : A) ∈ D := by
    rw [realPart_apply_coe,← IsScalarTower.algebraMap_smul ℂ]
    exact SMulMemClass.smul_mem _ (add_mem hx (star_mem hx))
  have him : (ℑ x : A) ∈ D := by
    rw [imaginaryPart_apply_coe]
    apply SMulMemClass.smul_mem
    rw [← IsScalarTower.algebraMap_smul ℂ (M := A)]
    exact SMulMemClass.smul_mem _ (sub_mem hx (star_mem hx))
  obtain ⟨r,hr⟩ := hsa _ hre (ℜ x).property
  obtain ⟨s,hs⟩ := hsa _ him (ℑ x).property
  refine ⟨(r : ℂ)+Complex.I*(s : ℂ),?_⟩
  calc
    π x=π ((ℜ x : A)+Complex.I • (ℑ x : A)) := congrArg π (realPart_add_I_smul_imaginaryPart x).symm
    _ = r • k+Complex.I • (s • k) := by rw [map_add,map_smul,hr,hs]
    _ = _ := by
      rw [add_smul,mul_smul]
      change r • k+Complex.I • (s • k) =
        (algebraMap ℝ ℂ r) • k+Complex.I • ((algebraMap ℝ ℂ s) • k)
      rw [IsScalarTower.algebraMap_smul ℂ,IsScalarTower.algebraMap_smul ℂ]

lemma hereditary_image_scalar_of_no_orthogonal (π : A →⋆ₙₐ[ℂ] B)
    {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0)
    (hno : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {x : A} (hx : x ∈ hereditarySubalgebra h hh.isSelfAdjoint) :
    ∃ z : ℂ,π x=z • π h :=
  exists_scalar_of_positive_scalars _ π (π h)
    (fun _ hb hb0 => exists_real_scalar_of_no_orthogonal π hh hhn hno hb hb0) hx

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

lemma ProperlyInfinite.diagonal_powers {a : A} {n : ℕ}
    (hpi : ProperlyInfinite (diagonalCopies n a)) (k : ℕ) :
    CuntzSubequiv (diagonalCopies (2^k*n) a) (diagonalCopies n a) := by
  induction k with
  | zero =>
    exact diagonalCopies_cuntzSubequiv a (by simp)
  | succ k ih =>
    have h := (ih.blockSum ih).trans hpi
    have h' := h.submatrix_left (finSumFinEquiv.symm : Fin (2^k*n+2^k*n) → _)
    rw [diagonalCopies_double] at h'
    exact (diagonalCopies_cuntzSubequiv a (show 2^(k+1)*n ≤ 2^k*n+2^k*n by
      rw [pow_succ]; nlinarith)).trans h'

lemma ProperlyInfinite.diagonal_absorbs {a : A} {n : ℕ} (hn : 1 ≤ n)
    (hpi : ProperlyInfinite (diagonalCopies n a)) (d : ℕ) :
    CuntzSubequiv (diagonalCopies d a) (diagonalCopies n a) := by
  have hd : d ≤ 2^d*n := calc
    d ≤ 2^d := (Nat.lt_two_pow_self (n := d)).le
    _ ≤ 2^d*n := by simpa only [mul_one] using Nat.mul_le_mul_left (2^d) hn
  exact (diagonalCopies_cuntzSubequiv a hd).trans (hpi.diagonal_powers d)

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

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectralRamp_mul_positiveCut (a : A) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 2*θ ≤ δ) :
    cfcₙ (spectralRamp θ) a*positiveCut δ a = positiveCut δ a := by
  have hf0 : max (0-δ) 0 = 0 := by rw [max_eq_right]; linarith
  rw [positiveCut, ← cfcₙ_mul (spectralRamp θ) (fun s : ℝ => max (s-δ) 0) a
    (continuous_spectralRamp θ).continuousOn (spectralRamp_eq_zero hθ hθ.le)
    (by fun_prop) hf0]
  congr 1
  funext s
  by_cases hs : s ≤ δ
  · rw [max_eq_right (by linarith : s-δ ≤ 0), mul_zero]
  · rw [spectralRamp_eq_one hθ (by linarith), one_mul]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FixedColumns
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

lemma uniformCopies_absorbs {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (a : A) (ha : 0 ≤ a) (d : ℕ) :
    CuntzSubequiv (diagonalCopies d a) (diagonalCopies n a) := by
  by_cases haz : a=0
  · subst a
    intro ε hε
    refine ⟨0, ?_⟩
    simpa [diagonalCopies] using hε
  · exact (hpi a ha haz).diagonal_absorbs hn d

local instance matrixRealModuleColumns_r3d3278_1 {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _
lemma exists_finite_model_columns {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (c : A) {α : ℝ} (hα : 0 < α) (d : ℕ) :
    ∃ L : CStarMatrix (Fin n) (Fin d) A,
      L.conjTranspose*L=diagonalCopies d (cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) c)) ∧
      L*L.conjTranspose ∈ hereditarySubalgebra (diagonalCopies n (positiveCut (α/2) c))
        (diagonalCopies_nonneg n (positiveCut_nonneg (α/2) c)).isSelfAdjoint ∧
      ‖L‖ ≤ 1 ∧ diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*L=L := by
  let c₁ := positiveCut (α/2) c
  have hc₁ : 0 ≤ c₁ := positiveCut_nonneg _ _
  obtain ⟨L,hL,hLher,hLn⟩ := (uniformCopies_absorbs hn hpi c₁ hc₁ d).exact_spectralRamp
    (diagonalCopies_nonneg d hc₁) (diagonalCopies_nonneg n hc₁) (α/8) (by positivity)
  refine ⟨L, ?_, hLher, hLn, ?_⟩
  · rw [hL, diagonalCopies_cfc d c₁ hc₁.isSelfAdjoint (spectralRamp (α/8))
      (continuous_spectralRamp _) (spectralRamp_eq_zero (by positivity) (by positivity))]
  · apply rectangular_left_identity_of_hereditary_range _ _ L
      (diagonalCopies_nonneg n hc₁).isSelfAdjoint _ hLher
    change (diagonalHom n (cfcₙ (spectralRamp (α/4)) c))*(diagonalHom n c₁)=diagonalHom n c₁
    rw [← map_mul]
    congr 1
    exact spectralRamp_mul_positiveCut c (by positivity) (by linarith)

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

lemma hereditarySubalgebra_inner (h : A) (hh : IsSelfAdjoint h) :
    IsClosedInner (hereditarySubalgebra h hh) := by
  refine ⟨NonUnitalStarSubalgebra.isClosed_topologicalClosure _,?_⟩
  intro a ha b hb x
  have hc : IsClosed {a : A | a*x*b ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc ha
  rintro _ ⟨u,rfl⟩
  have hc' : IsClosed {b : A | (h*u*h)*x*b ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc' hb
  rintro _ ⟨v,rfl⟩
  have he : (h*u*h)*x*(h*v*h)=h*(u*h*x*h*v)*h := by noncomm_ring
  change (h*u*h)*x*(h*v*h) ∈ hereditarySubalgebra h hh
  rw [he]
  exact sandwich_mem h (u*h*x*h*v) hh

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalPair
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

lemma map_ramp_cut_mul_of_no_orthogonal (π : A →⋆ₙₐ[ℂ] B)
    {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0)
    (hno : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0) :
    π (cfcₙ (spectralRamp (‖π h‖/8)) (positiveCut (‖π h‖/2) h))*π h=π h := by
  let l := ‖π h‖
  have hl : 0 < l := norm_pos_iff.mpr hhn
  have hhπ : IsSelfAdjoint (π h) := (map_nonneg π hh).isSelfAdjoint
  have hf : Continuous (fun x : ℝ => max (x-l/2) 0) := by fun_prop
  have hf0 : max (0-l/2) 0=0 := max_eq_right (by linarith)
  have hg0 : spectralRamp (l/8) 0=0 := spectralRamp_eq_zero (by positivity) (by positivity)
  rw [π.map_cfcₙ _ _ (continuous_spectralRamp _).continuousOn hg0 (by fun_prop)
    (positiveCut_nonneg _ _).isSelfAdjoint (map_nonneg π (positiveCut_nonneg _ _)).isSelfAdjoint]
  change cfcₙ (spectralRamp (l/8)) (π (cfcₙ (fun x : ℝ => max (x-l/2) 0) h))*π h=π h
  rw [π.map_cfcₙ _ _ hf.continuousOn hf0 (by fun_prop) hh.isSelfAdjoint hhπ]
  rw [← cfcₙ_comp (spectralRamp (l/8)) (fun x : ℝ => max (x-l/2) 0) (π h)
    (continuous_spectralRamp _).continuousOn hg0 hf.continuousOn hf0 hhπ]
  conv_rhs => rw [← cfcₙ_id' ℝ (π h) hhπ]
  conv_lhs => rhs; rw [← cfcₙ_id' ℝ (π h) hhπ]
  rw [← cfcₙ_mul ((spectralRamp (l/8)) ∘ (fun x : ℝ => max (x-l/2) 0))
    (fun x : ℝ => x) (π h) ((continuous_spectralRamp _).comp hf).continuousOn
    (by simpa only [Function.comp_apply,hf0] using hg0) continuous_id.continuousOn rfl]
  apply cfcₙ_congr
  intro x hx
  rcases mem_quasispectrum_iff.mp hx with rfl | hx
  · simp
  rcases spectrum_dichotomy_of_no_orthogonal _ π hno (self_mem_hereditary h hh) hh hx with rfl | rfl
  · simp
  · change spectralRamp (l/8) (max (l-l/2) 0)*l=l
    rw [max_eq_left (by linarith),spectralRamp_eq_one (by positivity) (by linarith),one_mul]

lemma exists_orthogonal_detected_pair_oai {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (π : A →⋆ₙₐ[ℂ] B) {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0) :
    ∃ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∃ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a ∧ 0 ≤ b ∧ a*b=0 ∧ π a ≠ 0 ∧ π b ≠ 0 := by
  classical
  by_contra! hno
  have hno' : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0 := by
    intro a ha b hb ha0 hb0 hab
    by_cases han : π a=0
    · exact Or.inl han
    · exact Or.inr (hno a ha b hb ha0 hb0 hab han)
  let l := ‖π h‖
  have hl : 0 < l := norm_pos_iff.mpr hhn
  let e := cfcₙ (spectralRamp (l/4)) h
  let d := cfcₙ (spectralRamp (l/8)) (positiveCut (l/2) h)
  obtain ⟨L,hL,-,-,heL⟩ := exists_finite_model_columns hn hpi h hl (n+1)
  have he : e ∈ hereditarySubalgebra h hh.isSelfAdjoint :=
    cfcₙ_mem _ (self_mem_hereditary h hh)
  have heL' (i : Fin n) (j : Fin (n+1)) : e*L i j=L i j := by
    have hv := congrArg (fun X => X i j) heL
    change ((Matrix.diagonal fun _ : Fin n => e)*(CStarMatrix.ofMatrix.symm L)) i j=L i j at hv
    simpa only [Matrix.diagonal_mul,CStarMatrix.ofMatrix_symm_apply] using hv
  have hm (i : Fin n) (j : Fin (n+1)) : L i j*h ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
    rw [← heL' i j]
    exact (hereditarySubalgebra_inner h hh.isSelfAdjoint).2 e he h
      (self_mem_hereditary h hh) (L i j)
  choose z hz using fun i j => hereditary_image_scalar_of_no_orthogonal π hh hhn hno' (hm i j)
  let Z : Matrix (Fin n) (Fin (n+1)) ℂ := z
  have hsq : π h*π h=l • π h := square_eq_norm_smul_of_no_orthogonal _ π hno'
    (self_mem_hereditary h hh) hh
  have hsqn : π h*π h ≠ 0 := by rw [hsq]; exact smul_ne_zero (ne_of_gt hl) hhn
  have hdh : π d*π h=π h := map_ramp_cut_mul_of_no_orthogonal π hh hhn hno'
  have hgram (i j : Fin (n+1)) :
      (Z.conjTranspose*Z) i j • (π h*π h) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j • (π h*π h) := by
    calc
      (Z.conjTranspose*Z) i j • (π h*π h) =
          ∑ k : Fin n,star (π (L k i*h))*π (L k j*h) := by
        change (∑ k : Fin n,star (z k i)*z k j) • (π h*π h)=_
        simp only [Finset.sum_smul,hz,star_smul,(map_nonneg π hh).star_eq,
          smul_mul_assoc,mul_smul_comm,smul_smul]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_comm]
      _ = π (h*(L.conjTranspose*L) i j*h) := by
        simp only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,map_mul,map_star,map_sum,
          Finset.mul_sum,Finset.sum_mul,star_mul,(map_nonneg π hh).star_eq]
        apply Finset.sum_congr rfl
        intro k _
        noncomm_ring
      _ = π (h*(diagonalCopies (n+1) d) i j*h) := by rw [hL]
      _ = _ := by
        by_cases hij : i=j
        · subst j
          simp only [diagonalCopies,CStarMatrix.ofMatrix_apply,Matrix.diagonal_apply_eq,Matrix.one_apply_eq,one_smul,map_mul]
          rw [mul_assoc,hdh]
        · simp [diagonalCopies,Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij]
  have hZZ : Z.conjTranspose*Z=1 := by
    ext i j
    exact (smul_left_injective ℂ hsqn) (hgram i j)
  have hr := (Matrix.rank_mul_le_left Z.conjTranspose Z).trans (Matrix.rank_le_width Z.conjTranspose)
  rw [hZZ,Matrix.rank_one] at hr
  simp only [Fintype.card_fin] at hr
  omega

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.WeakPureInfiniteness.exists_orthogonal_detected_pair_oai.{u, v} := @OAI.WeakPureInfiniteness.exists_orthogonal_detected_pair_oai.{u, v}
