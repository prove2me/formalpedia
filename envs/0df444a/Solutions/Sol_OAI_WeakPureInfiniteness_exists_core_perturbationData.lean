-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.exists_core_perturbationData
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:14:49.723956+00:00
-- url     : https://prove2.me/submissions/22024f1a-3147-48b5-91ad-bebddfc5f741

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W000
import Definitions.Def_OAIQ246W001
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
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Hereditary
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeSpatialAmbientMemNonUnitalStarSubalgebraComplexMinimalTensor _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Plateau
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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
lemma spectralRamp_positiveCut_plateau (a : A) (ha : IsSelfAdjoint a)
    {α : ℝ} (hα : 0 < α) :
    cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) a)*positiveCut (7*α/8) a =
      positiveCut (7*α/8) a := by
  have h0 : max (0-α/2) 0 = 0 := max_eq_right (by linarith)
  have h1 : max (0-7*α/8) 0 = 0 := max_eq_right (by linarith)
  rw [positiveCut, ← cfcₙ_comp (spectralRamp (α/8)) (fun s : ℝ => max (s-α/2) 0) a
    (continuous_spectralRamp _).continuousOn (spectralRamp_eq_zero (by positivity) (by positivity))
    (by fun_prop) h0 ha]
  rw [positiveCut, ← cfcₙ_mul (spectralRamp (α/8) ∘ (fun s : ℝ => max (s-α/2) 0)) (fun s : ℝ => max (s-7*α/8) 0) a ((continuous_spectralRamp _).comp (by fun_prop)).continuousOn (by
    change spectralRamp (α/8) (max (0-α/2) 0)=0
    rw [h0]
    exact spectralRamp_eq_zero (by positivity) (by positivity))
    (by fun_prop) h1]
  congr 1
  funext s
  change spectralRamp (α/8) (max (s-α/2) 0)*max (s-7*α/8) 0 = max (s-7*α/8) 0
  by_cases hs : s ≤ 7*α/8
  · rw [max_eq_right (by linarith : s-7*α/8 ≤ 0), mul_zero]
  · rw [spectralRamp_eq_one (by positivity) (by have := le_max_left (s-α/2) 0; linarith), one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positiveCut_ne_zero_of_lt_norm {b : H →L[ℂ] H} (hb : 0 ≤ b)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδb : δ < ‖b‖) : positiveCut δ b ≠ 0 := by
  have : Nontrivial (H →L[ℂ] H) := ⟨⟨b, 0, by intro h; rw [h, norm_zero] at hδb; linarith⟩⟩
  have hm := CStarAlgebra.norm_mem_spectrum_of_nonneg hb
  have hle := norm_apply_le_norm_cfcₙ (fun s : ℝ => max (s-δ) 0) b
    (spectrum_subset_quasispectrum ℝ b hm) (by fun_prop) (max_eq_right (by linarith)) hb.isSelfAdjoint
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_eq_left (by linarith)] at hle
  intro hz
  change positiveCut δ b = 0 at hz
  change ‖b‖-δ ≤ ‖positiveCut δ b‖ at hle
  rw [hz, norm_zero] at hle
  linarith

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CoreSelection
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

lemma exists_supported_positive_core (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    {u : A} (hu : 0 ≤ u) (hn : π u ≠ 0) :
    ∃ p ∈ hereditarySubalgebra u hu.isSelfAdjoint,
      ∃ h ∈ hereditarySubalgebra u hu.isSelfAdjoint,
      0 ≤ p ∧ ‖p‖ ≤ 1 ∧ 0 ≤ h ∧ p*h=h ∧ π h ≠ 0 := by
  let α := ‖π u‖
  have hα : 0 < α := norm_pos_iff.mpr hn
  let p := cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) u)
  let h := positiveCut (7*α/8) u
  have huD := self_mem_hereditary u hu
  have hmidD : positiveCut (α/2) u ∈ hereditarySubalgebra u hu.isSelfAdjoint := cfcₙ_mem _ huD
  have hpD : p ∈ hereditarySubalgebra u hu.isSelfAdjoint := cfcₙ_mem _ hmidD
  have hhD : h ∈ hereditarySubalgebra u hu.isSelfAdjoint := cfcₙ_mem _ huD
  have hp : 0 ≤ p := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg (α/8) s)
  have hpn : ‖p‖ ≤ 1 := by
    apply norm_cfcₙ_le
    intro s _
    rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg (α/8) s)]
    exact spectralRamp_le_one _ _
  refine ⟨p,hpD,h,hhD,hp,hpn,positiveCut_nonneg _ _,
    spectralRamp_positiveCut_plateau u hu.isSelfAdjoint hα,?_⟩
  have he : π h=positiveCut (7*α/8) (π u) :=
    π.map_cfcₙ (fun s : ℝ => max (s-7*α/8) 0) u (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hu.isSelfAdjoint (map_nonneg π hu).isSelfAdjoint
  rw [he]
  exact positiveCut_ne_zero_of_lt_norm (map_nonneg π hu) (by positivity) (by dsimp [α] <;> linarith)

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

omit [PartialOrder A] [StarOrderedRing A] in
lemma mul_zero_of_hereditary {a b x y : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : a*b=0) (hx : x ∈ hereditarySubalgebra a ha) (hy : y ∈ hereditarySubalgebra b hb) :
    x*y=0 := by
  have hxb := mul_zero_of_mem_hereditary_left ha hab hx
  apply closure_minimal _ (isClosed_eq (continuous_const.mul continuous_id) continuous_const) hy
  rintro _ ⟨c,rfl⟩
  change x*(b*c*b)=0
  rw [← mul_assoc,← mul_assoc,hxb,zero_mul,zero_mul]

lemma exists_orthogonal_detected_family {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (π : A →⋆ₙₐ[ℂ] B) (m : ℕ) {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0) :
    ∃ x : Fin m → A,
      (∀ i,x i ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ 0 ≤ x i ∧ π (x i) ≠ 0) ∧
      ∀ i j,i ≠ j → x i*x j=0 := by
  induction m generalizing h with
  | zero => exact ⟨Fin.elim0,by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,b,hb,ha0,hb0,hab,han,hbn⟩ := exists_orthogonal_detected_pair hn hpi π hh hhn
    obtain ⟨x,hx,hxx⟩ := ih ha0 han
    refine ⟨Fin.cons b x,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hb,hb0,hbn⟩
      · exact ⟨hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
          ha0.isSelfAdjoint ha (hx j).1,(hx j).2⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases (by simp) (fun j _ => ?_) j
        have he := mul_zero_of_mem_hereditary_left ha0.isSelfAdjoint hab (hx j).1
        have he' := congrArg star he
        simpa only [Fin.cons_zero,Fin.cons_succ,star_mul,hb0.star_eq,(hx j).2.1.star_eq,star_zero] using he'
      · refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j
        · exact mul_zero_of_mem_hereditary_left ha0.isSelfAdjoint hab (hx i).1
        · exact hxx i j (fun he => hij (congrArg Fin.succ he))

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularComparison
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

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

lemma cuntzSubequiv_of_hereditary {h x : CStarMatrix n n A}
    (hh : 0 ≤ h) (hx : 0 ≤ x) (hm : x ∈ hereditarySubalgebra h hh.isSelfAdjoint) :
    CuntzSubequiv x h := by
  intro ε hε
  simpa only [CStarMatrix.star_eq_conjTranspose] using
    exists_comparison_of_hereditary h x hh hx hm ε hε

attribute [local instance] OAI.WeakPureInfiniteness.matrixRealModuleComparison
lemma rectangular_initial_cuntz_range (u : CStarMatrix m n A) :
    CuntzSubequiv (u.conjTranspose*u) (u*u.conjTranspose) := by
  let t := u.conjTranspose*u
  have ht : 0 ≤ t := rectangular_initial_nonneg u
  have htt : 0 ≤ t*t := by simpa only [ht.star_eq] using star_mul_self_nonneg t
  have hm : t ∈ hereditarySubalgebra (t*t) htt.isSelfAdjoint := by
    have hs := sqrt_mem_hereditary (t*t) (t*t) htt.isSelfAdjoint
      (self_mem_hereditary (t*t) htt) htt
    rwa [CFC.sqrt_mul_self t ht] at hs
  intro ε hε
  obtain ⟨b,hb⟩ := cuntzSubequiv_of_hereditary htt ht hm ε hε
  refine ⟨u*b, ?_⟩
  have he : (u*b).conjTranspose*(u*u.conjTranspose)*(u*b) = b.conjTranspose*(t*t)*b := by
    rw [rectangular_star_mul]
    dsimp only [t]
    simp only [rectangular_mul_assoc]
  rwa [he]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteComparison
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

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma continuous_fiberDiagonal (m : ℕ) : Continuous (fiberDiagonal (A := A) (m := m)) := by
  change Continuous (fun x : Fin m → A => Matrix.diagonal x)
  fun_prop

lemma copies_cuntz_fiberDiagonal {m : ℕ} {c : A} {x : Fin m → A}
    (hcx : ∀ i,ElementCuntzSubequiv c (x i)) :
    CuntzSubequiv (diagonalCopies m c) (fiberDiagonal x) := by
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp
    ((continuous_fiberDiagonal (A := A) m).continuousAt (x := fun _ => c)) ε hε
  choose v hv using fun i => elementCuntzSubequiv_iff.mp (hcx i) δ hδ
  refine ⟨fiberDiagonal v,?_⟩
  have he : (fiberDiagonal v).conjTranspose*fiberDiagonal x*fiberDiagonal v=
      fiberDiagonal (fun i => star (v i)*x i*v i) := by
    change (Matrix.diagonal v).conjTranspose*Matrix.diagonal x*Matrix.diagonal v=
      Matrix.diagonal (fun i => star (v i)*x i*v i)
    simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Pi.star_apply]
  rw [he]
  have hd : dist (fun i => star (v i)*x i*v i) (fun _ => c) < δ :=
    (dist_pi_lt_iff hδ).mpr (fun i => by simpa only [dist_eq_norm] using hv i)
  have hout := hcont hd
  rw [dist_eq_norm] at hout
  exact hout

lemma orthogonal_fiberDiagonal_cuntz_sum {m : ℕ} (x : Fin m → A) (hx : ∀ i,0 ≤ x i)
    (hxx : ∀ i j,i ≠ j → x i*x j=0) :
    CuntzSubequiv (fiberDiagonal x) (diagonalCopies 1 (∑ i,x i)) := by
  let R : CStarMatrix (Fin 1) (Fin m) A := fun _ j => CFC.sqrt (x j)
  have hRi : R.conjTranspose*R=fiberDiagonal x := by
    ext i j
    change (∑ k : Fin 1,star (CFC.sqrt (x i))*CFC.sqrt (x j))=Matrix.diagonal x i j
    simp only [Fin.sum_univ_one,(CFC.sqrt_nonneg (x i)).star_eq]
    by_cases hij : i=j
    · subst j
      rw [Matrix.diagonal_apply_eq,CFC.sqrt_mul_sqrt_self _ (hx i)]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact mul_zero_of_hereditary (hx i).isSelfAdjoint (hx j).isSelfAdjoint (hxx i j hij)
        (sqrt_mem_hereditary _ _ (hx i).isSelfAdjoint (self_mem_hereditary _ (hx i)) (hx i))
        (sqrt_mem_hereditary _ _ (hx j).isSelfAdjoint (self_mem_hereditary _ (hx j)) (hx j))
  have hRr : R*R.conjTranspose=diagonalCopies 1 (∑ i,x i) := by
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j
    change (∑ k : Fin m,CFC.sqrt (x k)*star (CFC.sqrt (x k)))=∑ k : Fin m,x k
    apply Finset.sum_congr rfl
    intro k _
    rw [(CFC.sqrt_nonneg _).star_eq,CFC.sqrt_mul_sqrt_self _ (hx k)]
  rw [← hRi,← hRr]
  exact rectangular_initial_cuntz_range R

lemma copies_cuntz_of_common_orthogonal {m : ℕ} {c h : A} (hh : 0 ≤ h)
    (x : Fin m → A) (hx : ∀ i,0 ≤ x i ∧ x i ∈ hereditarySubalgebra h hh.isSelfAdjoint)
    (hxx : ∀ i j,i ≠ j → x i*x j=0) (hcx : ∀ i,ElementCuntzSubequiv c (x i)) :
    CuntzSubequiv (diagonalCopies m c) (diagonalCopies 1 h) := by
  apply (copies_cuntz_fiberDiagonal hcx).trans
  apply (orthogonal_fiberDiagonal_cuntz_sum x (fun i => (hx i).1) hxx).trans
  exact elementCuntzSubequiv_of_hereditary (Finset.sum_nonneg (fun i _ => (hx i).1)) hh
    ((hereditarySubalgebra h hh.isSelfAdjoint).sum_mem (fun i _ => (hx i).2))

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_IrreducibleOrbits
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

lemma RepresentationIrreducible.cyclic {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hπ : RepresentationIrreducible π) {ξ : H} (hξ : ξ ≠ 0) :
    DenseRange (fun a : A => π a ξ) := by
  let l : A →ₗ[ℂ] H :=
    { toFun := fun a => π a ξ
      map_add' := by intro a b; simp
      map_smul' := by intro r a; simp }
  let S := l.range.topologicalClosure
  have hS : RepresentationInvariant π S := by
    intro a x hx
    change π a x ∈ closure (l.range : Set H)
    apply map_mem_closure (π a).continuous hx
    rintro _ ⟨b,rfl⟩
    exact ⟨a*b,by simp [l,map_mul]⟩
  obtain hs | hs := hπ S l.range.isClosed_topologicalClosure hS
  · have hm : ξ ∈ S := l.range.le_topologicalClosure ⟨1,by simp [l]⟩
    rw [hs,Submodule.mem_bot] at hm
    exact (hξ hm).elim
  · change Dense (l.range : Set H)
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hs

lemma RepresentationIrreducible.exists_mixed_nonzero {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hπ : RepresentationIrreducible π) {u v : A} (hu : π u ≠ 0) (hv : π v ≠ 0) :
    ∃ x : A,π (u*x*v) ≠ 0 := by
  by_contra! hn
  obtain ⟨ξ,hξ⟩ : ∃ ξ : H,π v ξ ≠ 0 := by
    by_contra! h
    exact hv (by ext ξ; exact h ξ)
  have hz : ∀ η : H,π u η=0 := isClosed_property (hπ.cyclic hξ)
    (isClosed_eq (π u).continuous continuous_const) (by
      intro a
      have hh := DFunLike.congr_fun (hn a) ξ
      simpa only [map_mul,mul_apply_eq_comp,zero_apply] using hh)
  exact hu (by ext η; exact hz η)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalConnection2
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

omit [PartialOrder A] [StarOrderedRing A] in
lemma irreducible_starLift {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : NonUnitalRepresentationIrreducible π) : RepresentationIrreducible (Unitization.starLift π) := by
  intro S hSc hS
  apply hπ S hSc
  intro a x hx
  simpa only [starLift_inr_apply] using hS (a : Unitization ℂ A) x hx

lemma exists_local_common_two {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : NonUnitalRepresentationIrreducible π) {h k : A}
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hhn : π h ≠ 0) (hkn : π k ≠ 0) :
    ∃ c : A,0 ≤ c ∧ c ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ π c ≠ 0 ∧
      ElementCuntzSubequiv c h ∧ ElementCuntzSubequiv c k := by
  let ρ := Unitization.starLift π
  obtain ⟨x,hx⟩ := (irreducible_starLift hπ).exists_mixed_nonzero
    (u := (h : Unitization ℂ A)) (v := (k : Unitization ℂ A)) (by simpa only [starLift_inr_apply] using hhn) (by simpa only [starLift_inr_apply] using hkn)
  let z : A := x.fst • (h*k)+h*x.snd*k
  have hz : π z ≠ 0 := by
    have he : (h : Unitization ℂ A)*x*(k : Unitization ℂ A)=(z : Unitization ℂ A) := by
      rw [← Unitization.inl_fst_add_inr_snd_eq x]
      simp only [mul_add,add_mul,Unitization.inr_mul_inl,← Unitization.inr_mul,smul_mul_assoc,← Unitization.inr_add]
      rfl
    rw [he] at hx
    simpa only [starLift_inr_apply] using hx
  have hzright : z ∈ principalRightIdeal h := by
    apply Submodule.le_topologicalClosure _
    refine ⟨x.fst • k+x.snd*k,?_⟩
    change h*(x.fst • k+x.snd*k)=z
    dsimp [z]
    rw [mul_add,mul_smul_comm,mul_assoc]
  have hzleft : star z ∈ principalRightIdeal k := by
    apply Submodule.le_topologicalClosure _
    refine ⟨star x.fst • h+star x.snd*h,?_⟩
    change k*(star x.fst • h+star x.snd*h)=star z
    simp only [z,star_add,star_smul,star_mul,hh.star_eq,hk.star_eq,mul_add,mul_smul_comm,mul_assoc]
  have hc : 0 ≤ z*star z := mul_star_self_nonneg z
  have hch := rightIdeal_square_mem_hereditary h z hh.isSelfAdjoint hzright
  have hck : star z*z ∈ hereditarySubalgebra k hk.isSelfAdjoint := by
    simpa only [star_star] using rightIdeal_square_mem_hereditary k (star z) hk.isSelfAdjoint hzleft
  refine ⟨z*star z,hc,hch,?_,elementCuntzSubequiv_of_hereditary hc hh hch,
    (element_range_cuntz_initial z).trans (elementCuntzSubequiv_of_hereditary (star_mul_self_nonneg z) hk hck)⟩
  intro he
  have he' : π z*star (π z)=0 := by simpa only [map_mul,map_star] using he
  exact hz ((CStarRing.mul_star_self_eq_zero_iff _).mp he')

lemma exists_local_common_family {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : NonUnitalRepresentationIrreducible π) {h : A}
    (hh : 0 ≤ h) (hhn : π h ≠ 0) {m : ℕ} (x : Fin m → A)
    (hx : ∀ i,0 ≤ x i ∧ π (x i) ≠ 0) :
    ∃ c : A,0 ≤ c ∧ c ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ π c ≠ 0 ∧
      ElementCuntzSubequiv c h ∧ ∀ i,ElementCuntzSubequiv c (x i) := by
  induction m generalizing h with
  | zero => exact ⟨h,hh,self_mem_hereditary h hh,hhn,cuntzSubequiv_refl _,by simp⟩
  | succ m ih =>
    obtain ⟨d,hd,hdh,hdn,hdch,hdx⟩ := exists_local_common_two hπ hh (hx 0).1 hhn (hx 0).2
    obtain ⟨c,hc,hcd,hcn,hccd,hct⟩ := ih hd hdn (fun i => x i.succ) (fun i => hx i.succ)
    refine ⟨c,hc,hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
      hd.isSelfAdjoint hdh hcd,hcn,hccd.trans hdch,?_⟩
    intro i
    exact Fin.cases (hccd.trans hdx) hct i

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_LocalCommon
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

lemma exists_local_common_element {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
    {h k : A} (hh : 0 ≤ h) (hk : 0 ≤ k) (hhn : π h ≠ 0) (hkn : π k ≠ 0) :
    ∃ c : A,0 ≤ c ∧ c ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ π c ≠ 0 ∧
      CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h) ∧
      CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k) := by
  obtain ⟨x,hx,hxx⟩ := exists_orthogonal_detected_family hn hpi π n hh hhn
  obtain ⟨y,hy,hyy⟩ := exists_orthogonal_detected_family hn hpi π n hk hkn
  obtain ⟨d,hd,hdh,hdn,-,hdx⟩ := exists_local_common_family hπ hh hhn x (fun i => (hx i).2)
  obtain ⟨c,hc,hcd,hcn,hccd,hcy⟩ := exists_local_common_family hπ hd hdn y (fun i => (hy i).2)
  refine ⟨c,hc,hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
    hd.isSelfAdjoint hdh hcd,hcn,?_,?_⟩
  · exact copies_cuntz_of_common_orthogonal hh x (fun i => ⟨(hx i).2.1,(hx i).1⟩)
      hxx (fun i => hccd.trans (hdx i))
  · exact copies_cuntz_of_common_orthogonal hk y (fun i => ⟨(hy i).2.1,(hy i).1⟩) hyy hcy

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

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma make_local_perturbationData {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
    (p q h k : A) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpn : ‖p‖ ≤ 1) (hqn : ‖q‖ ≤ 1)
    (hpq : p*q=0) (hh : 0 ≤ h) (hk : 0 ≤ k) (hph : p*h=h) (hqk : q*k=k)
    (hhn : π h ≠ 0) (hkn : π k ≠ 0) :
    ∃ F : OrthogonalPerturbationData A n,F.p=p ∧ F.q=q ∧ π (positiveCut F.α F.c) ≠ 0 := by
  obtain ⟨c,hc,-,hcn,hch,hck⟩ := exists_local_common_element hn hpi hπ hh hk hhn hkn
  let α := ‖π c‖/2
  have hα : 0 < α := by dsimp [α]; exact half_pos (norm_pos_iff.mpr hcn)
  let F : OrthogonalPerturbationData A n :=
    ⟨p,q,h,k,c,hpn,hqn,hp,hq,hpq,hh,hk,hc,hph,hqk,hch,hck,α,hα⟩
  refine ⟨F,rfl,rfl,?_⟩
  change π (positiveCut α c) ≠ 0
  rw [show π (positiveCut α c)=positiveCut α (π c) from
    π.map_cfcₙ (fun s : ℝ => max (s-α) 0) c (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hc.isSelfAdjoint (map_nonneg π hc).isSelfAdjoint]
  exact positiveCut_ne_zero_of_lt_norm (map_nonneg π hc) hα.le (by dsimp [α] <;> linarith [norm_pos_iff.mpr hcn])

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

lemma exists_core_perturbationData_oai {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
    {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u*v=0) (hun : π u ≠ 0) (hvn : π v ≠ 0) :
    ∃ F : OrthogonalPerturbationData A n,
      F.p ∈ hereditarySubalgebra u hu.isSelfAdjoint ∧
      F.q ∈ hereditarySubalgebra v hv.isSelfAdjoint ∧ π (positiveCut F.α F.c) ≠ 0 := by
  obtain ⟨p,hpD,h,hhD,hp,hpn,hh,hph,hhn⟩ := exists_supported_positive_core π hu hun
  obtain ⟨q,hqD,k,hkD,hq,hqn,hk,hqk,hkn⟩ := exists_supported_positive_core π hv hvn
  obtain ⟨F,hFp,hFq,hFc⟩ := make_local_perturbationData hn hpi hπ p q h k hp hq hpn hqn
    (mul_zero_of_hereditary hu.isSelfAdjoint hv.isSelfAdjoint huv hpD hqD)
    hh hk hph hqk hhn hkn
  exact ⟨F,by rwa [hFp],by rwa [hFq],hFc⟩

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.WeakPureInfiniteness.exists_core_perturbationData_oai.{u, v} := @OAI.WeakPureInfiniteness.exists_core_perturbationData_oai.{u, v}
