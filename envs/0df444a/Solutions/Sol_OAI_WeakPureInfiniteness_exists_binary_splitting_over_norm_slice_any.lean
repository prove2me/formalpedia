-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:21:58.871815+00:00
-- url     : https://prove2.me/submissions/a6b14836-8d3f-4546-a092-cda647a5fcd6

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_square_zero_on_norm_slice_of_gap_any
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_uniform_gap_any

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

lemma CuntzSubequiv.reindex_right {a : CStarMatrix m m A} {b : CStarMatrix n n A}
    (hab : CuntzSubequiv a b) (e : k ≃ n) : CuntzSubequiv a (matrixSubmatrix e e b) := by
  have h := (cuntzSubequiv_refl (matrixSubmatrix e e b)).submatrix_left e.symm
  have he : matrixSubmatrix e.symm e.symm (matrixSubmatrix e e b) = b := by
    ext i j
    simp only [matrixSubmatrix, Equiv.apply_symm_apply]
  rw [he] at h
  exact hab.trans h

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
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SquareZeroComparison
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

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma square_zero_two_copies {a x : A} (ha : 0 ≤ a)
    (hx : x ∈ hereditarySubalgebra a ha.isSelfAdjoint) (hxx : x*x=0) :
    CuntzSubequiv (diagonalCopies 2 (star x*x)) (diagonalCopies 1 a) := by
  let D := hereditarySubalgebra a ha.isSelfAdjoint
  have hx' : x ∈ D := hx
  have hxs : star x ∈ D := star_mem hx'
  have hz : star x*x ∈ D := D.mul_mem hxs hx'
  have hw : x*star x ∈ D := D.mul_mem hx' hxs
  have hzw : (star x*x)*(x*star x)=0 := by
    calc
      _ = star x*(x*x)*star x := by noncomm_ring
      _ = 0 := by rw [hxx,mul_zero,zero_mul]
  have hwz : (x*star x)*(star x*x)=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hzw
  let y : Fin 2 → A := ![star x*x,x*star x]
  apply copies_cuntz_of_common_orthogonal ha y
  · intro i
    fin_cases i
    · exact ⟨star_mul_self_nonneg x,hz⟩
    · exact ⟨mul_star_self_nonneg x,hw⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hzw
    · exact hwz
    · exact (hij rfl).elim
  · intro i
    fin_cases i
    · exact cuntzSubequiv_refl _
    · exact element_initial_cuntz_range x

lemma CuntzSubequiv.double_copies {r s : ℕ} {a b : A}
    (hab : CuntzSubequiv (diagonalCopies r a) (diagonalCopies s b)) :
    CuntzSubequiv (diagonalCopies (r+r) a) (diagonalCopies (s+s) b) := by
  have h := (hab.blockSum hab).submatrix_left
    (finSumFinEquiv.symm : Fin (r+r) → Fin r ⊕ Fin r)
  rw [diagonalCopies_double] at h
  have h' := h.reindex_right (finSumFinEquiv.symm : Fin (s+s) ≃ Fin s ⊕ Fin s)
  rwa [diagonalCopies_double] at h'

lemma CuntzSubequiv.power_two_binary {a b : A}
    (hab : CuntzSubequiv (diagonalCopies 2 a) (diagonalCopies 1 b)) (j : ℕ) :
    CuntzSubequiv (diagonalCopies (2^(j+1)) a) (diagonalCopies (2^j) b) := by
  induction j with
  | zero => exact hab
  | succ j ih =>
    have h := ih.double_copies
    have he : 2^(j+1+1)=2^(j+1)+2^(j+1) := by rw [pow_succ,Nat.mul_two]
    have hf : 2^(j+1)=2^j+2^j := by rw [pow_succ,Nat.mul_two]
    rw [he,hf]
    rw [hf] at h
    exact h

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

theorem exists_square_zero_on_norm_slice_any
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ x ∈ D,x*x=0 ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ → π x ≠ 0 := by
  obtain ⟨γ,hγ,hgap⟩ := exists_uniform_gap_any
  exact exists_square_zero_on_norm_slice_of_gap_any (σ := γ/2) (by positivity)
    (by linarith) hgap hA hn hpi D hD hb hα hlocal

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniverseIndividualInfiniteness
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

section UniverseOne

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_binary_splitting_over_norm_slice_any_oai
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∃ z : A,0 ≤ z ∧ CuntzSubequiv (diagonalCopies (2^j) z) (diagonalCopies 1 a) ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),r ≤ ‖π a‖ → π z ≠ 0 := by
  induction j with
  | zero =>
    refine ⟨a,ha,cuntzSubequiv_refl _,?_⟩
    intro H π hπ hnz
    rw [hnz,norm_zero] at hπ
    linarith
  | succ j ih =>
    obtain ⟨z,hz,hza,hzn⟩ := ih
    have hlocal : NonzeroOnNormSlice (hereditarySubalgebra z hz.isSelfAdjoint) a r := by
      intro H π _ hπa
      exact ⟨z,self_mem_hereditary z hz,hz,hzn H π hπa⟩
    obtain ⟨x,hx,hxx,hxn⟩ := exists_square_zero_on_norm_slice_any hA hn hpi
      (hereditarySubalgebra z hz.isSelfAdjoint) (hereditarySubalgebra_inner z hz.isSelfAdjoint) ha hr hlocal
    refine ⟨star x*x,star_mul_self_nonneg x,
      ((square_zero_two_copies hz hx hxx).power_two_binary j).trans hza,?_⟩
    intro H π hπa
    rw [map_mul,map_star]
    exact (CStarRing.star_mul_self_eq_zero_iff (π x)).not.mpr (hxn H π hπa)

end UniverseOne

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u} : type_of% @OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any_oai.{u} := @OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any_oai.{u}
