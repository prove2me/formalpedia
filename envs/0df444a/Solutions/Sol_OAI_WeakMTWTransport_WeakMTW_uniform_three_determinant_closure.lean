-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:59.488383+00:00
-- url     : https://prove2.me/submissions/963edbc1-37ec-48c1-8d2e-70b77b0ebe46

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A020
import Definitions.Def_OAIQ232A030
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_uniform_extended_spectral_comparison
import Theorems.Thm_OAI_WeakMTWTransport_uniform_endpoint_middle_singular_comparison

section
-- module Solutions.OAIQ232_BH.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) :=
  hmtw.global_support hv (active_hull_subset_normalSubdifferential hv x hp)

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
lemma continuous_twoMountain (x y₀ y₁ : M) : Continuous (twoMountain x y₀ y₁) :=
  (continuous_const.sub (continuous_cost_left y₀)).max (continuous_const.sub (continuous_cost_left y₁))

omit [CompactSpace M] [Nonempty M] in
lemma twoMountain_self (x y₀ y₁ : M) : twoMountain x y₀ y₁ x=0 := by simp [twoMountain]

lemma cTransform_eq_of_lower_mountain {f : M → ℝ} (hf : Continuous f)
    {x y : M} (hx : f x=0) (hm : ∀ z, cost x y-cost z y≤f z) :
    cTransform f y = -cost x y := by
  apply le_antisymm
  · rw [cTransform_le_iff hf]
    intro z
    rw [cost_symm y z]
    linarith [hm z]
  · have hh := cTransform_gap_nonneg hf y x
    rw [contactGap,cost_symm y x,hx] at hh
    linarith

lemma cTransform_twoMountain_left (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₀ = -cost x y₀ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_left _ _)

lemma cTransform_twoMountain_right (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₁ = -cost x y₁ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_right _ _)

lemma cTransform_cTransform_twoMountain (x y₀ y₁ : M) :
    cTransform (cTransform (twoMountain x y₀ y₁))=twoMountain x y₀ y₁ := by
  funext z
  apply le_antisymm (cTransform_cTransform_le (continuous_twoMountain x y₀ y₁) z)
  apply max_le
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₀
    rw [contactGap,cTransform_twoMountain_left] at h
    linarith
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₁
    rw [contactGap,cTransform_twoMountain_right] at h
    linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ConvexBarycentricSegment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set

namespace WeakMTWTransport

lemma convex_barycentric_segment {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] {G : Set E} (hG : Convex ℝ G) (w : ι → ℝ) (v : ι → E)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i,w i=1) (hv : ∀ i,v i∈G)
    (i : ι) {μ : ℝ} (hμ : 0 ≤ μ) (hi : μ ≤ w i) (t : ℝ) (ht : t∈Icc (-μ) 1) :
    (∑ j,w j • v j)+t • (v i-∑ j,w j • v j)∈G := by
  classical
  let a : ι → ℝ := fun j => (1-t)*w j+if j=i then t else 0
  have ha (j : ι) (_hj : j∈Finset.univ) : 0 ≤ a j := by
    dsimp only [a]
    by_cases hj : j=i
    · rw [ite_eq_left hj,hj]
      by_cases h0 : 0 ≤ t
      · exact add_nonneg (mul_nonneg (by linarith [ht.2]) (hw i)) h0
      · have ht0 : t<0 := lt_of_not_ge h0
        nlinarith [mul_nonneg (neg_nonneg.mpr ht0.le) (hμ.trans hi),ht.1]
    · rw [ite_eq_right hj,add_zero]
      exact mul_nonneg (by linarith [ht.2]) (hw j)
  have has : ∑ j,a j=1 := by
    simp only [a,Finset.sum_add_distrib,←Finset.mul_sum,hs,mul_one]
    simp
  have HH := hG.sum_mem (t := Finset.univ) ha has (fun j _ => hv j)
  have he : (∑ j,a j • v j)=(∑ j,w j • v j)+t • (v i-∑ j,w j • v j) := by
    simp only [a,add_smul,mul_smul,Finset.sum_add_distrib,←Finset.smul_sum,
      ite_smul,zero_smul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
    module
  rwa [he] at HH
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiberNormal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma outward_inner_ratio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p e : E} {t D κ L : ℝ} (he : ‖e‖=1) (ht : 0<t)
    (hh : 0 < inner ℝ p e) (hκ : 0<κ) (hL : 0<L)
    (hhD : κ*D ≤ (inner ℝ p e)^2)
    (hgap : ‖p+t • e‖^2-‖p‖^2 ≤ L*D) :
    0 < inner ℝ p (t • e) ∧ ‖t • e‖^2/inner ℝ p (t • e) ≤ L/(2*κ) := by
  have hN : ‖t • e‖=t := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,he,mul_one]
  have hI : inner ℝ p (t • e)=t*inner ℝ p e := by simp only [real_inner_smul_right]
  refine ⟨by rw [hI]; exact mul_pos ht hh,?_⟩
  rw [norm_add_sq_real,hN,hI] at hgap
  have H1 := mul_le_mul_of_nonneg_left hgap hκ.le
  have H2 := mul_le_mul_of_nonneg_left hhD hL.le
  have hT : 2*κ*t ≤ L*inner ℝ p e := by
    nlinarith only [H1,H2,hh,mul_nonneg hκ.le (sq_nonneg t)]
  have hr : ‖t • e‖^2/inner ℝ p (t • e)=t/inner ℝ p e := by
    rw [hN,hI]
    field_simp
  rw [hr,div_le_div_iff₀ hh (show 0<2*κ by positivity)]
  nlinarith only [hT]

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MinMax
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section MinMax
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma paired_basis_slice {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    ∃ v : E, v ≠ 0 ∧ (∀ j : Fin n, i < j → a.repr v j = 0) ∧
      (∀ j : Fin n, j < i → b.repr v j = 0) :=  by
  classical
  let f : Fin (i.val+1) → Fin n :=  fun j  => ⟨j.val,by omega⟩
  have hf : Function.Injective f :=  by
    intro j k h
    apply Fin.ext
    simpa only [f] using congrArg (fun z : Fin n => z.val) h
  let V :=  Submodule.span ℝ (range (fun j : Fin (i.val+1)  => a (f j)))
  have hdim : Module.finrank ℝ V = i.val+1 :=  by
    exact (finrank_span_eq_card (a.toBasis.linearIndependent.comp f hf)).trans (Fintype.card_fin _)
  let L : V →ₗ[ℝ] (Fin i.val → ℝ) :=
    { toFun :=  fun v j  => b.repr v ⟨j.val,lt_trans j.isLt i.isLt⟩
      map_add' :=  by intros; ext j; simp
      map_smul' :=  by intros; ext j; simp }
  have hk :=  LinearMap.ker_ne_bot_of_finrank_lt (f :=  L) (by
    rw [hdim,Module.finrank_pi,Fintype.card_fin]; omega)
  obtain ⟨v,hv,hv0⟩ :=  (Submodule.ne_bot_iff _).mp hk
  have hvE : (v:E) ≠ 0 :=  by
    intro h
    exact hv0 (Subtype.ext h)
  refine ⟨v,hvE,?_,?_⟩
  · intro j hj
    have H : ∀ w∈V, a.repr w j = 0 :=  by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw  =>
          obtain ⟨k,rfl⟩ :=  hw
          have hne : f k ≠ j :=  by intro h; have :=  congrArg Fin.val h; dsimp [f] at this; omega
          simp [Ne.symm hne]
      | zero  => simp
      | add x y hx hy ihx ihy  => simp [ihx,ihy]
      | smul c x hx ih  => simp [ih]
    exact H v v.property
  · intro j hj
    have H :=  congrFun (show L v = 0 from hv) (⟨j.val,hj⟩ : Fin i.val)
    exact H

lemma eigenvalue_quadratic_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (v : E) :
    inner ℝ (A v) v = ∑ j, hA.eigenvalues hn j*((hA.eigenvectorBasis hn).repr v j)^2 :=  by
  have H :=  (hA.eigenvectorBasis hn).repr.inner_map_map (A v) v
  rw [←H,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.inner_apply,conj_trivial,RCLike.ofReal_real_eq_id,id_eq]
  ring

omit [FiniteDimensional ℝ E] in
lemma eigenbasis_norm_expansion {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (v : E) :
    ‖v‖^2 = ∑ j, (b.repr v j)^2 :=  by
  rw [←b.repr.norm_map v,EuclideanSpace.real_norm_sq_eq]

lemma ordered_eigenvalue_quadratic_comparison {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ v, inner ℝ (A v) v ≤ a*inner ℝ (B v) v+b*‖v‖^2)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    hA.eigenvalues hn i ≤ a*hB.eigenvalues hn i+b :=  by
  obtain ⟨v,hv,hav,hbv⟩ :=  paired_basis_slice (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn) i
  have hAv : hA.eigenvalues hn i*‖v‖^2 ≤ inner ℝ (A v) v :=  by
    rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hji) (sq_nonneg _)
    · rw [hav j (lt_of_not_ge hji)]; simp
  have hBv : inner ℝ (B v) v ≤ hB.eigenvalues hn i*‖v‖^2 :=  by
    rw [eigenvalue_quadratic_expansion hB hn,eigenbasis_norm_expansion (hB.eigenvectorBasis hn),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hB.eigenvalues_antitone hn hij) (sq_nonneg _)
    · rw [hbv j (lt_of_not_ge hij)]; simp
  have H := h v
  have Hmul := mul_le_mul_of_nonneg_left hBv ha
  have hpos : 0 < ‖v‖^2 :=  sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  nlinarith

end MinMax
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormMinMax
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section NormMinMax
variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ F] in
lemma paired_basis_slice_map {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : OrthonormalBasis (Fin n) ℝ F) (K : E →ₗ[ℝ] F) (i : Fin n) :
    ∃ v : E, v ≠ 0 ∧ (∀ j : Fin n, i < j → a.repr v j = 0) ∧
      (∀ j : Fin n, j < i → b.repr (K v) j = 0) :=  by
  classical
  let f : Fin (i.val+1) → Fin n :=  fun j  => ⟨j.val,by omega⟩
  have hf : Function.Injective f :=  by
    intro j k h
    apply Fin.ext
    simpa only [f] using congrArg (fun z : Fin n => z.val) h
  let V :=  Submodule.span ℝ (range (fun j : Fin (i.val+1)  => a (f j)))
  have hdim : Module.finrank ℝ V = i.val+1 :=  by
    exact (finrank_span_eq_card (a.toBasis.linearIndependent.comp f hf)).trans (Fintype.card_fin _)
  let L : V →ₗ[ℝ] (Fin i.val → ℝ) :=
    { toFun :=  fun v j  => b.repr (K v) ⟨j.val,lt_trans j.isLt i.isLt⟩
      map_add' :=  by intros; ext j; simp
      map_smul' :=  by intros; ext j; simp }
  have hk :=  LinearMap.ker_ne_bot_of_finrank_lt (f :=  L) (by
    rw [hdim,Module.finrank_pi,Fintype.card_fin]; omega)
  obtain ⟨v,hv,hv0⟩ :=  (Submodule.ne_bot_iff _).mp hk
  have hvE : (v:E) ≠ 0 :=  by
    intro h
    exact hv0 (Subtype.ext h)
  refine ⟨v,hvE,?_,?_⟩
  · intro j hj
    have H : ∀ w∈V, a.repr w j = 0 :=  by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw  =>
          obtain ⟨k,rfl⟩ :=  hw
          have hne : f k ≠ j :=  by intro h; have :=  congrArg Fin.val h; dsimp [f] at this; omega
          simp [Ne.symm hne]
      | zero  => simp
      | add x y hx hy ihx ihy  => simp [ihx,ihy]
      | smul c x hx ih  => simp [ih]
    exact H v v.property
  · intro j hj
    have H :=  congrFun (show L v = 0 from hv) (⟨j.val,hj⟩ : Fin i.val)
    exact H

lemma quadratic_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, i < j → (hA.eigenvectorBasis hn).repr v j = 0) :
    hA.eigenvalues hn i * ‖v‖^2 ≤ inner ℝ (A v) v := by
  rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hji) (sq_nonneg _)
  · rw [hv j (lt_of_not_ge hji)]; simp

lemma quadratic_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, j < i → (hA.eigenvectorBasis hn).repr v j = 0) :
    inner ℝ (A v) v ≤ hA.eigenvalues hn i * ‖v‖^2 := by
  rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hij) (sq_nonneg _)
  · rw [hv j (lt_of_not_ge hij)]; simp

lemma ordered_eigenvalue_pullback_comparison {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
    (hA : A.IsSymmetric) (hB : B.IsPositive) (K : E →ₗ[ℝ] F)
    {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hK : ∀ v, ‖K v‖ ≤ c * ‖v‖)
    (h : ∀ v, inner ℝ (A v) v ≤ a * inner ℝ (B (K v)) (K v) + b * ‖v‖^2)
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
    hA.eigenvalues hnE i ≤ a * c^2 * hB.isSymmetric.eigenvalues hnF i + b := by
  obtain ⟨v,hv,hav,hbv⟩ := paired_basis_slice_map (hA.eigenvectorBasis hnE)
    (hB.isSymmetric.eigenvectorBasis hnF) K i
  have hAv := quadratic_lower_spectral_slice hA hnE i v hav
  have hBv := quadratic_upper_spectral_slice hB.isSymmetric hnF i (K v) hbv
  have hBp := hB.nonneg_eigenvalues hnF i
  have hnorm := sq_le_sq₀ (norm_nonneg (K v)) (mul_nonneg hc (norm_nonneg v)) |>.mpr (hK v)
  have hmul := mul_le_mul_of_nonneg_left hnorm hBp
  have hmul' := mul_le_mul_of_nonneg_left (hBv.trans hmul) ha
  have hpos : 0 < ‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  have H := h v
  nlinarith

lemma ordered_singularValues_pullback {A : E →ₗ[ℝ] G} {B : F →ₗ[ℝ] H}
    (K : E →ₗ[ℝ] F) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hK : ∀ v, ‖K v‖ ≤ c * ‖v‖) (h : ∀ v, ‖A v‖ ≤ a * ‖B (K v)‖)
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n)
    (i : Fin n) : A.singularValues i ≤ a * c * B.singularValues i := by
  have H := ordered_eigenvalue_pullback_comparison A.isSymmetric_adjoint_comp_self
    B.isPositive_adjoint_comp_self K (sq_nonneg a) hc hK (b := 0) (fun v => by
      simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq,
        zero_mul,add_zero]
      nlinarith [h v,norm_nonneg (A v),norm_nonneg (B (K v))]) hnE hnF i
  rw [←A.sq_singularValues_fin hnE,←B.sq_singularValues_fin hnF] at H
  have hAp := A.singularValues_nonneg i
  have hBp := B.singularValues_nonneg i
  have hprod := mul_nonneg (mul_nonneg ha hc) hBp
  nlinarith

end NormMinMax
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveSingular
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace WeakMTWTransport
section PositiveSingular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma eigenbasis_operator_norm_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (v : E) :
    ‖A v‖^2 = ∑ j, (hA.eigenvalues hn j)^2*((hA.eigenvectorBasis hn).repr v j)^2 := by
  rw [eigenbasis_norm_expansion (hA.eigenvectorBasis hn)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id,id_eq,mul_pow]

lemma positive_norm_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, i < j → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    (hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2≤‖A v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn i)
      (hA.isSymmetric.eigenvalues_antitone hn hji) 2
  · rw [hv j (lt_of_not_ge hji)]; simp

lemma positive_norm_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, j < i → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    ‖A v‖^2≤(hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn j)
      (hA.isSymmetric.eigenvalues_antitone hn hij) 2
  · rw [hv j (lt_of_not_ge hij)]; simp

lemma positive_singularValues_eq_eigenvalues {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    A.singularValues i=hA.isSymmetric.eigenvalues hn i := by
  have hG := A.isSymmetric_adjoint_comp_self
  have hApos := hA.nonneg_eigenvalues hn i
  have hspos := A.singularValues_nonneg i
  apply le_antisymm
  · obtain ⟨v,hv,hgv,hav⟩ := paired_basis_slice (hG.eigenvectorBasis hn)
      (hA.isSymmetric.eigenvectorBasis hn) i
    have h1 := quadratic_lower_spectral_slice hG hn i v hgv
    have h2 := positive_norm_upper_spectral_slice hA hn i v hav
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h1
    rw [←A.sq_singularValues_fin hn] at h1
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith
  · obtain ⟨v,hv,hav,hgv⟩ := paired_basis_slice (hA.isSymmetric.eigenvectorBasis hn)
      (hG.eigenvectorBasis hn) i
    have h1 := positive_norm_lower_spectral_slice hA hn i v hav
    have h2 := quadratic_upper_spectral_slice hG hn i v hgv
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h2
    rw [←A.sq_singularValues_fin hn] at h2
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith

end PositiveSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SpectralContinuity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Filter
open scoped Topology

namespace WeakMTWTransport
section SpectralContinuity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ordered_eigenvalues_positive_crossing {A B : E →L[ℝ] E}
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {c C : ℝ}
    (h : ∀ v, c*‖v‖^2 ≤ inner ℝ (B v) v-inner ℝ (A v) v ∧
      inner ℝ (B v) v-inner ℝ (A v) v ≤ C*‖v‖^2)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    hA.eigenvalues hn i+c ≤ hB.eigenvalues hn i ∧
      hB.eigenvalues hn i ≤ hA.eigenvalues hn i+C := by
  have H1 := ordered_eigenvalue_quadratic_comparison hA hB (a := 1) (b := -c)
    (by norm_num) (fun v => by have := (h v).1; change inner ℝ (A v) v ≤ 1*inner ℝ (B v) v+(-c)*‖v‖^2; linarith) hn i
  have H2 := ordered_eigenvalue_quadratic_comparison hB hA (a := 1) (b := C)
    (by norm_num) (fun v => by have := (h v).2; change inner ℝ (B v) v ≤ 1*inner ℝ (A v) v+C*‖v‖^2; linarith) hn i
  constructor <;> linarith

end SpectralContinuity
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_5
lemma uniform_middle_ordered_crossing :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      ∀ hz : z.2 ∈ minimizingVectors z.1, ∀ δ : ℝ, ∀ hd : 0 ≤ δ, ∀ hdhalf : δ ≤ 1/2,
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) (sprayFlow (1/4) z).1)),
      (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
        (show (0:ℝ) ≤ 1/2 by norm_num)).isSymmetric.eigenvalues rfl i + c*δ ≤
        (shortened_middle_operator_positive hz hd hdhalf).isSymmetric.eigenvalues rfl i ∧
      (shortened_middle_operator_positive hz hd hdhalf).isSymmetric.eigenvalues rfl i ≤
        (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
          (show (0:ℝ) ≤ 1/2 by norm_num)).isSymmetric.eigenvalues rfl i + C*δ := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middleHessian_crossing (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd hdhalf i
  apply ordered_eigenvalues_positive_crossing
  intro v
  simpa only [inner_middleHessianOperator,sub_zero,mul_assoc] using H z hz δ hd hdhalf v

end MiddleSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MiddleScaling
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleScaling
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleHessian_scaled_ray (z : TangentBundle 𝓘(ℝ,Model n) M)
    (h T : ℝ) (hT : T ≠ 0) :
    HEq (middleHessian (tangentScale T z) (h/T) 1) (T • middleHessian z h T) := by
  unfold middleHessian
  rw [sprayFlow_scale,mul_div_cancel₀ _ hT]
  change HEq
    ((h/T)⁻¹ • normalHessian (sprayFlow h z).1 (-(h/T) • (T • (sprayFlow h z).2)) +
      (1-h/T)⁻¹ • normalHessian (sprayFlow h z).1 ((1-h/T) • (T • (sprayFlow h z).2)))
    (T • (h⁻¹ • normalHessian (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) +
      (T-h)⁻¹ • normalHessian (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2)))
  simp only [smul_smul]
  have h1 : -(h/T)*T = -h := by field_simp
  have h2 : (1-h/T)*T = T-h := by field_simp
  rw [h1,h2]
  apply heq_of_eq
  ext v w
  simp only [add_apply,smul_apply,smul_eq_mul]
  have h3 : (h/T)⁻¹ = T*h⁻¹ := by simp [div_eq_mul_inv]
  have h4 : (1-h/T)⁻¹ = T*(T-h)⁻¹ := by
    rw [show 1-h/T=(T-h)/T by field_simp]
    simp [div_eq_mul_inv]
  rw [h3,h4]
  ring

end MiddleScaling
end WeakMTWTransport

end

end

section

noncomputable section
namespace WeakMTWTransport
section SpectralScaling
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma ordered_singularValues_positive_smul (A : E →ₗ[ℝ] F) {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    (t • A).singularValues i = t * A.singularValues i := by
  have h1 := ordered_singularValues_pullback (A := t • A) (B := A)
    (LinearMap.id) ht.le (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1*‖v‖; simp)
    (fun v => by simp only [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_pos ht,LinearMap.id_apply]; exact le_rfl) hn hn i
  have h2 := ordered_singularValues_pullback (A := A) (B := t • A)
    (LinearMap.id) (inv_nonneg.mpr ht.le) (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1*‖v‖; simp)
    (fun v => by simp only [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_pos ht,LinearMap.id_apply]; rw [←mul_assoc,inv_mul_cancel₀ ht.ne',one_mul]) hn hn i
  simp only [mul_one] at h1 h2
  apply le_antisymm h1
  have H := mul_le_mul_of_nonneg_left h2 ht.le
  simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] using H
end SpectralScaling
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearSingular_heq {x y : M} (hxy : x=y)
    {B : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ}
    {C : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ}
    (hBC : HEq B C) (i : ℕ) :
    intrinsicBilinearSingular x B i=intrinsicBilinearSingular y C i := by
  subst y
  cases hBC
  rfl

local instance localInst_r7161c1_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearOperator_smul (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)
    (t : ℝ) : intrinsicBilinearOperator y (t • B)=t • intrinsicBilinearOperator y B := by
  ext v
  simp only [intrinsicBilinearOperator,comp_apply,smul_apply,map_smul]

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearSingular_pos_smul (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) (i : Fin (Module.finrank ℝ (Model n))) :
    intrinsicBilinearSingular y (t • B) i=t*intrinsicBilinearSingular y B i := by
  unfold intrinsicBilinearSingular
  rw [intrinsicBilinearOperator_smul]
  exact ordered_singularValues_positive_smul (intrinsicBilinearOperator y B).toLinearMap ht rfl i

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleSingularValue_scaled_ray (z : TangentBundle 𝓘(ℝ,Model n) M)
    (h T : ℝ) (hT : 0 < T) (i : Fin (Module.finrank ℝ (Model n))) :
    middleSingularValue (tangentScale T z) (h/T) 1 i = T*middleSingularValue z h T i := by
  have hbase : (sprayFlow (h/T) (tangentScale T z)).1=(sprayFlow h z).1 := by
    rw [sprayFlow_scale,mul_div_cancel₀ _ hT.ne']
    rfl
  have H := intrinsicBilinearSingular_heq hbase (middleHessian_scaled_ray z h T hT.ne') i
  change middleSingularValue (tangentScale T z) (h/T) 1 i = _ at H
  rw [H,intrinsicBilinearSingular_pos_smul _ _ hT]
  rfl

end MiddleSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_RadialSingular
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section RadialSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_8
lemma uniform_middle_singular_crossing :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2 ∈ minimizingVectors z.1 → ∀ δ ∈ Icc (0:ℝ) (1/2),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      middleSingularValue z (1/4) 1 i+c*δ ≤ middleSingularValue z (1/4) (1-δ) i ∧
      middleSingularValue z (1/4) (1-δ) i ≤ middleSingularValue z (1/4) 1 i+C*δ := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middle_ordered_crossing (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd i
  have h0 := positive_singularValues_eq_eigenvalues
    (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num)) rfl i
  have h1 := positive_singularValues_eq_eigenvalues
    (shortened_middle_operator_positive hz hd.1 hd.2) rfl i
  simp only [sub_zero] at h0
  change middleSingularValue z (1/4) 1 i = _ at h0
  change middleSingularValue z (1/4) (1-δ) i = _ at h1
  simpa only [h0,h1,sub_zero] using H z hz δ hd.1 hd.2 i

lemma uniform_radial_singular_shortening :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ δ ∈ Icc (0:ℝ) (1/2),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      c*((endpointExpDifferential x p).toLinearMap.singularValues i+δ) ≤
        (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i ∧
      (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i ≤
        C*((endpointExpDifferential x p).toLinearMap.singularValues i+δ) := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_endpoint_middle_singular_comparison (n := n) (M := M)
  obtain ⟨l,u,hl,hu,J⟩ := uniform_middle_singular_crossing (n := n) (M := M)
  refine ⟨1/(2*a*(b+1/l)),b*(a+u),div_pos (by norm_num)
    (by positivity),mul_pos hb (add_pos ha hu),?_⟩
  intro x p hp δ hd i
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let T := 1-δ
  have hT : 0 < T := by dsimp [T] <;> linarith [hd.2]
  have hT1 : T ≤ 1 := by dsimp [T] <;> linarith [hd.1]
  have hThalf : (1/2:ℝ) ≤ T := by dsimp [T] <;> linarith [hd.2]
  have ht : (1/4:ℝ)/T ∈ Icc (1/4:ℝ) (3/4) := by
    constructor
    · rw [le_div_iff₀ hT]; nlinarith
    · rw [div_le_iff₀ hT]; nlinarith
  have H0 := H x p hp (1/4) (by constructor <;> norm_num) i
  have H1 := H x (T • p) (minimizingVectors_smul hp hT.le hT1) ((1/4)/T) ht i
  have HS := middleSingularValue_scaled_ray z (1/4) T hT i
  change middleSingularValue (⟨x,T • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) ((1/4)/T) 1 i = _ at HS
  rw [HS] at H1
  have J1 := J z hp δ hd i
  let S := (endpointExpDifferential x p).toLinearMap.singularValues i
  let R := (endpointExpDifferential x (T • p)).toLinearMap.singularValues i
  let d0 := middleSingularValue z (1/4) 1 i
  let d1 := middleSingularValue z (1/4) T i
  change S ≤ b*d0 ∧ d0 ≤ a*S at H0
  change R ≤ b*(T*d1) ∧ T*d1 ≤ a*R at H1
  change d0+l*δ ≤ d1 ∧ d1 ≤ d0+u*δ at J1
  have hd0 : 0 ≤ d0 := (middleHessianOperator z (1/4) 1).toLinearMap.singularValues_nonneg i
  have hd1 : 0 ≤ d1 := (middleHessianOperator z (1/4) T).toLinearMap.singularValues_nonneg i
  have hS : 0 ≤ S := (endpointExpDifferential x p).toLinearMap.singularValues_nonneg i
  have hR : 0 ≤ R := (endpointExpDifferential x (T • p)).toLinearMap.singularValues_nonneg i
  have hlowD : d1 ≤ 2*a*R := by
    have hh := mul_le_mul_of_nonneg_right hThalf hd1
    nlinarith [H1.2]
  have hupD : d1 ≤ a*S+u*δ := J1.2.trans (add_le_add H0.2 le_rfl)
  have hSle : S ≤ b*d1 := H0.1.trans (mul_le_mul_of_nonneg_left
    (by nlinarith [J1.1,mul_nonneg hl.le hd.1]) hb.le)
  have hdle : δ ≤ (1/l)*d1 := by
    rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
    nlinarith [J1.1]
  constructor
  · change (1/(2*a*(b+1/l)))*(S+δ) ≤ R
    rw [one_div,mul_comm,←div_eq_mul_inv,div_le_iff₀ (by positivity : 0 < 2*a*(b+1/l))]
    calc
      S+δ ≤ (b+1/l)*d1 := by nlinarith only [hSle,hdle]
      _ ≤ (b+1/l)*(2*a*R) := mul_le_mul_of_nonneg_left hlowD (by positivity)
      _ = R*(2*a*(b+1/l)) := by ring
  · change R ≤ b*(a+u)*(S+δ)
    have hh := mul_le_mul_of_nonneg_right hT1 hd1
    have hh2 := H1.1.trans (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hh) hb.le)
    calc
      R ≤ b*d1 := hh2
      _ ≤ b*(a*S+u*δ) := mul_le_mul_of_nonneg_left hupD hb.le
      _ ≤ b*(a+u)*(S+δ) := by
        have h1 := mul_nonneg ha.le hd.1
        have h2 := mul_nonneg hu.le hS
        nlinarith [mul_nonneg hb.le h1,mul_nonneg hb.le h2]

end RadialSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_DoubleMountain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_left {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₀ : p₀∈minimizingVectors x) :
    p₀∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₀,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_left]
  ring

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_right {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₁ : p₁∈minimizingVectors x) :
    p₁∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₁,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_right]
  ring

lemma WeakMTW.double_mountain (hmtw : WeakMTW (n := n) (M := M)) {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x}
    (hp₀ : p₀∈minimizingVectors x) (hp₁ : p₁∈minimizingVectors x)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    a • p₀+b • p₁∈minimizingVectors x ∧ ∀ z : M,
      cost x (riemannianExp x (a • p₀+b • p₁))-cost z (riemannianExp x (a • p₀+b • p₁)) ≤
        max (cost x (riemannianExp x p₀)-cost z (riemannianExp x p₀))
          (cost x (riemannianExp x p₁)-cost z (riemannianExp x p₁)) := by
  let f := twoMountain x (riemannianExp x p₀) (riemannianExp x p₁)
  have hp : a • p₀+b • p₁∈convexHull ℝ (activeLogs (n := n) (cTransform f) x) :=
    (convex_convexHull _ _)
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_left hp₀))
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_right hp₁)) ha hb hab
  obtain ⟨hmin,hsup⟩ := hmtw.active_hull_global_support
    (continuous_cTransform (continuous_twoMountain x _ _)) hp
  refine ⟨hmin,?_⟩
  intro z
  have hh := hsup z
  rw [cTransform_cTransform_twoMountain,twoMountain_self] at hh
  change 0+cost x (riemannianExp x (a • p₀+b • p₁))≤
    twoMountain x (riemannianExp x p₀) (riemannianExp x p₁) z+
      cost z (riemannianExp x (a • p₀+b • p₁)) at hh
  exact sub_le_iff_le_add.mpr (by simpa only [zero_add,twoMountain] using hh)

lemma WeakMTW.convex_minimizingVectors (hmtw : WeakMTW (n := n) (M := M)) (x : M) :
    Convex ℝ (minimizingVectors (n := n) x) := by
  intro p hp q hq a b ha hb hab
  exact (hmtw.double_mountain hp hq ha hb hab).1
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_SpectralDeterminants
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SpectralDeterminants
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_15
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma expJacobian_eq_prod_singularValues (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    expJacobian x p = ∏ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential x p).toLinearMap.singularValues i := by
  change (endpointExpDifferential x p).toLinearMap.normDet=_
  rw [LinearMap.normDet_eq_prod_singularValues,Fin.prod_univ_eq_prod_range]
  rfl

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma expJacobian_comparison_of_singularValues {x : M}
    {p q : TangentSpace 𝓘(ℝ,Model n) x} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : Fin (Module.finrank ℝ (Model n)),
      c*(endpointExpDifferential x p).toLinearMap.singularValues i ≤
        (endpointExpDifferential x q).toLinearMap.singularValues i) :
    c^Module.finrank ℝ (Model n)*expJacobian x p ≤ expJacobian x q := by
  rw [expJacobian_eq_prod_singularValues,expJacobian_eq_prod_singularValues]
  have HH := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (Model n)))))
    (fun i _ => mul_nonneg hc ((endpointExpDifferential x p).toLinearMap.singularValues_nonneg i))
    (fun i _ => h i)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using HH

lemma uniform_radial_expJacobian_comparison :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ θ∈Icc (1/2:ℝ) 1,
      c*expJacobian x p ≤ expJacobian x (θ • p) := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_radial_singular_shortening (n := n) (M := M)
  refine ⟨a^Module.finrank ℝ (Model n),pow_pos ha _,?_⟩
  intro x p hp θ ht
  apply expJacobian_comparison_of_singularValues ha.le
  intro i
  have HH := (H x p hp (1-θ) (by constructor <;> linarith [ht.1,ht.2]) i).1
  rw [show (1:ℝ)-(1-θ)=θ by ring] at HH
  have hm := mul_nonneg ha.le (show 0 ≤ 1-θ by linarith [ht.2])
  nlinarith only [HH,hm]

lemma WeakMTW.uniform_extended_expJacobian_comparison
    (hmtw : WeakMTW (n := n) (M := M)) {a B : ℝ} (ha : 0<a) (hB : 0<B) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q ≤ B →
      (∀ t∈Icc (-a) 1,p+t • q∈minimizingVectors x) →
      c*expJacobian x (p+q) ≤ expJacobian x p := by
  obtain ⟨c,hc,H⟩ := hmtw.uniform_extended_spectral_comparison ha hB
  exact ⟨c^Module.finrank ℝ (Model n),pow_pos hc _,fun x p q hpq hB hline =>
    expJacobian_comparison_of_singularValues hc.le (H x p q hpq hB hline)⟩
end SpectralDeterminants
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ReverseSpectrum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ReverseSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_16
omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma sprayFlow_reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) (t : ℝ) :
    sprayFlow t (reverseRay z)=tangentScale (-1) (sprayFlow (1-t) z) := by
  rw [reverseRay,sprayFlow_scale,←sprayFlow_add]
  congr 2
  ring

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleHessian_reverse_half (z : TangentBundle 𝓘(ℝ,Model n) M) :
    HEq (middleHessian (reverseRay z) (1/2) 1) (middleHessian z (1/2) 1) := by
  unfold middleHessian
  rw [sprayFlow_reverseRay]
  rw [show (1:ℝ)-1/2=1/2 by norm_num]
  change HEq
    ((1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((-(1/2:ℝ)) • ((-1:ℝ) • (sprayFlow (1/2) z).2))+
      (1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((1/2:ℝ) • ((-1:ℝ) • (sprayFlow (1/2) z).2)))
    ((1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((-(1/2:ℝ)) • (sprayFlow (1/2) z).2)+
      (1/2:ℝ)⁻¹ • normalHessian (sprayFlow (1/2) z).1
        ((1/2:ℝ) • (sprayFlow (1/2) z).2))
  apply heq_of_eq
  simp only [smul_smul]
  norm_num only
  ext v w
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleSingularValue_reverse_half (z : TangentBundle 𝓘(ℝ,Model n) M) (i : ℕ) :
    middleSingularValue (reverseRay z) (1/2) 1 i=middleSingularValue z (1/2) 1 i := by
  have hb : (sprayFlow (1/2:ℝ) (reverseRay z)).1=(sprayFlow (1/2:ℝ) z).1 := by
    rw [sprayFlow_reverseRay]
    norm_num only
    rfl
  exact intrinsicBilinearSingular_heq hb (middleHessian_reverse_half z) i

lemma uniform_reverse_singular_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential (reverseRay z).1 (reverseRay z).2).toLinearMap.singularValues i ≤
        C*(endpointExpDifferential z.1 z.2).toLinearMap.singularValues i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_endpoint_middle_singular_comparison (n := n) (M := M)
  refine ⟨C*c,mul_pos hC hc,?_⟩
  intro z hz i
  have h0 := (H z.1 z.2 hz (1/2) (by constructor <;> norm_num) i).2
  have h1 := (H (reverseRay z).1 (reverseRay z).2 (reverseRay_minimizing hz)
    (1/2) (by constructor <;> norm_num) i).1
  change _ ≤ C*middleSingularValue (reverseRay z) (1/2) 1 i at h1
  change middleSingularValue z (1/2) 1 i ≤ _ at h0
  rw [middleSingularValue_reverse_half] at h1
  exact h1.trans ((mul_le_mul_of_nonneg_left h0 hC.le).trans_eq (mul_assoc _ _ _).symm)

lemma uniform_reverse_expJacobian_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → expJacobian (reverseRay z).1 (reverseRay z).2 ≤
        C*expJacobian z.1 z.2 := by
  obtain ⟨C,hC,H⟩ := uniform_reverse_singular_comparison (n := n) (M := M)
  refine ⟨C ^ Module.finrank ℝ (Model n),pow_pos hC _,?_⟩
  intro z hz
  rw [expJacobian_eq_prod_singularValues,expJacobian_eq_prod_singularValues]
  have HH := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (Model n)))))
    (fun i _ => (endpointExpDifferential (reverseRay z).1 (reverseRay z).2).toLinearMap.singularValues_nonneg i)
    (fun i _ => H z hz i)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using HH
end ReverseSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_OutwardSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section OutwardSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance outwardSpectrumFiniteDimensionalTangentSpace_r7161c1_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma WeakMTW.uniform_outward_expJacobian_comparison
    (hmtw : WeakMTW (n := n) (M := M)) {μ κ L : ℝ}
    (hμ : 0<μ) (hκ : 0<κ) (hL : 0<L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ι : Type) [Fintype ι] (x : M)
      (v : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
      (p : TangentSpace 𝓘(ℝ,Model n) x),
      (∀ j,0 ≤ w j) → (∑ j,w j=1) → (∀ j,v j∈minimizingVectors x) →
      p=∑ j,w j • v j → ∀ (i : ι) (e : TangentSpace 𝓘(ℝ,Model n) x) (t D : ℝ),
      μ ≤ w i → ‖e‖=1 → 0<t → 0<D → 0 < inner ℝ p e →
      κ*D ≤ (inner ℝ p e)^2 → ‖v i‖^2-‖p‖^2 ≤ L*D → v i=p+t • e →
      c*expJacobian x (v i) ≤ expJacobian x p := by
  obtain ⟨c,hc,H⟩ := hmtw.uniform_extended_expJacobian_comparison hμ
    (div_pos hL (show 0<2*κ by positivity))
  refine ⟨c,hc,?_⟩
  intro ι _ x v w p hw hs hv hp i e t D hi he ht _hD hh hhD hgap hvi
  have hratio := outward_inner_ratio he ht hh hκ hL hhD (hvi ▸ hgap)
  have hline (s : ℝ) (hst : s∈Icc (-μ) 1) : p+s • (t • e)∈minimizingVectors x := by
    have HH := convex_barycentric_segment (hmtw.convex_minimizingVectors x)
      w v hw hs hv i hμ.le hi s hst
    rw [←hp,hvi] at HH
    simpa only [add_sub_cancel_left] using HH
  have HH := H x p (t • e) hratio.1 hratio.2 hline
  rwa [←hvi] at HH
end OutwardSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ReversedRadial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ReversedRadial
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_17_r7161c1_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma uniform_reversed_radial_expJacobian_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ z : TangentBundle 𝓘(ℝ,Model n) M, z.2∈minimizingVectors z.1 →
        ∀ l∈Icc (1/2:ℝ) 1,
        l⁻¹ • (reverseRay z).2∈minimizingVectors (reverseRay z).1 →
        c*expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ≤
          C*expJacobian z.1 z.2) ∧
      (∀ z : TangentBundle 𝓘(ℝ,Model n) M, z.2∈minimizingVectors z.1 →
        ∀ l∈Icc (1:ℝ) 2,
        c*expJacobian z.1 z.2 ≤
          C*expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2)) := by
  obtain ⟨c,hc,Hc⟩ := uniform_radial_expJacobian_comparison (n := n) (M := M)
  obtain ⟨C,hC,HC⟩ := uniform_reverse_expJacobian_comparison (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_,?_⟩
  · intro z hz l hl hr
    have hl0 : l≠0 := ne_of_gt (by linarith [hl.1])
    have H := Hc (reverseRay z).1 (l⁻¹ • (reverseRay z).2) hr l hl
    rw [smul_smul,mul_inv_cancel₀ hl0,one_smul] at H
    exact H.trans (HC z hz)
  · intro z hz l hl
    have hl1 : l⁻¹∈Icc (1/2:ℝ) 1 := by
      constructor
      · exact (le_inv_comm₀ (by norm_num) (by linarith [hl.1])).mpr (by simpa using hl.2)
      · exact inv_le_one_of_one_le₀ hl.1
    have H := Hc (reverseRay z).1 (reverseRay z).2 (reverseRay_minimizing hz) l⁻¹ hl1
    have R := HC (reverseRay z) (reverseRay_minimizing hz)
    rw [reverseRay_reverseRay] at R
    calc c*expJacobian z.1 z.2 ≤ c*(C*expJacobian (reverseRay z).1 (reverseRay z).2) :=
          mul_le_mul_of_nonneg_left R hc.le
      _ = C*(c*expJacobian (reverseRay z).1 (reverseRay z).2) := by ring
      _ ≤ C*expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2) :=
          mul_le_mul_of_nonneg_left H hC.le
end ReversedRadial
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ThreeDeterminantsClose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma three_determinants_close {σ σi σt σti V W K c C d c₀ c₁ C₀ : ℝ}
    (hσ : 0<σ) (hσi : 0<σi) (hσt : 0<σt) (hσti : 0<σti)
    (hK : 0<K) (hc : 0 < c) (hC : 0<C) (hd : 0<d)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hC₀ : 0<C₀)
    (hr : c*σt ≤ C*σ) (hri : c*σi ≤ C*σti) (ha : d*σi ≤ σ)
    (hV : c₀*σ^2/σt ≤ V) (hW : W ≤ C₀*σi^2/σti) (hVW : c₁*K*V ≤ W) :
    K ≤ (C₀*C*C)/(c₁*c₀*c*c*d) := by
  have hV0 : 0 ≤ V := (div_nonneg (mul_nonneg hc₀.le (sq_nonneg σ)) hσt.le).trans hV
  have hlow : c₀*c*σ ≤ C*V := by
    have h0 := (div_le_iff₀ hσt).mp hV
    have h1 := mul_le_mul_of_nonneg_left h0 hc.le
    have h2 := mul_le_mul_of_nonneg_left hr hV0
    apply (mul_le_mul_iff_right₀ hσ).mp
    nlinarith only [h1,h2]
  have hupp : c*W ≤ C₀*C*σi := by
    have h0 := (le_div_iff₀ hσti).mp hW
    have h1 := mul_le_mul_of_nonneg_left h0 hc.le
    have h2 := mul_le_mul_of_nonneg_left hri (mul_nonneg hC₀.le hσi.le)
    apply (mul_le_mul_iff_right₀ hσti).mp
    nlinarith only [h1,h2]
  have h1 := mul_le_mul_of_nonneg_left hVW (mul_nonneg hc.le hC.le)
  have h2 := mul_le_mul_of_nonneg_left hlow (mul_nonneg (mul_nonneg hc.le hc₁.le) hK.le)
  have h3 := mul_le_mul_of_nonneg_left hupp hC.le
  have h4 := mul_le_mul_of_nonneg_left ha
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc₁.le hc₀.le) hc.le) hc.le) hK.le)
  apply (le_div_iff₀ (by positivity : 0 < c₁*c₀*c*c*d)).mpr
  apply (mul_le_mul_iff_right₀ hσi).mp
  nlinarith only [h1,h2,h3,h4]

section DeterminantClosure
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance threeDeterminantsCloseFiniteDimensionalTangentSpace_r7161c1_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma WeakMTW.uniform_three_determinant_closure_oai
    (hmtw : WeakMTW (n := n) (M := M)) {μ κ A c₀ c₁ C₀ : ℝ}
    (hμ : 0<μ) (hκ : 0<κ) (hA : 0<A) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hC₀ : 0<C₀) :
    ∃ B : ℝ, 0<B ∧ ∀ (ι : Type) [Fintype ι] (x : M)
      (v : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
      (p : TangentSpace 𝓘(ℝ,Model n) x),
      (∀ j,0 ≤ w j) → (∑ j,w j=1) → (∀ j,v j∈minimizingVectors x) →
      p=∑ j,w j • v j → ∀ (i : ι) (e : TangentSpace 𝓘(ℝ,Model n) x) (t D : ℝ),
      μ ≤ w i → ‖e‖=1 → 0<t → 0<D → 0 < inner ℝ p e →
      κ*D ≤ (inner ℝ p e)^2 → ‖v i‖^2-‖p‖^2 ≤ A*D → v i=p+t • e →
      ∀ l∈Icc (1/2:ℝ) 1, ∀ li∈Icc (1:ℝ) 2,
      let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
      let zi : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,v i⟩
      let σ := expJacobian x p
      let σi := expJacobian x (v i)
      let σt := expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2)
      let σti := expJacobian (reverseRay zi).1 (li⁻¹ • (reverseRay zi).2)
      l⁻¹ • (reverseRay z).2∈minimizingVectors (reverseRay z).1 →
      0<σ → 0<σi → 0<σt → 0<σti → ∀ V W K : ℝ, 0<K →
      c₀*σ^2/σt ≤ V → W ≤ C₀*σi^2/σti → c₁*K*V ≤ W → K ≤ B := by
  obtain ⟨c,C,hc,hC,HR,HRi⟩ := uniform_reversed_radial_expJacobian_comparison (n := n) (M := M)
  obtain ⟨d,hd,HO⟩ := hmtw.uniform_outward_expJacobian_comparison hμ hκ hA
  refine ⟨(C₀*C*C)/(c₁*c₀*c*c*d),by positivity,?_⟩
  intro ι _ x v w p hw hs hv hp i e t D hi he ht hD hh hhD hgap hvi l hl li hli
  dsimp only
  intro hr hσ hσi hσt hσti V W K hK hV hW hVW
  have hpG : p∈minimizingVectors x := by
    rw [hp]
    exact (hmtw.convex_minimizingVectors x).sum_mem (fun j _ => hw j) hs (fun j _ => hv j)
  exact three_determinants_close hσ hσi hσt hσti hK hc hC hd hc₀ hc₁ hC₀
    (HR ⟨x,p⟩ hpG l hl hr) (HRi ⟨x,v i⟩ (hv i) li hli)
    (HO ι x v w p hw hs hv hp i e t D hi he ht hD hh hhD hgap hvi) hV hW hVW
end DeterminantClosure
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure_oai.{u_1}
