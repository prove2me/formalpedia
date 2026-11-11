-- Prove2me | solution 1 for OAI.WeakMTWTransport.original_chart_good_null
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:03.348097+00:00
-- url     : https://prove2.me/submissions/e1c047a6-4d4d-4c70-be4b-360377d6115a

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
import Definitions.Def_OAIQ232A026
import Definitions.Def_OAIQ232A027

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Calculus
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma convexOn_of_affine_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S, f x+L (y-x)≤f y) :
    ConvexOn ℝ S f := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x+b • y
  obtain ⟨L,hL⟩ := hs z (hS hx hy ha hb hab)
  have hx' := mul_le_mul_of_nonneg_left (hL x hx) ha
  have hy' := mul_le_mul_of_nonneg_left (hL y hy) hb
  have hzero : a*L (x-z)+b*L (y-z)=0 := by
    rw [←smul_eq_mul a,←smul_eq_mul b,←map_smul,←map_smul,←map_add]
    have he : a • (x-z)+b • (y-z)=0 := by
      rw [smul_sub,smul_sub,←add_sub_add_comm,←add_smul,hab,one_smul]
      exact sub_self z
    rw [he,map_zero]
  change f z≤a*f x+b*f y
  have hc : a*f z+b*f z=f z := by rw [←add_mul,hab,one_mul]
  nlinarith [hc]

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Inner
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexOn_of_quadratic_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (B : ℝ)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-B*‖y-x‖^2≤f y) :
    ConvexOn ℝ S (fun x => f x+B*‖x‖^2) := by
  apply convexOn_of_affine_lower_supports hS
  intro x hx
  obtain ⟨L,hL⟩ := hs x hx
  refine ⟨L+(2*B) • innerSL ℝ x,?_⟩
  intro y hy
  have H := hL y hy
  simp only [_root_.add_apply,_root_.smul_apply,innerSL_apply_apply,inner_sub_right,
    smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real] at H
  have hi : inner ℝ y x=inner ℝ x y := real_inner_comm _ _
  rw [hi] at H
  nlinarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Subgradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_lipschitz_extension {f : E → ℝ} {s : Set E} {L : ℝ≥0}
    (hc : ConvexOn ℝ s f) (hlip : LipschitzOnWith L f s) (hs : s.Nonempty) :
    ∃ g : E → ℝ, LipschitzWith L g ∧ ConvexOn ℝ univ g ∧ EqOn f g s := by
  have : Nonempty s := hs.to_subtype
  let g := fun y : E => ⨅ x : s, f x + L * dist y x
  have hB : ∀ y : E, BddBelow (range fun x : s => f x + L * dist y x) := by
    intro y
    obtain ⟨z,hz⟩ := hs
    refine ⟨f z - L*dist y z, ?_⟩
    rintro w ⟨t,rfl⟩
    dsimp
    rw [sub_le_iff_le_add,add_assoc,← mul_add,add_comm (dist y t)]
    calc
      f z ≤ f t + L * dist z t := hlip.le_add_mul hz t.2
      _ ≤ f t + L*(dist y z + dist y t) := by
        gcongr
        exact dist_triangle_left _ _ _
  have hEq : EqOn f g s := by
    intro x hx
    refine le_antisymm (le_ciInf fun y => hlip.le_add_mul hx y.2) ?_
    simpa only [add_zero,Subtype.coe_mk,mul_zero,dist_self] using ciInf_le (hB x) ⟨x,hx⟩
  have hgL : LipschitzWith L g := by
    apply LipschitzWith.of_le_add_mul L
    intro x y
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun z => ?_
    rw [sub_le_iff_le_add]
    calc
      g x ≤ f z + L*dist x z := ciInf_le (hB x) _
      _ ≤ f z + L*dist y z + L*dist x y := by
        rw [add_assoc,← mul_add,add_comm (dist y z)]
        gcongr
        exact dist_triangle _ _ _
  refine ⟨g,hgL,⟨convex_univ,?_⟩,hEq⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨u,hu⟩ : ∃ u : s, f u + L*dist x u < g x + eps :=
    exists_lt_of_ciInf_lt (by dsimp [g]; linarith : g x < g x + eps)
  obtain ⟨v,hv⟩ : ∃ v : s, f v + L*dist y v < g y + eps :=
    exists_lt_of_ciInf_lt (by dsimp [g]; linarith : g y < g y + eps)
  have huv : a • (u:E) + b • (v:E) ∈ s := hc.1 u.2 v.2 ha hb hab
  have hcf := hc.2 u.2 v.2 ha hb hab
  have hdist : dist (a • x+b • y) (a • (u:E)+b • (v:E)) ≤
      a*dist x u + b*dist y v := by
    rw [dist_eq_norm,dist_eq_norm,dist_eq_norm]
    have heq : a • x+b • y-(a • (u:E)+b • (v:E)) =
      a • (x-u) + b • (y-v) := by simp only [smul_sub]; abel
    rw [heq]
    calc
      ‖a • (x-u)+b • (y-v)‖ ≤ ‖a • (x-u)‖+‖b • (y-v)‖ := norm_add_le _ _
      _ = a*‖x-u‖+b*‖y-v‖ := by rw [norm_smul_of_nonneg ha,norm_smul_of_nonneg hb]
  calc
    g (a • x+b • y) ≤ f (a • (u:E)+b • (v:E)) +
        L*dist (a • x+b • y) (a • (u:E)+b • (v:E)) :=
      ciInf_le (hB _) ⟨_,huv⟩
    _ ≤ a*f u+b*f v + L*(a*dist x u+b*dist y v) := by
      exact add_le_add hcf (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
    _ = a*(f u+L*dist x u)+b*(f v+L*dist y v) := by ring
    _ ≤ a*(g x+eps)+b*(g y+eps) := add_le_add
      (mul_le_mul_of_nonneg_left hu.le ha) (mul_le_mul_of_nonneg_left hv.le hb)
    _ = a*g x+b*g y+eps := by nlinarith [hab]

open MeasureTheory

lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {s : Set X} {P : X → Prop}
    (hloc : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (∀ᵐ z ∂μ, z ∈ U → P z)) :
    ∀ᵐ z ∂μ, z ∈ s → P z := by
  classical
  choose U hUo hxU hUae using fun x : s => hloc x x.2
  have hcov : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  obtain ⟨c,hc,hcover⟩ := (IsLindelof.of_coe (s := s)).elim_countable_subcover U hUo hcov
  have hnull : μ (⋃ i ∈ c, {z | z ∈ U i ∧ ¬P z}) = 0 := by
    apply (measure_biUnion_null_iff hc).mpr
    intro i _
    simpa only [Classical.not_imp] using (ae_iff.mp (hUae i))
  apply ae_iff.mpr
  apply measure_mono_null _ hnull
  intro z hz
  have hz' : z ∈ s ∧ ¬P z := by simpa only [mem_ofPred_eq,Classical.not_imp] using hz
  obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hcover hz'.1)
  exact mem_iUnion₂.mpr ⟨i,hi,hzi,hz'.2⟩

namespace ConvexProximal

lemma norm_sq_add_real (a b : E) :
    ‖a+b‖^2 = ‖a‖^2 + 2 * inner ℝ a b + ‖b‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right]
  rw [real_inner_comm b a]
  ring

lemma energy_increment (f : E → ℝ) (y x v : E) (t : ℝ) :
    energy f y (x + t • (v-x)) - energy f y x =
      f (x + t • (v-x)) - f x +
        t * inner ℝ (x-y) (v-x) + t^2/2*‖v-x‖^2 := by
  have heq : x + t • (v-x) - y = (x-y) + t • (v-x) := by abel
  simp only [energy, heq, norm_sq_add_real, real_inner_smul_right, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma subgradient_iff_minimizer {f : E → ℝ} (hf : ConvexOn ℝ univ f) (y x : E) :
    IsSubgradientOn f univ x (y-x) ↔ ∀ v, energy f y x ≤ energy f y v := by
  constructor
  · intro hs v
    have hh := hs v (mem_univ _)
    have hi := energy_increment f y x v 1
    have heq : x + (1:ℝ) • (v-x) = v := by simp
    rw [heq] at hi
    have hí : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
      rw [← neg_sub x y, inner_neg_left]
    rw [hí] at hh
    nlinarith [sq_nonneg ‖v-x‖]
  · intro hm v _
    have hb (t : ℝ) (ht : t ∈ Ioo 0 1) :
        f x + inner ℝ (y-x) (v-x) ≤ f v + t/2*‖v-x‖^2 := by
      have hc := hf.2 (mem_univ x) (mem_univ v) (by linarith [ht.2] : 0 ≤ 1-t)
        ht.1.le (by ring : 1-t+t=1)
      have heq : (1-t) • x + t • v = x + t • (v-x) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      rw [heq] at hc
      have hi := energy_increment f y x v t
      have hlo := hm (x + t • (v-x))
      have hinner : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
        rw [← neg_sub x y, inner_neg_left]
      rw [hinner]
      have hc' : f (x + t • (v-x)) ≤ (1-t)*f x + t*f v := by
        simpa only [smul_eq_mul] using hc
      apply (mul_le_mul_iff_left₀ ht.1).mp
      nlinarith
    have hcl : (0 : ℝ) ∈ closure (Ioo 0 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
      simp
    have hc : Continuous (fun t : ℝ => f v + t/2*‖v-x‖^2) := by fun_prop
    have hh := ContinuousWithinAt.closure_le hcl
      (continuousWithinAt_const (b := f x + inner ℝ (y-x) (v-x))) hc.continuousWithinAt hb
    simpa using hh

lemma subgradient_strong_min {f : E → ℝ} {y x : E}
    (hs : IsSubgradientOn f univ x (y-x)) (v : E) :
    energy f y x + ‖v-x‖^2/2 ≤ energy f y v := by
  have hh := hs v (mem_univ _)
  have hi := energy_increment f y x v 1
  have heq : x + (1:ℝ) • (v-x) = v := by simp
  rw [heq] at hi
  have hí : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
    rw [← neg_sub x y, inner_neg_left]
  rw [hí] at hh
  nlinarith

lemma subgradient_monotone {f : E → ℝ} {x z p q : E}
    (hp : IsSubgradientOn f univ x p) (hq : IsSubgradientOn f univ z q) :
    0 ≤ inner ℝ (p-q) (x-z) := by
  have h1 := hp z (mem_univ _)
  have h2 := hq x (mem_univ _)
  rw [← neg_sub x z, inner_neg_right] at h1
  simp only [inner_sub_left]
  linarith

lemma minimizer_unique {f : E → ℝ} (hf : ConvexOn ℝ univ f) {y x z : E}
    (hx : ∀ v, energy f y x ≤ energy f y v)
    (hz : ∀ v, energy f y z ≤ energy f y v) : x = z := by
  have hs := (subgradient_iff_minimizer hf y x).mpr hx
  have hb := subgradient_strong_min hs z
  have hh := hz x
  have hzero : ‖z-x‖ = 0 := by nlinarith [norm_nonneg (z-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

variable [FiniteDimensional ℝ E]

lemma prox_minimizes (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (y v : E) :
    energy f y (prox f L hf y) ≤ energy f y v :=
  Classical.choose_spec (exists_minimizer hf y) v

lemma prox_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) (y : E) :
    IsSubgradientOn f univ (prox f L hlip y) (y - prox f L hlip y) :=
  (subgradient_iff_minimizer hconv y _).mpr (prox_minimizes f L hlip y)

lemma prox_of_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) {x p : E} (hp : IsSubgradientOn f univ x p) :
    prox f L hlip (x+p) = x := by
  apply minimizer_unique hconv (prox_minimizes f L hlip (x+p))
  apply (subgradient_iff_minimizer hconv (x+p) x).mp
  simpa using hp

lemma prox_firm {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) (y z : E) :
    ‖prox f L hlip y - prox f L hlip z‖^2 ≤
      inner ℝ (prox f L hlip y - prox f L hlip z) (y-z) := by
  have hm := subgradient_monotone (prox_subgradient hlip hconv y)
    (prox_subgradient hlip hconv z)
  have heq : (y-prox f L hlip y) - (z-prox f L hlip z) =
      (y-z) - (prox f L hlip y - prox f L hlip z) := by abel
  rw [heq, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at hm
  linarith

lemma prox_lipschitz {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) : LipschitzWith 1 (prox f L hlip) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hf := prox_firm hlip hconv y z
  have hi := real_inner_le_norm (prox f L hlip y - prox f L hlip z) (y-z)
  have hnorm : ‖prox f L hlip y - prox f L hlip z‖ ≤ ‖y-z‖ := by
    nlinarith [norm_nonneg (prox f L hlip y - prox f L hlip z), norm_nonneg (y-z)]
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hnorm

omit [FiniteDimensional ℝ E] in
lemma subgradient_norm_le {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    {x p : E} (hp : IsSubgradientOn f univ x p) : ‖p‖ ≤ L := by
  have hs := hp (x+p) (mem_univ _)
  have hl := hlip.dist_le_mul (x+p) x
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hs
  simp only [dist_eq_norm, add_sub_cancel_left] at hl
  have hh := (abs_le.mp hl).2
  nlinarith [norm_nonneg p]

lemma gradient_subgradient {f : E → ℝ} (hc : ConvexOn ℝ univ f) {x : E}
    {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    IsSubgradientOn f univ x ((InnerProductSpace.toDual ℝ E).symm f') := by
  intro v _
  rw [InnerProductSpace.toDual_symm_apply]
  have hd : HasDerivAt (fun t : ℝ => f (x + t • (v-x))) (f' (v-x)) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x + t • (v-x)) (v-x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v-x)).const_add x
    have hdf : HasFDerivAt f f' (x + (0:ℝ) • (v-x)) := by simpa using hder
    exact hdf.comp_hasDerivAt 0 hp
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹ * (f (x+t • (v-x)) - f x) ≤ f v - f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have hcv := hc.2 (mem_univ x) (mem_univ v) (by linarith [ht.2] : 0 ≤ 1-t)
      ht.1.le (by ring : 1-t+t=1)
    have heq : (1-t) • x + t • v = x + t • (v-x) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [heq] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div, div_le_iff₀ ht.1]
    nlinarith
  have ht : Tendsto (fun t : ℝ => t⁻¹ * (f (x+t • (v-x)) - f x))
      (𝓝[>] 0) (𝓝 (f' (v-x))) := by
    simpa only [zero_add, zero_smul, add_zero, smul_eq_mul] using hd.tendsto_slope_zero_right
  have hh := le_of_tendsto ht hb
  linarith

lemma subgradient_eq_gradient {f : E → ℝ} {x p : E} {f' : E →L[ℝ] ℝ}
    (hder : HasFDerivAt f f' x) (hp : IsSubgradientOn f univ x p) :
    p = (InnerProductSpace.toDual ℝ E).symm f' := by
  let g : E → ℝ := fun z => f z - inner ℝ p z
  have hmin : IsLocalMin g x := by
    apply Filter.Eventually.of_forall
    intro z
    have hh := hp z (mem_univ _)
    dsimp [g]
    simp only [inner_sub_right] at hh
    linarith
  have hdg : HasFDerivAt g (f' - innerSL ℝ p) x :=
    hder.sub (innerSL ℝ p).hasFDerivAt
  have hz := hmin.hasFDerivAt_eq_zero hdg
  have heq : f' = innerSL ℝ p := sub_eq_zero.mp hz
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact heq.symm

omit [FiniteDimensional ℝ E] in
lemma isClosed_subgradient_projection {f : E → ℝ} (hf : Continuous f)
    {K : Set E} (hK : IsCompact K) :
    IsClosed {x | ∃ p ∈ K, IsSubgradientOn f univ x p} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : Set (E × K) := {z | IsSubgradientOn f univ z.1 z.2.1}
  have hC : IsClosed C := by
    simp only [C, IsSubgradientOn, ofPred_forall]
    exact isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) (by fun_prop)
  have heq : {x | ∃ p ∈ K, IsSubgradientOn f univ x p} = Prod.fst '' C := by
    ext x
    constructor
    · rintro ⟨p,hp,hpx⟩
      exact ⟨(x,⟨p,hp⟩),hpx,rfl⟩
    · rintro ⟨⟨z,p⟩,hz,rfl⟩
      exact ⟨p.1,p.2,hz⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace C hC

lemma subgradient_continuity_at_singleton {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) {x p0 : E}
    (huniq : ∀ p, IsSubgradientOn f univ x p → p = p0) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p → ‖p-p0‖ < eps := by
  intro eps heps
  let K := Metric.closedBall (0:E) (L:ℝ) \ Metric.ball p0 eps
  have hK : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hclosed := isClosed_subgradient_projection hlip.continuous hK
  have hx : x ∉ {z | ∃ p ∈ K, IsSubgradientOn f univ z p} := by
    rintro ⟨p,hp,hpx⟩
    have heq := huniq p hpx
    exact hp.2 (heq ▸ Metric.mem_ball_self heps)
  obtain ⟨delta,hd,hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hx)
  refine ⟨delta,hd,?_⟩
  intro z p hz hp
  by_contra hbad
  have hpK : p ∈ K := by
    constructor
    · simpa only [Metric.mem_closedBall,dist_zero_right] using subgradient_norm_le hlip hp
    · simpa only [Metric.mem_ball,dist_eq_norm] using hbad
  exact (hball (by simpa only [Metric.mem_ball,dist_eq_norm] using hz)) ⟨p,hpK,hp⟩

lemma subgradient_continuity_of_differentiable {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) {x : E} {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p →
        ‖p-(InnerProductSpace.toDual ℝ E).symm f'‖ < eps :=
  subgradient_continuity_at_singleton hlip (fun _ hp => subgradient_eq_gradient hder hp)

lemma uniform_subgradient_differential_of_regular_prox {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    {x y : E} {f' : E →L[ℝ] ℝ} (hdf : HasFDerivAt f f' x)
    (hy : prox f L hlip y = x) (B : E ≃L[ℝ] E)
    (hdP : HasFDerivAt (prox f L hlip) (B : E →L[ℝ] E) y) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p →
        ‖p - (InnerProductSpace.toDual ℝ E).symm f' -
          ((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x)‖ ≤
          eps * ‖z-x‖ := by
  let p0 := (InnerProductSpace.toDual ℝ E).symm f'
  have hyp : y = x + p0 := by
    have hs := prox_subgradient hlip hc y
    rw [hy] at hs
    have heq := subgradient_eq_gradient hdf hs
    dsimp [p0]
    rw [← heq]
    abel
  intro eps heps
  let K : ℝ := ‖(B.symm : E →L[ℝ] E)‖ + 1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hKbound : ‖(B.symm : E →L[ℝ] E)‖ ≤ K := by dsimp [K] <;> linarith
  let eta : ℝ := min (1/(2*K)) (eps/(2*K^2))
  have heta : 0 < eta := by dsimp [eta] <;> positivity
  have heta1 : K*eta ≤ 1/2 := by
    have hh := min_le_left (1/(2*K)) (eps/(2*K^2))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*K)).mp hh
    dsimp [eta]
    nlinarith
  have heta2 : 2*K^2*eta ≤ eps := by
    have hh := min_le_right (1/(2*K)) (eps/(2*K^2))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*K^2)).mp hh
    dsimp [eta]
    nlinarith
  obtain ⟨r,hr,hrem⟩ := Metric.mem_nhds_iff.mp (hdP.isLittleO.bound heta)
  obtain ⟨d,hd,hcont⟩ := subgradient_continuity_of_differentiable hlip hdf (r/2)
    (by positivity)
  refine ⟨min d (r/2), by positivity, ?_⟩
  intro z p hz hp
  have hpn : ‖p-p0‖ < r/2 := hcont z p (lt_of_lt_of_le hz (min_le_left _ _)) hp
  let k : E := z+p-y
  have hk : k = (z-x) + (p-p0) := by dsimp [k]; rw [hyp]; abel
  have hkr : ‖z+p-y‖ < r := by
    calc
      ‖z+p-y‖ = ‖(z-x)+(p-p0)‖ := congrArg norm hk
      _ ≤ ‖z-x‖ + ‖p-p0‖ := norm_add_le _ _
      _ < r := by have hz' := lt_of_lt_of_le hz (min_le_right _ _); linarith
  have hPz : prox f L hlip (z+p) = z := prox_of_subgradient hlip hc hp
  have hres : ‖(z-x) - B k‖ ≤ eta*‖k‖ := by
    have hh := hrem (by simpa only [Metric.mem_ball,dist_eq_norm] using hkr)
    simpa only [Set.mem_ofPred_eq, hy,hPz,k,ContinuousLinearEquiv.coe_coe] using hh
  have hinv : k = B.symm (z-x) - B.symm ((z-x)-B k) := by
    simp only [map_sub, B.symm_apply_apply]
    abel
  have hknorm : ‖k‖ ≤ 2*K*‖z-x‖ := by
    have htri : ‖k‖ ≤ ‖B.symm (z-x)‖ + ‖B.symm ((z-x)-B k)‖ := by
      conv_lhs => rw [hinv]
      exact norm_sub_le _ _
    have h1 := (B.symm : E →L[ℝ] E).le_opNorm (z-x)
    have h2 := (B.symm : E →L[ℝ] E).le_opNorm ((z-x)-B k)
    have h1' : ‖B.symm (z-x)‖ ≤ K*‖z-x‖ := h1.trans
      (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
    have h2' : ‖B.symm ((z-x)-B k)‖ ≤ K*eta*‖k‖ := by
      calc
        ‖B.symm ((z-x)-B k)‖ ≤ K*‖(z-x)-B k‖ := h2.trans
          (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
        _ ≤ K*(eta*‖k‖) := mul_le_mul_of_nonneg_left hres hK.le
        _ = K*eta*‖k‖ := by ring
    have h3 := mul_le_mul_of_nonneg_right heta1 (norm_nonneg k)
    nlinarith
  have heq : p-p0-((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x) =
      - B.symm ((z-x)-B k) := by
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, map_sub, B.symm_apply_apply]
    rw [hk]
    abel
  change ‖p-p0-((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x)‖ ≤ _
  rw [heq,norm_neg]
  calc
    ‖B.symm ((z-x)-B k)‖ ≤ K*‖(z-x)-B k‖ :=
      ((B.symm : E →L[ℝ] E).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
    _ ≤ K*(eta*‖k‖) := mul_le_mul_of_nonneg_left hres hK.le
    _ ≤ K*(eta*(2*K*‖z-x‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hknorm heta.le) hK.le
    _ = (2*K^2*eta)*‖z-x‖ := by ring
    _ ≤ eps*‖z-x‖ := mul_le_mul_of_nonneg_right heta2 (norm_nonneg _)

end ConvexProximal
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_TransformSemiconvex
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
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
section TransformSemiconvex
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_cTransform_semiconvex (a : M) :
    ∃ K>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ v : M → ℝ, Continuous v →
        ConvexOn ℝ (ball (extChartAt 𝓘(ℝ,Model n) a a) r)
          (fun z => cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm z)+K/2*‖z‖^2) := by
  obtain ⟨B,hB,r,hr,hrT,hjet⟩ := uniform_half_cost_hessian (n := n) a
  refine ⟨4*B,by positivity,r,hr,hrT,?_⟩
  intro v hv
  have he : 4*B/2=2*B := by ring
  rw [he]
  apply convexOn_of_quadratic_lower_supports (convex_ball _ _)
  intro x hx
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (χ.symm x)
  let f := chartCost (n := n) a (riemannianExp (χ.symm x) ((1/2:ℝ) • p))
  refine ⟨(-2:ℝ) • fderiv ℝ f x,?_⟩
  intro z hz
  have hrem := first_order_remainder_le_of_hessian_bound (convex_ball _ _) hB.le
    (fun w hw => (hjet x hx p hp.1 w hw).1)
    (fun w hw => (hjet x hx p hp.1 w hw).2) hx hz
  have hlow := active_split_lower_support hv hp.1 hp.2
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (χ.symm z)
  change |f z-f x-fderiv ℝ f x (z-x)|≤B*‖z-x‖^2 at hrem
  change -(f z-f x)/(1/2:ℝ) ≤ cTransform v (χ.symm z)-cTransform v (χ.symm x) at hlow
  have hU := (abs_le.mp hrem).2
  simp only [_root_.smul_apply,smul_eq_mul]
  norm_num at hlow
  nlinarith

end TransformSemiconvex
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_Measurable
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
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open MeasureTheory

namespace ConvexProximal
variable [FiniteDimensional ℝ E]
section Measurable
open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E]

lemma exists_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hc : ConvexOn ℝ univ f) (x : E) :
    ∃ p, IsSubgradientOn f univ x p := by
  let μ : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hdense : Dense {z | DifferentiableAt ℝ f z} :=
    μ.dense_of_ae (hlip.ae_differentiableAt (μ := μ))
  let P := Metric.closedBall (0:E) (L:ℝ)
  have hP : IsCompact P := isCompact_closedBall _ _
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let C : Set (E × P) := {z | IsSubgradientOn f univ z.1 z.2.1}
  have hfc := hlip.continuous
  have hC : IsClosed C := by
    simp only [C, IsSubgradientOn, ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro _hy
    exact isClosed_le (by fun_prop) (by fun_prop)
  have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have hsub : {z | DifferentiableAt ℝ f z} ⊆ Prod.fst '' C := by
    intro z hz
    let p := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)
    have hp : IsSubgradientOn f univ z p := gradient_subgradient hc hz.hasFDerivAt
    have hpn : p ∈ P := by
      simpa only [P, Metric.mem_closedBall, dist_zero_right] using subgradient_norm_le hlip hp
    exact ⟨(z, ⟨p, hpn⟩), hp, rfl⟩
  have hx : x ∈ Prod.fst '' C := by
    rw [← hproj.closure_eq]
    exact (Dense.mono hsub hdense) x
  obtain ⟨⟨z,p⟩, hz, rfl⟩ := hx
  exact ⟨p.1, hz⟩

lemma prox_surjective {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hc : ConvexOn ℝ univ f) : Function.Surjective (prox f L hlip) := by
  intro x
  obtain ⟨p,hp⟩ := exists_subgradient hlip hc x
  exact ⟨x+p, prox_of_subgradient hlip hc hp⟩

lemma ae_exists_regular_proximal_inverse {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, ∃ y : E, prox f L hlip y = x ∧
      DifferentiableAt ℝ (prox f L hlip) y ∧
      (fderiv ℝ (prox f L hlip) y).det ≠ 0 := by
  let P := prox f L hlip
  let ν : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hP : LipschitzWith 1 P := prox_lipschitz hlip hc
  let N : Set E := {y | ¬DifferentiableAt ℝ P y}
  let Z : Set E := {y | DifferentiableAt ℝ P y ∧ (fderiv ℝ P y).det = 0}
  have hN : ν N = 0 := (ae_iff).mp (hP.ae_differentiableAt (μ := ν))
  have hPN : ν (P '' N) = 0 := by
    have hh := hP.hausdorffMeasure_image_le
      (by positivity : (0:ℝ) ≤ Module.finrank ℝ E) N
    simpa only [ν, hN, mul_zero, nonpos_iff_eq_zero] using hh
  have hNμ : μ (P '' N) = 0 :=
    (Measure.absolutelyContinuous_isAddHaarMeasure μ ν) hPN
  have hZμ : μ (P '' Z) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun y hy => hy.1.hasFDerivAt.hasFDerivWithinAt) (fun y hy => hy.2)
  have hgood : ∀ᵐ x ∂μ, x ∉ P '' N ∧ x ∉ P '' Z := by
    exact (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hNμ)).and (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hZμ))
  filter_upwards [hgood] with x hx
  obtain ⟨y,hy⟩ := prox_surjective hlip hc x
  have hd : DifferentiableAt ℝ P y := by
    by_contra hn
    exact hx.1 ⟨y,hn,hy⟩
  refine ⟨y,hy,hd,?_⟩
  intro hz
  exact hx.2 ⟨y,⟨hd,hz⟩,hy⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma subgradient_line_deriv {f : E → ℝ} {x h : E} {t a : ℝ} {p : E}
    (hp : IsSubgradientOn f univ (x+t • h) p)
    (hd : HasDerivAt (fun s : ℝ => f (x+s • h)) a t) :
    a = inner ℝ p h := by
  have hm : IsLocalMin (fun s : ℝ => f (x+s • h) - s*inner ℝ p h) t := by
    apply Filter.Eventually.of_forall
    intro s
    have hh := hp (x+s • h) (mem_univ _)
    have heq : (x+s • h)-(x+t • h) = (s-t) • h := by
      simp only [sub_smul]; abel
    rw [heq,real_inner_smul_right] at hh
    dsimp
    nlinarith
  have hh := hm.hasDerivAt_eq_zero (hd.sub ((hasDerivAt_id t).mul_const (inner ℝ p h)))
  simpa only [one_mul, sub_eq_zero] using hh

lemma quadraticExpansion_of_subgradient_differential {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    {x p : E} {A : E →L[ℝ] E}
    (hdiff : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z q : E, ‖z-x‖ < delta → IsSubgradientOn f univ z q →
        ‖q-p-A (z-x)‖ ≤ eps*‖z-x‖) :
    HasQuadraticExpansion (fun h => f (x+h)) p A := by
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hdiff eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  let g : ℝ → ℝ := fun t => f (x+t • h)
  have hline : LipschitzWith ‖h‖₊ (fun t : ℝ => x+t • h) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have heq : (x+s • h)-(x+t • h) = (s-t) • h := by
      simp only [sub_smul]; abel
    simp only [dist_eq_norm,heq,norm_smul,Real.norm_eq_abs,coe_nnnorm]
    exact le_of_eq (mul_comm _ _)
  have hgAC : AbsolutelyContinuousOnInterval g 0 1 :=
    (hlip.comp hline).lipschitzOnWith.absolutelyContinuousOnInterval
  let a : ℝ := inner ℝ p h
  let b : ℝ := inner ℝ (A h) h
  have hlin : IntervalIntegrable (fun t : ℝ => a+t*b) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => a+t*b)).intervalIntegrable _ _
  have haebound : ∀ᵐ t : ℝ, t ∈ uIoc (0:ℝ) 1 →
      ‖deriv g t - (a+t*b)‖ ≤ eps*‖h‖^2 := by
    filter_upwards [hgAC.ae_differentiableAt] with t ht htc
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at htc
      exact ⟨htc.1.le,htc.2⟩
    have htu : t ∈ uIcc (0:ℝ) 1 := by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ht01
    obtain ⟨q,hq⟩ := exists_subgradient hlip hc (x+t • h)
    have hder : deriv g t = inner ℝ q h := subgradient_line_deriv hq (ht htu).hasDerivAt
    have hth : ‖(x+t • h)-x‖ ≤ ‖h‖ := by
      simp only [add_sub_cancel_left,norm_smul_of_nonneg ht01.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht01.2
    have hnorm := hbound (x+t • h) q (hth.trans_lt hh) hq
    have heq : deriv g t - (a+t*b) = inner ℝ (q-p-A ((x+t • h)-x)) h := by
      simp only [hder,a,b,inner_sub_left,add_sub_cancel_left,map_smul,
        real_inner_smul_left]
      ring
    calc
      ‖deriv g t - (a+t*b)‖ = ‖inner ℝ (q-p-A ((x+t • h)-x)) h‖ := congrArg norm heq
      _ ≤ ‖q-p-A ((x+t • h)-x)‖*‖h‖ := norm_inner_le_norm _ _
      _ ≤ (eps*‖(x+t • h)-x‖)*‖h‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ (eps*‖h‖)*‖h‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hth heps.le) (norm_nonneg _)
      _ = eps*‖h‖^2 := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae haebound
  rw [intervalIntegral.integral_sub hgAC.intervalIntegrable_deriv hlin,
    hgAC.integral_deriv_eq_sub] at hi
  have hilin : (∫ t : ℝ in (0:ℝ)..1, a+t*b) = a+b/2 := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => a) (g := fun t : ℝ => t*b)
      (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => t*b)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const,integral_id]
    norm_num
    ring
  rw [hilin] at hi
  simpa only [HasQuadraticExpansion,quadraticTaylor,g,a,b,one_smul,zero_smul,add_zero,
    Real.norm_eq_abs,sub_zero,abs_one,mul_one,sub_sub,add_assoc] using hi

omit [MeasurableSpace E] [BorelSpace E] in

lemma symmetrized_quadratic (A : E →L[ℝ] E) :
    let S := (1/2 : ℝ) • (A + A.adjoint)
    (∀ h k, inner ℝ (S h) k = inner ℝ h (S k)) ∧
      (∀ h, inner ℝ (S h) h = inner ℝ (A h) h) := by
  dsimp
  constructor
  · intro h k
    simp only [smul_apply,add_apply,real_inner_smul_left,real_inner_smul_right,
      inner_add_left,inner_add_right,A.adjoint_inner_left,A.adjoint_inner_right]
    ring
  · intro h
    simp only [smul_apply,add_apply,real_inner_smul_left,inner_add_left,
      A.adjoint_inner_left,real_inner_comm h (A h)]
    ring

lemma ae_quadraticExpansion_lipschitz_convex {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  filter_upwards [hlip.ae_differentiableAt (μ := μ),
    ae_exists_regular_proximal_inverse hlip hc μ] with x hdf hx
  obtain ⟨y,hy,hdP,hdet⟩ := hx
  let B := (fderiv ℝ (prox f L hlip) y).toContinuousLinearEquivOfDetNeZero hdet
  have hB : HasFDerivAt (prox f L hlip) (B : E →L[ℝ] E) y := by
    simpa only [B,ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hdP.hasFDerivAt
  let p := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  let A := (B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E
  have hdiff := uniform_subgradient_differential_of_regular_prox hlip hc
    hdf.hasFDerivAt hy B hB
  have hquad : HasQuadraticExpansion (fun h => f (x+h)) p A :=
    quadraticExpansion_of_subgradient_differential hlip hc hdiff
  let S := (1/2 : ℝ) • (A + A.adjoint)
  obtain ⟨hsym,hdiag⟩ := symmetrized_quadratic A
  change ∀ h, inner ℝ (S h) h = inner ℝ (A h) h at hdiag
  refine ⟨p,S,hsym,?_⟩
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hquad eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  have hi := hbound h hh
  simpa only [quadraticTaylor,hdiag h] using hi

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma quadraticExpansion_congr_nhds {f g : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hfg : f =ᶠ[𝓝 (0:E)] g) (hf : HasQuadraticExpansion f p A) :
    HasQuadraticExpansion g p A := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hfg
  have hzero : f 0 = g 0 := hfg.self_of_nhds
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hf eps heps
  refine ⟨min d r,by positivity,?_⟩
  intro h hh
  have hhg : f h = g h := hball (by
    simpa only [Metric.mem_ball,dist_zero_right] using lt_of_lt_of_le hh (min_le_right _ _))
  have hb := hbound h (lt_of_lt_of_le hh (min_le_left _ _))
  simpa only [quadraticTaylor,hzero,hhg] using hb

lemma ae_quadraticExpansion_convex_open {f : E → ℝ} {s : Set E}
    (hs : IsOpen s) (hc : ConvexOn ℝ s f) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, x ∈ s → ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  apply ae_of_locally_ae μ
  intro x hx
  obtain ⟨L,t,ht,hlip⟩ := hc.locallyLipschitzOn hs hx
  rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hx)] at ht
  obtain ⟨r,hr,hrt⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (hs.mem_nhds hx))
  have hrt' : Metric.ball x r ⊆ t := fun _ hy => (hrt hy).1
  have hrs : Metric.ball x r ⊆ s := fun _ hy => (hrt hy).2
  obtain ⟨g,hgL,hgC,hfg⟩ := convex_lipschitz_extension
    (hc.subset hrs (convex_ball _ _)) (hlip.mono hrt')
    (Metric.nonempty_ball.mpr hr)
  refine ⟨Metric.ball x r,Metric.isOpen_ball,Metric.mem_ball_self hr,?_⟩
  filter_upwards [ae_quadraticExpansion_lipschitz_convex hgL hgC μ] with z hz hzb
  obtain ⟨p,A,hA,hquad⟩ := hz
  refine ⟨p,A,hA,quadraticExpansion_congr_nhds ?_ hquad⟩
  have hcont : Tendsto (fun h : E => z+h) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun h : E => z+h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0:E)
  filter_upwards [hcont (Metric.isOpen_ball.mem_nhds hzb)] with h hh
  exact (hfg hh).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma quadraticExpansion_sub_quadratic {f : E → ℝ} {x p : E} {A : E →L[ℝ] E}
    (K : ℝ)
    (hg : HasQuadraticExpansion (fun h => f (x+h)+K/2*‖x+h‖^2) p A) :
    HasQuadraticExpansion (fun h => f (x+h)) (p-K • x)
      (A-K • ContinuousLinearMap.id ℝ E) := by
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hg eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  have heq : (f (x+h)+K/2*‖x+h‖^2) -
      quadraticTaylor (f (x+0)+K/2*‖x+0‖^2) p A h =
        f (x+h)-quadraticTaylor (f (x+0)) (p-K • x)
          (A-K • ContinuousLinearMap.id ℝ E) h := by
    simp only [quadraticTaylor,add_zero,norm_sq_add_real,inner_sub_left,
      real_inner_smul_left,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    ring
  have hb := hbound h hh
  rwa [heq] at hb

lemma ae_quadraticExpansion_semiconvex_open {f : E → ℝ} {s : Set E} (K : ℝ)
    (hs : IsOpen s) (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, x ∈ s → ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  filter_upwards [ae_quadraticExpansion_convex_open hs hc μ] with x hx hxs
  obtain ⟨p,A,hA,hquad⟩ := hx hxs
  refine ⟨p-K • x,A-K • ContinuousLinearMap.id ℝ E,?_,
    quadraticExpansion_sub_quadratic K hquad⟩
  intro h k
  simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,inner_sub_left,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right,hA h k]
end Measurable

end ConvexProximal
end WeakMTWTransport

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartAlexandrov
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartAlexandrov
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
omit [Nonempty M] in
lemma original_chart_alexandrov_null {u v:M → ℝ} (hu:Continuous u)
    (hdual:IsCostDualPair u v) (a:M) :
    ∃r>0,∃N:Set (Model n),volume N=0 ∧
      Metric.ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀x∈Metric.ball (extChartAt 𝓘(ℝ,Model n) a a) r,x∉N →
        ∃p:Model n,∃A:Model n →L[ℝ] Model n,
          (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
          HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (x+h))) p A := by
  obtain ⟨K,hK,r,hr,ht,hs⟩:=uniform_cTransform_semiconvex (n:=n) a
  have H:=ConvexProximal.ae_quadraticExpansion_semiconvex_open K isOpen_ball (hs u hu) volume
  rw [←hdual.2] at H
  let good:=fun x:Model n=> ∃p:Model n,∃A:Model n →L[ℝ] Model n,
      (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (x+h))) p A
  let N: Set (Model n):={x | x∈Metric.ball (extChartAt 𝓘(ℝ,Model n) a a) r ∧ ¬good x}
  refine ⟨r,hr,N,?_,ht,?_⟩
  · have H':∀ᵐ x:Model n ∂volume,x∉N := H.mono (fun x hx ⟨hb,hbad⟩=>hbad (hx hb))
    rw [ae_iff] at H'
    convert H' using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq,not_not]
  · intro x hx hN
    by_contra hn
    exact hN ⟨hx,hn⟩
end ChartAlexandrov
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ChartLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

lemma chart_spray_hasDerivAt (a : M) (z : TangentBundle 𝓘(ℝ,Model n) M) {t : ℝ}
    (ht : (sprayFlow t z).1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    HasDerivAt (fun s => extChartAt 𝓘(ℝ,Model n) a (sprayFlow s z).1)
      (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a)
        (sprayFlow t z).1 (sprayFlow t z).2) t := by
  have hsrc : (sprayFlow t z).1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using ht
  have projectedDeriv :=
    (ContinuousLinearMap.fst ℝ (Model n) (Model n)).hasFDerivAt.comp_hasDerivAt t
      (sprayFlow_chart_hasDerivAt (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z ht)
  change HasDerivAt (fun s => extChartAt 𝓘(ℝ,Model n) a (sprayFlow s z).1)
    (tangentCoordChange 𝓘(ℝ,Model n) (sprayFlow t z).1 a
      (sprayFlow t z).1 (sprayFlow t z).2) t at projectedDeriv
  apply projectedDeriv.congr_deriv
  symm
  change (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (chartAt (Model n) a)
    (sprayFlow t z).1) (sprayFlow t z).2 = _
  rw [mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

variable [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_lipschitzOn_chart (a : M) :
    ∃ C : ℝ≥0, ∃ r>0, ball a r⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) (ball a r) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hC,H⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ,Model n) a
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) H)
  let Cnn : ℝ≥0 := ⟨C,hC.le⟩
  refine ⟨Cnn,R/3,by positivity,?_,?_⟩
  · exact fun x hx => (hsub ((ball_subset_ball (by linarith : R/3≤R)) hx)).1
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) x y
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  have hpN : ‖p‖=dist x y := by rw [←he]; exact hp.symm
  have hpath : ∀ t∈Icc (0:ℝ) 1, (sprayFlow t z).1∈ball a R := by
    intro t ht
    have hD := dist_sprayFlow_le z 0 t
    simp only [sprayFlow_zero,zero_sub,abs_neg,abs_of_nonneg ht.1] at hD
    change dist x (sprayFlow t z).1≤t*‖p‖ at hD
    have hD' : dist x (sprayFlow t z).1≤dist x y :=
      hD.trans (by rw [←hpN]; exact mul_le_of_le_one_left (norm_nonneg _) ht.2)
    have hxy := dist_triangle x a y
    have hax : dist x a<R/3 := hx
    have hay : dist y a<R/3 := hy
    have htri := dist_triangle (sprayFlow t z).1 x a
    rw [dist_comm (sprayFlow t z).1 x] at htri
    rw [dist_comm a y] at hxy
    change dist (sprayFlow t z).1 a<R
    linarith
  let γ := fun t : ℝ => extChartAt 𝓘(ℝ,Model n) a (sprayFlow t z).1
  let dγ : ℝ → Model n := fun t => mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n)
    (extChartAt 𝓘(ℝ,Model n) a) (sprayFlow t z).1 (sprayFlow t z).2
  have hd : ∀ t∈Icc (0:ℝ) 1, HasDerivWithinAt γ (dγ t) (Icc 0 1) t := by
    intro t ht
    exact (chart_spray_hasDerivAt a z (hsub (hpath t ht)).1).hasDerivWithinAt
  have hb : ∀ t∈Icc (0:ℝ) 1, ‖dγ t‖≤C*‖p‖ := by
    intro t ht
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    rw [sprayFlow_speed]
    exact mul_le_mul_of_nonneg_right (hsub (hpath t ht)).2.le (norm_nonneg _)
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hd (fun t ht => hb t ⟨ht.1,ht.2.le⟩)
  have he1 : (sprayFlow 1 z).1=y := by
    simpa only [z,←riemannianExp_eq_sprayFlow] using he
  have he0 : (sprayFlow 0 z).1=x := by rw [sprayFlow_zero]
  change dist (extChartAt 𝓘(ℝ,Model n) a x) (extChartAt 𝓘(ℝ,Model n) a y)≤C*dist x y
  simpa only [γ,he1,he0,←dist_eq_norm,dist_comm,hpN] using hfin

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_EuclideanVolumeFactorNe
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner _root_.OAI.WeakMTWTransport.riemannianExp_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Metric Bundle
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma euclideanVolumeFactor_ne_zero (n : ℕ) : euclideanVolumeFactor n≠0 := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact ENNReal.div_ne_zero.mpr ⟨(measure_ball_pos volume (0:Model n) zero_lt_one).ne',
    measure_ball_lt_top.ne⟩

lemma euclideanVolumeFactor_ne_top (n : ℕ) : euclideanVolumeFactor n≠⊤ := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact ENNReal.div_ne_top measure_ball_lt_top.ne
    (measure_ball_pos _ (0:Model n) zero_lt_one).ne'

instance metricVolume_model_haar (n : ℕ) :
    (metricVolume (M := Model n) n).IsAddHaarMeasure := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact Measure.IsAddHaarMeasure.smul _ (euclideanVolumeFactor_ne_zero n)
    (euclideanVolumeFactor_ne_top n)

lemma lipschitzOn_metricVolume_image_le {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {C : ℝ≥0} {f : X → Y} {s : Set X} (hf : LipschitzOnWith C f s) (n : ℕ) :
    metricVolume n (f '' s)≤(C:ℝ≥0∞)^n*metricVolume n s := by
  have H := hf.hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
  have hh := mul_le_mul_right H (euclideanVolumeFactor n)
  simpa only [metricVolume,Measure.smul_apply,smul_eq_mul,ENNReal.rpow_natCast,
    mul_assoc,mul_comm,mul_left_comm] using hh

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_OriginalNullSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal

namespace WeakMTWTransport
section OriginalNullSet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma original_ae_chart_null {P:M → Prop} (hP:∀ᵐ x ∂metricVolume n,P x) (a:M) :
    ∃r>0,∃N:Set (Model n),volume N=0 ∧
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,z∉N →
        P ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨C,R,hR,hS,hC⟩:=exists_lipschitzOn_chart (n:=n) a
  have ht:χ a∈χ.target:=mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a
  have hi:ContinuousAt χ.symm (χ a):=continuousAt_extChartAt_symm'' ht
  have he:χ.symm (χ a)=a:=χ.left_inv (mem_extChartAt_source a)
  obtain ⟨r,hr,hsub⟩:=Metric.mem_nhds_iff.mp (inter_mem
    ((isOpen_extChartAt_target a).mem_nhds ht)
    (hi.preimage_mem_nhds (he.symm ▸ ball_mem_nhds a hR)))
  let B:Set M:=ball a R ∩ {x | ¬P x}
  let N:Set (Model n):=χ '' B
  have hB:metricVolume n B=0:=measure_mono_null inter_subset_right (ae_iff.mp hP)
  have hN:volume N=0:=by
    apply (Measure.absolutelyContinuous_isAddHaarMeasure volume (metricVolume (M:=Model n) n))
    apply le_antisymm _ zero_le
    have H:=lipschitzOn_metricVolume_image_le (hC.mono (show B⊆ball a R from inter_subset_left)) n
    rw [hB,mul_zero] at H
    exact H
  refine ⟨r,hr,N,hN,fun z hz=>(hsub hz).1,?_⟩
  intro z hz hn
  by_contra hp
  apply hn
  exact ⟨χ.symm z,⟨by
    have hb:= (hsub hz).2
    change dist (χ.symm z) (χ.symm (χ a)) < R at hb
    rw [he] at hb
    exact hb,hp⟩,χ.right_inv (hsub hz).1⟩

omit [Nonempty M] in
lemma original_chart_good_null_oai {P:M → Prop} (hP:∀ᵐ x ∂metricVolume n,P x)
    {u v:M → ℝ} (hu:Continuous u) (hdual:IsCostDualPair u v) (a:M) :
    ∃r>0,∃N:Set (Model n),volume N=0 ∧
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,z∉N →
        P ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
        ∃p:Model n,∃A:Model n →L[ℝ] Model n,
          (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
          HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h))) p A := by
  obtain ⟨r,hr,N,hN,ht,hg⟩:=original_ae_chart_null (n:=n) hP a
  obtain ⟨s,hs,Q,hQ,hst,hq⟩:=original_chart_alexandrov_null (n:=n) hu hdual a
  refine ⟨min r s,lt_min hr hs,N∪Q,measure_union_null hN hQ,?_,?_⟩
  · exact (ball_subset_ball (min_le_left _ _)).trans ht
  · intro z hz hn
    have hNr:z∉N:=fun hm=>hn (Or.inl hm)
    have hQr:z∉Q:=fun hm=>hn (Or.inr hm)
    exact ⟨hg z (ball_subset_ball (min_le_left _ _) hz) hNr,
      hq z (ball_subset_ball (min_le_right _ _) hz) hQr⟩
end OriginalNullSet
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.original_chart_good_null_oai.{u_1} := @OAI.WeakMTWTransport.original_chart_good_null_oai.{u_1}
