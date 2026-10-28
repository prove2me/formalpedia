-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_local_weighted_carleman
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:09:42.583092+00:00
-- url     : https://prove2.me/submissions/3d8e3683-1b73-43a7-aaf9-4e13d8bb2c51

import Mathlib
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TestDerivativeComm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace SmoothScalar
variable (v : E)
lemma directional_mul (f g : SmoothScalar E) :
    directional v (f * g) = directional v f * g + f * directional v g := by
  apply Subtype.ext
  ext x
  change fderiv ℝ ((f : E → ℝ) * (g : E → ℝ)) x v = _
  rw [fderiv_mul ((SmoothScalar.contDiff f).differentiable (by simp)).differentiableAt
    ((SmoothScalar.contDiff g).differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply,
    smul_eq_mul, Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply,
    directional_apply]
  ring
end SmoothScalar

variable (K : Compacts E)

lemma testProductRule (v : E) (a : SmoothScalar E) (f : EllipticTest K) :
    testDerivative K v (testMultiply K a f) =
      testMultiply K (SmoothScalar.directional v a) f + testMultiply K a (testDerivative K v f) := by
  ext x
  have he : (testMultiply K a f : E → ℝ) = fun x => a x * f x := by ext y; simp
  simp only [testDerivative_apply, he]
  change fderiv ℝ ((a : E → ℝ) * (f : E → ℝ)) x v = _
  rw [fderiv_mul ((SmoothScalar.contDiff a).differentiable (by simp)).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul,
    testMultiply_apply, SmoothScalar.directional_apply,
    testDerivative_apply]
  ring

lemma testMultiply_add (a b : SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (a + b) f = testMultiply K a f + testMultiply K b f := by
  ext x
  simp only [testMultiply_apply, Subalgebra.coe_add, Pi.add_apply, add_apply, add_mul]
lemma testMultiply_smul (c : ℝ) (a : SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (c • a) f = c • testMultiply K a f := by
  ext x
  simp only [testMultiply_apply, Subalgebra.coe_smul, Pi.smul_apply, smul_apply, smul_eq_mul, mul_assoc]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma testPair_integrable (f g : EllipticTest K) :
    Integrable (fun x => f x * g x) (volume : Measure E) :=
  (f.contDiff.continuous.mul g.contDiff.continuous).integrable_of_hasCompactSupport
    (f.compact_supp.mul_right)

lemma testPair_comm (f g : EllipticTest K) : testPair K f g = testPair K g f := by
  simp only [testPair, mul_comm]
lemma testPair_add_left (f g h : EllipticTest K) :
    testPair K (f + g) h = testPair K f h + testPair K g h := by
  simp only [testPair, FunLike.coe_add, Pi.add_apply, add_mul]
  exact integral_add (testPair_integrable K f h) (testPair_integrable K g h)
lemma testPair_smul_left (c : ℝ) (f g : EllipticTest K) :
    testPair K (c • f) g = c * testPair K f g := by
  simp only [testPair, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _
lemma testPair_nonneg (f : EllipticTest K) : 0 ≤ testPair K f f :=
  integral_nonneg (fun _ => mul_self_nonneg _)

lemma testDerivative_skew (v : E) (f g : EllipticTest K) :
    testPair K (testDerivative K v f) g = -testPair K f (testDerivative K v g) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure E)) (v := v) (f := (f : E → ℝ)) (g := (g : E → ℝ))
    (testPair_integrable K (testDerivative K v f) g)
    (testPair_integrable K f (testDerivative K v g))
    (testPair_integrable K f g)
    (fun x _ => (f.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _ => (g.contDiff.differentiable (by simp)).differentiableAt)
  change testPair K f (testDerivative K v g) = -testPair K (testDerivative K v f) g at h
  linarith

lemma testMultiply_symmetric (a : SmoothScalar E) (f g : EllipticTest K) :
    testPair K (testMultiply K a f) g = testPair K f (testMultiply K a g) := by
  unfold testPair
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [testMultiply_apply]
  ring

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E)

lemma testDerivative_comm (v w : E) (f : EllipticTest K) :
    testDerivative K v (testDerivative K w f) = testDerivative K w (testDerivative K v f) := by
  ext x
  have hdf := (f.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hfun (z : E) : (testDerivative K z f : E → ℝ) = fun y => fderiv ℝ f y z := by
    ext y; rfl
  simp only [testDerivative_apply, hfun,
    fderiv_clm_apply hdf.differentiableAt (differentiableAt_const w),
    fderiv_clm_apply hdf.differentiableAt (differentiableAt_const v)]
  simpa using (f.contDiff.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))).eq v w

lemma testMultiply_mul (a b : SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (a * b) f = testMultiply K a (testMultiply K b f) := by
  ext x
  simp only [testMultiply_apply, Subalgebra.coe_mul, Pi.mul_apply, mul_assoc]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma testPair_add_right (f g h : EllipticTest K) :
    testPair K f (g + h) = testPair K f g + testPair K f h := by
  rw [testPair_comm, testPair_add_left, testPair_comm K g, testPair_comm K h]
lemma testPair_smul_right (c : ℝ) (f g : EllipticTest K) :
    testPair K f (c • g) = c * testPair K f g := by
  rw [testPair_comm, testPair_smul_left, testPair_comm]
lemma testPair_neg_left (f g : EllipticTest K) : testPair K (-f) g = -testPair K f g := by
  simpa only [neg_one_smul, neg_one_mul] using testPair_smul_left K (-1) f g
lemma testPair_neg_right (f g : EllipticTest K) : testPair K f (-g) = -testPair K f g := by
  rw [testPair_comm, testPair_neg_left, testPair_comm]
lemma testPair_sub_left (f g h : EllipticTest K) :
    testPair K (f-g) h = testPair K f h - testPair K g h := by
  simp only [sub_eq_add_neg, testPair_add_left, testPair_neg_left]
lemma testPair_sub_right (f g h : EllipticTest K) :
    testPair K f (g-h) = testPair K f g - testPair K f h := by
  simp only [sub_eq_add_neg, testPair_add_right, testPair_neg_right]
lemma testPair_sum_left {ι : Type*} (s : Finset ι) (f : ι → EllipticTest K) (g : EllipticTest K) :
    testPair K (∑ i ∈ s, f i) g = ∑ i ∈ s, testPair K (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, testPair_add_left, ih]
lemma testPair_sum_right {ι : Type*} (s : Finset ι) (f : EllipticTest K) (g : ι → EllipticTest K) :
    testPair K f (∑ i ∈ s, g i) = ∑ i ∈ s, testPair K f (g i) := by
  rw [testPair_comm, testPair_sum_left]
  congr 1
  ext i
  exact testPair_comm K _ _

lemma testPair_weighted_derivative (a : SmoothScalar E) (v : E) (f g : EllipticTest K) :
    testPair K (testMultiply K a (testDerivative K v f)) g +
      testPair K (testMultiply K a f) (testDerivative K v g) =
      -testPair K (testMultiply K (SmoothScalar.directional v a) f) g := by
  have h := testDerivative_skew K v (testMultiply K a f) g
  rw [testProductRule, testPair_add_left] at h
  linarith

lemma testPair_weighted_self_derivative (a : SmoothScalar E) (v : E) (f : EllipticTest K) :
    2 * testPair K (testMultiply K a f) (testDerivative K v f) =
      -testPair K (testMultiply K (SmoothScalar.directional v a) f) f := by
  have h := testPair_weighted_derivative K a v f f
  rw [testMultiply_symmetric, testPair_comm K (testDerivative K v f)] at h
  linarith



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_TestElliptic
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι]
variable (e : ι → E)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma testElliptic_pair (a : ι → ι → SmoothScalar E) (f g : EllipticTest K) :
    testPair K (testElliptic K e a f) g = -testEnergy K e a f g := by
  simp only [testElliptic, LinearMap.sum_apply, LinearMap.comp_apply, testPair_sum_left,
    testDerivative_skew, Finset.sum_neg_distrib, testEnergy]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma testMultiply_sum {η : Type*} (s : Finset η) (a : η → SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (∑ i ∈ s, a i) f = ∑ i ∈ s, testMultiply K (a i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext x
    simp [testMultiply_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, testMultiply_add, ih]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WeightedPair
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma weightedPair_symm (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K a f g = weightedPair K a g f := by
  unfold weightedPair
  rw [testMultiply_symmetric, testPair_comm]
lemma weightedPair_add_coeff (a b : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (a+b) f g = weightedPair K a f g + weightedPair K b f g := by
  simp only [weightedPair, testMultiply_add, testPair_add_left]
lemma weightedPair_smul_coeff (c : ℝ) (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (c • a) f g = c * weightedPair K a f g := by
  simp only [weightedPair, testMultiply_smul, testPair_smul_left]
lemma weightedPair_sum_coeff {ι : Type*} (s : Finset ι) (a : ι → SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (∑ i ∈ s, a i) f g = ∑ i ∈ s, weightedPair K (a i) f g := by
  simp only [weightedPair, testMultiply_sum, testPair_sum_left]
lemma weightedPair_add_right (a : SmoothScalar E) (f g h : EllipticTest K) :
    weightedPair K a f (g+h) = weightedPair K a f g + weightedPair K a f h := by
  simp only [weightedPair, testPair_add_right]
lemma weightedPair_sum_right {ι : Type*} (s : Finset ι) (a : SmoothScalar E)
    (f : EllipticTest K) (g : ι → EllipticTest K) :
    weightedPair K a f (∑ i ∈ s, g i) = ∑ i ∈ s, weightedPair K a f (g i) := by
  simp only [weightedPair, testPair_sum_right]
lemma weightedPair_mul (a b : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K a f (testMultiply K b g) = weightedPair K (a*b) f g := by
  unfold weightedPair
  rw [← testMultiply_symmetric, ← testMultiply_mul, mul_comm b a]
lemma weightedPair_derivative (a : SmoothScalar E) (v : E) (f g : EllipticTest K) :
    weightedPair K a (testDerivative K v f) g + weightedPair K a f (testDerivative K v g) =
      -weightedPair K (SmoothScalar.directional v a) f g :=
  testPair_weighted_derivative K a v f g
lemma weightedPair_self_derivative (a : SmoothScalar E) (v : E) (f : EllipticTest K) :
    2 * weightedPair K a f (testDerivative K v f) =
      -weightedPair K (SmoothScalar.directional v a) f f :=
  testPair_weighted_self_derivative K a v f
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CoefficientElliptic
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma testElliptic_multiplier_pair (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (q : SmoothScalar E) (f : EllipticTest K) :
    2 * testPair K (testElliptic K e a f) (testMultiply K q f) =
      weightedPair K (coefficientElliptic e a q) f f -
        2 * ∑ i, ∑ j, weightedPair K (a i j * q)
          (testDerivative K (e j) f) (testDerivative K (e i) f) := by
  have hcross (i j : ι) :
      2 * weightedPair K (a i j * SmoothScalar.directional (e i) q)
        (testDerivative K (e j) f) f =
      -weightedPair K (SmoothScalar.directional (e j)
        (a i j * SmoothScalar.directional (e i) q)) f f := by
    rw [weightedPair_symm K _ (testDerivative K (e j) f)]
    exact weightedPair_self_derivative K _ (e j) f
  rw [testElliptic_pair]
  unfold testEnergy
  simp only [show ∀ a g h, testPair K (testMultiply K a g) h = weightedPair K a g h from fun _ _ _ => rfl,
    testProductRule, weightedPair_add_right, weightedPair_mul, Finset.sum_add_distrib,
    mul_neg, Finset.mul_sum]
  have he : weightedPair K (coefficientElliptic e a q) f f =
      ∑ i, ∑ j, weightedPair K (SmoothScalar.directional (e j)
        (a i j * SmoothScalar.directional (e i) q)) f f := by
    simp only [coefficientElliptic, weightedPair_sum_coeff]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
  rw [he]
  have hc : 2 * (∑ i, ∑ j, weightedPair K (a i j * SmoothScalar.directional (e i) q)
      (testDerivative K (e j) f) f) =
      -(∑ i, ∑ j, weightedPair K (SmoothScalar.directional (e j)
        (a i j * SmoothScalar.directional (e i) q)) f f) := by
    simp only [Finset.mul_sum, hcross, Finset.sum_neg_distrib]
  simp only [← Finset.mul_sum]
  linarith

lemma testElliptic_transport_pair (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (f : EllipticTest K) :
    2 * testPair K (testElliptic K e a f) (testTransport K e X f) =
      -2 * (∑ i, ∑ j, ∑ k, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f)) +
      ∑ i, ∑ j, ∑ k, weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f) := by
  let T (i j k : ι) := weightedPair K (a i j * X k) (testDerivative K (e j) f)
    (testDerivative K (e k) (testDerivative K (e i) f))
  have hT (i j k : ι) : T i j k + T j i k =
      -weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f) := by
    dsimp only [T]
    rw [ha j i, weightedPair_symm K _ (testDerivative K (e i) f)]
    have hh := weightedPair_derivative K (a i j * X k) (e k)
      (testDerivative K (e j) f) (testDerivative K (e i) f)
    linarith
  have hswap : (∑ i, ∑ j, ∑ k, T j i k) = ∑ i, ∑ j, ∑ k, T i j k :=
    Finset.sum_comm
  have hcancel : 2 * (∑ i, ∑ j, ∑ k, T i j k) =
      -(∑ i, ∑ j, ∑ k, weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) := by
    calc
      _ = (∑ i, ∑ j, ∑ k, (T i j k + T j i k)) := by
        simp only [Finset.sum_add_distrib, hswap]; ring
      _ = _ := by simp only [hT, Finset.sum_neg_distrib]
  rw [testElliptic_pair]
  unfold testEnergy testTransport
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, weightedPair_sum_right,
    testProductRule, weightedPair_add_right,
    show ∀ a g h, testPair K (testMultiply K a g) h = weightedPair K a g h from fun _ _ _ => rfl,
    weightedPair_mul,
    Finset.sum_add_distrib]
  have hreorder (i j k : ι) : weightedPair K (a i j * X k)
      (testDerivative K (e j) f) (testDerivative K (e i) (testDerivative K (e k) f)) =
      T i j k := by
    rw [testDerivative_comm K (e i) (e k)]
  simp only [hreorder]
  linarith
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology

lemma continuous_quadratic_coercive {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (q : V → ℝ) (hq : Continuous q)
    (hhom : ∀ (c : ℝ) (v : V), q (c • v) = c^2 * q v)
    (hpos : ∀ v ≠ 0, 0 < q v) : ∃ μ > 0, ∀ v, μ * ‖v‖^2 ≤ q v := by
  have hzero : q 0 = 0 := by simpa using hhom 0 0
  cases subsingleton_or_nontrivial V with
  | inl h =>
    let := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    rw [Subsingleton.elim v 0, norm_zero, hzero]
    norm_num
  | inr h =>
    let := h
    obtain ⟨v, hv⟩ : ∃ v : V, ‖v‖ = 1 := by
      obtain ⟨w, hw⟩ := exists_ne (0 : V)
      refine ⟨‖w‖⁻¹ • w, ?_⟩
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      ⟨v, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩ hq.continuousOn
    have hv₀norm : ‖v₀‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv₀
    have hv₀ne : v₀ ≠ 0 := by intro hz; simp [hz] at hv₀norm
    refine ⟨q v₀, hpos v₀ hv₀ne, ?_⟩
    intro w
    by_cases hw : w = 0
    · simp [hw, hzero]
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hwn.le), inv_mul_cancel₀ hwn.ne']
    have hh := hmin (show ‖w‖⁻¹ • w ∈ Metric.sphere (0 : V) 1 by
      simpa [Metric.mem_sphere, dist_zero_right] using hunit)
    change q v₀ ≤ q (‖w‖⁻¹ • w) at hh
    rw [hhom] at hh
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖w‖)
    calc
      _ ≤ (‖w‖⁻¹)^2 * q w * ‖w‖^2 := hh'
      _ = q w := by field_simp

variable {ι : Type*} [Fintype ι]

lemma realQuadratic_hom (a : ι → ι → ℝ) (c : ℝ) (v : ι → ℝ) :
    realQuadratic a (c • v) = c^2 * realQuadratic a v := by
  simp only [realQuadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma matrix_positive_coercive (a : Matrix ι ι ℝ) (ha : a.PosDef) :
    ∃ μ > 0, ∀ v : ι → ℝ, μ * squareSum v ≤ realQuadratic a v := by
  let q : EuclideanSpace ℝ ι → ℝ := fun v => realQuadratic a v
  have hc : Continuous q := by
    unfold q realQuadratic
    fun_prop
  have hp : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 → 0 < q v := by
    intro v hv
    have he : (fun i => v i) ≠ 0 := by
      intro hz
      apply hv
      ext i
      exact congrFun hz i
    have h := ha.dotProduct_mulVec_pos he
    dsimp [q, realQuadratic]
    simpa only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum,
      mul_left_comm, mul_assoc] using h
  have hh : ∀ (c : ℝ) (v : EuclideanSpace ℝ ι), q (c • v) = c^2*q v :=
    fun c v => realQuadratic_hom a c v
  obtain ⟨μ, hμ, hbound⟩ := continuous_quadratic_coercive q hc hh hp
  refine ⟨μ, hμ, fun v => ?_⟩
  have hb := hbound (WithLp.toLp 2 v)
  rw [EuclideanSpace.real_norm_sq_eq] at hb
  simpa only [q, squareSum, sq, PiLp.toLp_apply] using hb

lemma squareSum_nonneg (v : ι → ℝ) : 0 ≤ squareSum v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma abs_mul_le_squareSum (v : ι → ℝ) (i j : ι) : |v i * v j| ≤ squareSum v := by
  have hi : v i * v i ≤ squareSum v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ i)
  have hj : v j * v j ≤ squareSum v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (v i + v j), sq_nonneg (v i - v j)]

lemma realQuadratic_abs_bound (a : ι → ι → ℝ) (v : ι → ℝ) :
    |realQuadratic a v| ≤ (∑ i, ∑ j, |a i j|) * squareSum v := by
  unfold realQuadratic
  calc
    _ ≤ ∑ i, |∑ j, a i j * v i * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i j * v i * v j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_mul_le_squareSum v i j) (abs_nonneg _)

lemma realQuadratic_sub (a b : ι → ι → ℝ) (v : ι → ℝ) :
    realQuadratic (a-b) v = realQuadratic a v - realQuadratic b v := by
  simp only [realQuadratic, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma continuous_matrix_lower_near {T : Type*} [TopologicalSpace T]
    (a : T → ι → ι → ℝ) (ha : ∀ i j, Continuous (fun x => a x i j)) (x₀ : T)
    (hlower : ∀ v, 2 * squareSum v ≤ realQuadratic (a x₀) v) :
    ∀ᶠ x in nhds x₀, ∀ v, squareSum v ≤ realQuadratic (a x) v := by
  let variation : T → ℝ := fun x => ∑ i, ∑ j, |a x₀ i j - a x i j|
  have hc : Continuous variation := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (continuous_const.sub (ha i j)).abs
  have hzero : variation x₀ = 0 := by simp [variation]
  have he : ∀ᶠ x in nhds x₀, variation x < 1 :=
    (hc.tendsto x₀).eventually_lt_const (by rw [hzero]; norm_num)
  filter_upwards [he] with x hx v
  have hb := realQuadratic_abs_bound (a x₀ - a x) v
  rw [realQuadratic_sub] at hb
  change |realQuadratic (a x₀) v - realQuadratic (a x) v| ≤ variation x * squareSum v at hb
  have hh := mul_le_mul_of_nonneg_right hx.le (squareSum_nonneg v)
  have hh' := (le_abs_self (realQuadratic (a x₀) v - realQuadratic (a x) v)).trans hb
  linarith [hlower v]


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_DistanceSquare
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma testMultiplier_skew_pair (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (f : EllipticTest K) :
    testPair K (testMultiply K p f) (testSkewTransport K e X f) =
      -weightedPair K (coefficientTransport e X p) f f := by
  have h (i : ι) := weightedPair_self_derivative K (p * X i) (e i) f
  simp only [SmoothScalar.directional_mul, weightedPair_add_coeff] at h
  simp only [testSkewTransport, LinearMap.add_apply, LinearMap.smul_apply,
    testPair_add_right, testPair_smul_right, testTransport, LinearMap.sum_apply,
    LinearMap.comp_apply, testPair_sum_right]
  change 2 * (∑ i, weightedPair K p f (testMultiply K (X i) (testDerivative K (e i) f))) +
    weightedPair K p f (testMultiply K (coefficientDivergence e X) f) = _
  simp only [weightedPair_mul, coefficientDivergence, Finset.mul_sum,
    weightedPair_sum_coeff, coefficientTransport]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (X i)]
  linarith [h i]

lemma derivative_product_energy (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (f : EllipticTest K) :
    (∑ i, ∑ j, ∑ k, weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) =
      (∑ i, ∑ j, ∑ k, weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) +
      ∑ i, ∑ j, weightedPair K (a i j * coefficientDivergence e X)
        (testDerivative K (e j) f) (testDerivative K (e i) f) := by
  simp only [SmoothScalar.directional_mul, weightedPair_add_coeff,
    Finset.sum_add_distrib, coefficientDivergence, Finset.mul_sum, weightedPair_sum_coeff]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem carleman_commutator (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (τ : ℝ) (f : EllipticTest K) :
    2 * testPair K (carlemanSymmetric K e a p τ f) (carlemanSkew K e X τ f) =
      τ * (4 * (∑ i, ∑ j, ∑ k,
          weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
            (testDerivative K (e j) f) (testDerivative K (e k) f)) -
        2 * (∑ i, ∑ j, ∑ k,
          weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
            (testDerivative K (e j) f) (testDerivative K (e i) f)) -
        weightedPair K (coefficientElliptic e a (coefficientDivergence e X)) f f) +
      2 * τ^3 * weightedPair K (coefficientTransport e X p) f f := by
  have hT := testElliptic_transport_pair K e a ha X f
  have hq := testElliptic_multiplier_pair K e a ha (coefficientDivergence e X) f
  have hp := testMultiplier_skew_pair K e X p f
  rw [derivative_product_energy K e a X f] at hT
  simp only [carlemanSymmetric, carlemanSkew, LinearMap.add_apply, LinearMap.smul_apply,
    testPair_smul_right, testPair_add_left, testPair_smul_left, hp]
  simp only [testSkewTransport, LinearMap.add_apply, LinearMap.smul_apply,
    testPair_add_right, testPair_smul_right]
  linear_combination -τ * (2 * hT + hq)

lemma testPair_cauchy_shift (f g : EllipticTest K) (c : ℝ) :
    -2 * c * testPair K f g - c^2 * testPair K g g ≤ testPair K f f := by
  have h := testPair_nonneg K (f + c • g)
  simp only [testPair_add_left, testPair_add_right, testPair_smul_left,
    testPair_smul_right, testPair_comm K g f] at h
  nlinarith


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

lemma SmoothScalar.sum_apply {κ : Type*} (s : Finset κ) (f : κ → SmoothScalar E) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Subalgebra.coe_zero, Pi.zero_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Subalgebra.coe_add, Pi.add_apply, ih]

lemma phase_derivative (ψ : SmoothScalar E) (H : ℝ) (v : E) :
    SmoothScalar.directional v (convexifyPhase ψ H) =
      (1 + H • ψ) * SmoothScalar.directional v ψ := by
  simp only [convexifyPhase, map_add, map_smul, SmoothScalar.directional_mul]
  apply Subtype.ext
  ext x
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_one,
    Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
  ring

lemma phase_gradient (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ) (i : ι) :
    coefficientGradient e a (convexifyPhase ψ H) i =
      (1 + H • ψ) * coefficientGradient e a ψ i := by
  simp only [coefficientGradient, phase_derivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma phase_norm (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ) :
    coefficientNorm e a (convexifyPhase ψ H) =
      (1 + H • ψ)^2 * coefficientNorm e a ψ := by
  simp only [coefficientNorm, phase_derivative, phase_gradient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma SmoothScalar.directional_one (v : E) : SmoothScalar.directional v (1 : SmoothScalar E) = 0 := by
  apply Subtype.ext
  ext x
  simp [SmoothScalar.directional_apply]

lemma phase_gradient_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) (i : ι) :
    coefficientGradient e a (convexifyPhase ψ H) i x = coefficientGradient e a ψ i x := by
  rw [phase_gradient]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
    Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, hx,
    mul_zero, add_zero, one_mul]

lemma phase_norm_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) :
    coefficientNorm e a (convexifyPhase ψ H) x = coefficientNorm e a ψ x := by
  rw [phase_norm]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
    Subalgebra.coe_pow, Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
    Pi.pow_apply, smul_eq_mul, hx, mul_zero, add_zero, one_pow, one_mul]

lemma phase_gradient_derivative_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) (i j : ι) :
    SmoothScalar.directional (e j) (coefficientGradient e a (convexifyPhase ψ H) i) x =
      SmoothScalar.directional (e j) (coefficientGradient e a ψ i) x +
        H * SmoothScalar.directional (e j) ψ x * coefficientGradient e a ψ i x := by
  rw [phase_gradient, SmoothScalar.directional_mul, map_add, map_smul,
    SmoothScalar.directional_one]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
    Subalgebra.coe_zero, Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul, hx]
  ring

lemma phase_transport_norm_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) :
    coefficientTransport e (coefficientGradient e a (convexifyPhase ψ H))
        (coefficientNorm e a (convexifyPhase ψ H)) x =
      coefficientTransport e (coefficientGradient e a ψ) (coefficientNorm e a ψ) x +
        2*H*(coefficientNorm e a ψ x)^2 := by
  have hd (i : ι) :
      SmoothScalar.directional (e i) (coefficientNorm e a (convexifyPhase ψ H)) x =
        SmoothScalar.directional (e i) (coefficientNorm e a ψ) x +
          2*H*SmoothScalar.directional (e i) ψ x * coefficientNorm e a ψ x := by
    rw [phase_norm, pow_two, SmoothScalar.directional_mul, SmoothScalar.directional_mul,
      map_add, map_smul, SmoothScalar.directional_one]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
      Subalgebra.coe_zero, Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul, hx]
    ring
  simp only [coefficientTransport, SmoothScalar.sum_apply,
    Subalgebra.coe_mul, Pi.mul_apply, phase_gradient_at e a ψ H x hx, hd,
    mul_add, Finset.sum_add_distrib]
  congr 1
  have hn : coefficientNorm e a ψ x =
      ∑ i, SmoothScalar.directional (e i) ψ x * coefficientGradient e a ψ i x := by
    simp only [coefficientNorm, SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]
  calc
    _ = 2*H*(∑ i, SmoothScalar.directional (e i) ψ x * coefficientGradient e a ψ i x) *
        coefficientNorm e a ψ x := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← hn]; ring


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma exponentialWeight_derivative (φ : SmoothScalar E) (τ : ℝ) (v : E) :
    SmoothScalar.directional v (exponentialWeight φ τ) =
      τ • (exponentialWeight φ τ * SmoothScalar.directional v φ) := by
  apply Subtype.ext
  ext x
  change fderiv ℝ (fun y => Real.exp (τ * φ y)) x v = _
  have hd := (((SmoothScalar.contDiff φ).differentiable (by simp) x).hasFDerivAt.const_mul τ).exp
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, Subalgebra.coe_smul, Subalgebra.coe_mul, Pi.smul_apply,
    Pi.mul_apply, SmoothScalar.directional_apply, exponentialWeight_apply]
  ring

lemma testMultiply_exponential_inverse (φ : SmoothScalar E) (τ : ℝ) (f : EllipticTest K) :
    testMultiply K (exponentialWeight φ (-τ)) (testMultiply K (exponentialWeight φ τ) f) = f := by
  ext x
  simp only [testMultiply_apply, exponentialWeight_apply, ← mul_assoc, ← Real.exp_add]
  simp

lemma coefficientElliptic_exponential (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (τ : ℝ) :
    coefficientElliptic e a (exponentialWeight φ τ) =
      exponentialWeight φ τ *
        (τ • coefficientDivergence e (coefficientGradient e a φ) +
          τ^2 • coefficientNorm e a φ) := by
  have hg (i : ι) : (∑ j, a i j * SmoothScalar.directional (e j) (exponentialWeight φ τ)) =
      τ • (exponentialWeight φ τ * coefficientGradient e a φ i) := by
    apply Subtype.ext
    ext x
    simp only [exponentialWeight_derivative, coefficientGradient, SmoothScalar.sum_apply,
      Subalgebra.coe_smul, Subalgebra.coe_mul, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : coefficientElliptic e a (exponentialWeight φ τ) =
      ∑ i, SmoothScalar.directional (e i)
        (∑ j, a i j * SmoothScalar.directional (e j) (exponentialWeight φ τ)) := by
    simp only [coefficientElliptic, map_sum]
  rw [he]
  simp_rw [hg]
  simp only [map_smul, SmoothScalar.directional_mul, exponentialWeight_derivative,
    coefficientDivergence, coefficientNorm,
    Finset.sum_add_distrib, smul_add, Finset.smul_sum, mul_add, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Subtype.ext
  ext x
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_mul,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

lemma testElliptic_product (a : ι → ι → SmoothScalar E) (ha : ∀ i j, a i j = a j i)
    (b : SmoothScalar E) (f : EllipticTest K) :
    testElliptic K e a (testMultiply K b f) =
      testMultiply K b (testElliptic K e a f) +
        (2:ℝ) • (∑ i, ∑ j, testMultiply K (a i j * SmoothScalar.directional (e i) b)
          (testDerivative K (e j) f)) + testMultiply K (coefficientElliptic e a b) f := by
  have hterm (i j : ι) :
      testDerivative K (e i) (testMultiply K (a i j) (testDerivative K (e j) (testMultiply K b f))) =
      testMultiply K b (testDerivative K (e i) (testMultiply K (a i j) (testDerivative K (e j) f))) +
      testMultiply K (a i j * SmoothScalar.directional (e i) b) (testDerivative K (e j) f) +
      testMultiply K (a i j * SmoothScalar.directional (e j) b) (testDerivative K (e i) f) +
      testMultiply K (SmoothScalar.directional (e i) (a i j * SmoothScalar.directional (e j) b)) f := by
    simp only [testProductRule, map_add, ← testMultiply_mul,
      SmoothScalar.directional_mul, testMultiply_add]
    ext x
    simp only [FunLike.coe_add, Pi.add_apply, testMultiply_apply,
      Subalgebra.coe_mul, Pi.mul_apply]
    ring
  have hcross : (∑ i, ∑ j, testMultiply K (a i j * SmoothScalar.directional (e j) b)
      (testDerivative K (e i) f)) =
      ∑ i, ∑ j, testMultiply K (a i j * SmoothScalar.directional (e i) b)
        (testDerivative K (e j) f) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
  simp only [testElliptic, LinearMap.sum_apply, LinearMap.comp_apply, hterm,
    Finset.sum_add_distrib, map_sum, coefficientElliptic, testMultiply_sum]
  rw [hcross]
  simp only [two_smul, add_assoc]

lemma testElliptic_exponential (a : ι → ι → SmoothScalar E) (ha : ∀ i j, a i j = a j i)
    (φ : SmoothScalar E) (τ : ℝ) (f : EllipticTest K) :
    testElliptic K e a (testMultiply K (exponentialWeight φ τ) f) =
      testMultiply K (exponentialWeight φ τ)
        (testElliptic K e a f + τ • testSkewTransport K e (coefficientGradient e a φ) f +
          τ^2 • testMultiply K (coefficientNorm e a φ) f) := by
  rw [testElliptic_product K e a ha, coefficientElliptic_exponential]
  have hcross : (∑ i, ∑ j, testMultiply K
      (a i j * SmoothScalar.directional (e i) (exponentialWeight φ τ)) (testDerivative K (e j) f)) =
      τ • testMultiply K (exponentialWeight φ τ) (testTransport K e (coefficientGradient e a φ) f) := by
    rw [Finset.sum_comm]
    simp only [exponentialWeight_derivative, testTransport, coefficientGradient,
      LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Finset.smul_sum,
      testMultiply_sum, ← testMultiply_mul, mul_smul_comm, testMultiply_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
    congr 2
    ring_nf
  rw [hcross]
  simp only [testMultiply_mul, testMultiply_add, testMultiply_smul, map_add, map_smul,
    testSkewTransport, LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul]
  module

lemma carleman_conjugation (a : ι → ι → SmoothScalar E) (ha : ∀ i j, a i j = a j i)
    (φ : SmoothScalar E) (τ : ℝ) (u : EllipticTest K) :
    carlemanSymmetric K e a (coefficientNorm e a φ) τ (testMultiply K (exponentialWeight φ τ) u) +
      carlemanSkew K e (coefficientGradient e a φ) τ (testMultiply K (exponentialWeight φ τ) u) =
      testMultiply K (exponentialWeight φ τ) (testElliptic K e a u) := by
  have h := testElliptic_exponential K e a ha φ (-τ) (testMultiply K (exponentialWeight φ τ) u)
  rw [testMultiply_exponential_inverse] at h
  apply_fun testMultiply K (exponentialWeight φ τ) at h
  have hi (f : EllipticTest K) :
      testMultiply K (exponentialWeight φ τ) (testMultiply K (exponentialWeight φ (-τ)) f) = f := by
    simpa only [neg_neg] using testMultiply_exponential_inverse K φ (-τ) f
  rw [hi] at h
  simpa only [carlemanSymmetric, carlemanSkew, LinearMap.add_apply, LinearMap.smul_apply,
    neg_sq, add_assoc, add_left_comm, add_comm] using h.symm


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoefficientGradientApply
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma weightedPair_integrable (a : SmoothScalar E) (f g : EllipticTest K) :
    Integrable (fun x => a x * f x * g x) (volume : Measure E) := by
  simpa only [testMultiply_apply] using testPair_integrable K (testMultiply K a f) g

lemma weightedPair_integral (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K a f g = ∫ x, a x * f x * g x := by
  simp only [weightedPair, testPair, testMultiply_apply]

lemma weightedPair_le_of_bound (a : SmoothScalar E) (C : ℝ)
    (h : ∀ x ∈ K, a x ≤ C) (f : EllipticTest K) :
    weightedPair K a f f ≤ C * testPair K f f := by
  rw [weightedPair_integral, testPair, ← integral_const_mul]
  apply integral_mono (weightedPair_integrable K a f f)
    ((testPair_integrable K f f).const_mul C)
  intro x
  by_cases hx : x ∈ K
  · nlinarith [mul_le_mul_of_nonneg_right (h x hx) (mul_self_nonneg (f x))]
  · have hf := f.zero_on_compl hx
    simp [hf]

lemma weightedPair_lower_shift (a b : SmoothScalar E) (C μ : ℝ)
    (h : ∀ x ∈ K, μ ≤ 2 * a x - 2 * C * b x) (f : EllipticTest K) :
    μ * testPair K f f ≤ 2 * weightedPair K a f f - 2 * C * weightedPair K b f f := by
  have hint : Integrable (fun x => 2 * (a x * f x * f x) - 2 * C * (b x * f x * f x))
      (volume : Measure E) :=
    ((weightedPair_integrable K a f f).const_mul 2).sub
      ((weightedPair_integrable K b f f).const_mul (2*C))
  rw [weightedPair_integral, weightedPair_integral, testPair, ← integral_const_mul,
    ← integral_const_mul, ← integral_const_mul, ← integral_sub]
  · apply integral_mono ((testPair_integrable K f f).const_mul μ) hint
    intro x
    by_cases hx : x ∈ K
    · nlinarith [mul_le_mul_of_nonneg_right (h x hx) (mul_self_nonneg (f x))]
    · have hf := f.zero_on_compl hx
      simp [hf]
  · exact (weightedPair_integrable K a f f).const_mul 2
  · exact (weightedPair_integrable K b f f).const_mul (2*C)

lemma carleman_basic_bound (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (τ C : ℝ) (f : EllipticTest K) :
    τ * (carlemanGradient K e a X f + 2*C * testEnergy K e a f f) +
      τ^3 * (2 * weightedPair K (coefficientTransport e X p) f f -
        2*C * weightedPair K p f f) -
      τ * weightedPair K (coefficientElliptic e a (coefficientDivergence e X)) f f -
      C^2 * τ^2 * testPair K f f ≤
    testPair K (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f)
      (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f) := by
  have hshift := testPair_cauchy_shift K (carlemanSymmetric K e a p τ f) f (C*τ)
  have hskew := testPair_nonneg K (carlemanSkew K e X τ f)
  have hcomm := carleman_commutator K e a ha X p τ f
  change 2 * testPair K (carlemanSymmetric K e a p τ f) (carlemanSkew K e X τ f) =
    τ * (carlemanGradient K e a X f -
      weightedPair K (coefficientElliptic e a (coefficientDivergence e X)) f f) +
    2 * τ^3 * weightedPair K (coefficientTransport e X p) f f at hcomm
  have hS : testPair K (carlemanSymmetric K e a p τ f) f =
      -testEnergy K e a f f + τ^2 * weightedPair K p f f := by
    simp only [carlemanSymmetric, LinearMap.add_apply, LinearMap.smul_apply,
      testPair_add_left, testPair_smul_left, testElliptic_pair, weightedPair]
  rw [hS] at hshift
  simp only [testPair_add_left, testPair_add_right,
    testPair_comm K (carlemanSkew K e X τ f) (carlemanSymmetric K e a p τ f)]
  nlinarith only [hshift, hskew, hcomm]

lemma carleman_coercive_of_bounds (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (τ C μ M : ℝ) (hτ : 0 ≤ τ) (f : EllipticTest K)
    (hg : μ * testGradientSquare K e f ≤
      carlemanGradient K e a X f + 2*C * testEnergy K e a f f)
    (hm : ∀ x ∈ K, μ ≤ 2 * coefficientTransport e X p x - 2*C*p x)
    (hq : ∀ x ∈ K, coefficientElliptic e a (coefficientDivergence e X) x ≤ M)
    (ht : τ*M + C^2*τ^2 ≤ (μ/2)*τ^3) :
    τ*μ*testGradientSquare K e f + (μ/2)*τ^3*testPair K f f ≤
      testPair K (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f)
        (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f) := by
  have h := carleman_basic_bound K e a ha X p τ C f
  have hg' := mul_le_mul_of_nonneg_left hg hτ
  have hm' := mul_le_mul_of_nonneg_left
    (weightedPair_lower_shift K (coefficientTransport e X p) p C μ hm f) (pow_nonneg hτ 3)
  have hq' := mul_le_mul_of_nonneg_left
    (weightedPair_le_of_bound K (coefficientElliptic e a (coefficientDivergence e X)) M hq f) hτ
  have ht' := mul_le_mul_of_nonneg_right ht (testPair_nonneg K f)
  nlinarith only [h, hg', hm', hq', ht']


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι]

lemma testQuadratic_integrable (a : ι → ι → SmoothScalar E) (f : ι → EllipticTest K) :
    Integrable (fun x => pointwiseQuadratic a x (fun i => f i x)) (volume : Measure E) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact weightedPair_integrable K (a i j) (f i) (f j)

lemma testQuadratic_integral (a : ι → ι → SmoothScalar E) (f : ι → EllipticTest K) :
    testQuadratic K a f = ∫ x, pointwiseQuadratic a x (fun i => f i x) := by
  unfold testQuadratic pointwiseQuadratic
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    weightedPair_integrable K (a i j) (f i) (f j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => weightedPair_integrable K (a i j) (f i) (f j))]
  apply Finset.sum_congr rfl
  intro j _
  exact weightedPair_integral K (a i j) (f i) (f j)

lemma testQuadratic_lower_bound (a : ι → ι → SmoothScalar E) (μ : ℝ)
    (h : ∀ x ∈ K, ∀ v : ι → ℝ, μ * ∑ i, v i * v i ≤ pointwiseQuadratic a x v)
    (f : ι → EllipticTest K) :
    μ * ∑ i, testPair K (f i) (f i) ≤ testQuadratic K a f := by
  have hi : Integrable (fun x => ∑ i, f i x * f i x) (volume : Measure E) :=
    integrable_finsetSum _ fun i _ => testPair_integrable K (f i) (f i)
  rw [testQuadratic_integral]
  have he : (∑ i, testPair K (f i) (f i)) = ∫ x, ∑ i, f i x * f i x := by
    simp only [testPair]
    rw [integral_finsetSum _ (fun i _ => testPair_integrable K (f i) (f i))]
  rw [he, ← integral_const_mul]
  apply integral_mono (hi.const_mul μ) (testQuadratic_integrable K a f)
  intro x
  by_cases hx : x ∈ K
  · exact h x hx (fun i => f i x)
  · have hf (i : ι) : f i x = 0 := (f i).zero_on_compl hx
    simp only [hf, mul_zero, Finset.sum_const_zero, pointwiseQuadratic, le_refl]

variable (e : ι → E)

lemma weightedPair_neg_coeff (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (-a) f g = -weightedPair K a f g := by
  simp only [weightedPair_integral]
  change (∫ point, -a point * f point * g point) = -(∫ point, a point * f point * g point)
  simp only [neg_mul, integral_neg]
lemma weightedPair_sub_coeff (a b : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (a-b) f g = weightedPair K a f g - weightedPair K b f g := by
  simp only [sub_eq_add_neg, weightedPair_add_coeff, weightedPair_neg_coeff]

lemma carlemanMatrix_quadratic (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C : ℝ) (f : EllipticTest K) :
    testQuadratic K (carlemanMatrix e a X C) (fun i => testDerivative K (e i) f) =
      carlemanGradient K e a X f + 2*C * testEnergy K e a f f := by
  simp only [testQuadratic, carlemanMatrix, weightedPair_add_coeff, weightedPair_sub_coeff,
    weightedPair_smul_coeff, weightedPair_sum_coeff, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, carlemanGradient, testEnergy,
    show ∀ a g h, testPair K (testMultiply K a g) h = weightedPair K a g h from fun _ _ _ => rfl]
  have h1 : (∑ j, ∑ k, ∑ i, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f)) =
      ∑ i, ∑ j, ∑ k, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f) := by
    calc
      _ = ∑ j, ∑ i, ∑ k, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
          (testDerivative K (e j) f) (testDerivative K (e k) f) :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have h2 : (∑ j, ∑ i, ∑ k, weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) =
      ∑ i, ∑ j, ∑ k, weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f) := Finset.sum_comm
  rw [h1, h2, Finset.sum_comm (f := fun j i => weightedPair K (a i j)
    (testDerivative K (e j) f) (testDerivative K (e i) f))]

lemma carleman_gradient_bound (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C μ : ℝ)
    (h : ∀ x ∈ K, ∀ v : ι → ℝ,
      μ * ∑ i, v i * v i ≤ pointwiseQuadratic (carlemanMatrix e a X C) x v)
    (f : EllipticTest K) :
    μ * testGradientSquare K e f ≤ carlemanGradient K e a X f + 2*C * testEnergy K e a f f := by
  rw [← carlemanMatrix_quadratic]
  exact testQuadratic_lower_bound K _ μ h _


end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

lemma coefficientGradient_apply (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (i : ι) (x : E) :
    coefficientGradient e a φ i x = ∑ j, a i j x * SmoothScalar.directional (e j) φ x := by
  simp only [coefficientGradient, SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]

lemma coefficientNorm_quadratic (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (x : E) :
    coefficientNorm e a φ x = realQuadratic (fun i j => a i j x)
      (fun i => SmoothScalar.directional (e i) φ x) := by
  simp only [coefficientNorm, SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply,
    coefficientGradient_apply, realQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coefficientNorm_pos (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (x : E)
    (ha : Matrix.PosDef (fun i j => a i j x))
    (hφ : (fun i => SmoothScalar.directional (e i) φ x) ≠ 0) :
    0 < coefficientNorm e a φ x := by
  have h := ha.dotProduct_mulVec_pos hφ
  rw [coefficientNorm_quadratic]
  simpa only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum,
    mul_left_comm, mul_assoc, realQuadratic] using h

lemma carlemanMatrix_apply (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C : ℝ) (j k : ι) (x : E) :
    carlemanMatrix e a X C j k x =
      4 * (∑ i, a i j x * SmoothScalar.directional (e i) (X k) x) -
        2 * (∑ l, X l x * SmoothScalar.directional (e l) (a k j) x) + 2*C*a k j x := by
  simp only [carlemanMatrix, Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]

lemma carlemanMatrix_convexify_at (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (H C : ℝ)
    (x : E) (hx : ψ x = 0) (j k : ι) :
    carlemanMatrix e a (coefficientGradient e a (convexifyPhase ψ H)) C j k x =
      carlemanMatrix e a (coefficientGradient e a ψ) C j k x +
        4*H*coefficientGradient e a ψ j x * coefficientGradient e a ψ k x := by
  simp only [carlemanMatrix_apply, phase_gradient_at e a ψ H x hx,
    phase_gradient_derivative_at e a ψ H x hx, mul_add, Finset.sum_add_distrib]
  have hs : (∑ i, a i j x * (H * SmoothScalar.directional (e i) ψ x *
        coefficientGradient e a ψ k x)) =
      H * coefficientGradient e a ψ j x * coefficientGradient e a ψ k x := by
    rw [coefficientGradient_apply e a ψ j x]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i j]
    ring
  rw [hs]
  ring

lemma carlemanMatrix_quadratic_convexify (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (H C : ℝ)
    (x : E) (hx : ψ x = 0) (v : ι → ℝ) :
    pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a (convexifyPhase ψ H)) C) x v =
      pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a ψ) C) x v +
        4*H*(∑ i, coefficientGradient e a ψ i x * v i)^2 := by
  simp only [pointwiseQuadratic, carlemanMatrix_convexify_at e a ha ψ H C x hx,
    add_mul, Finset.sum_add_distrib]
  congr 1
  rw [pow_two]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma carlemanMatrix_energy_shift (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (C : ℝ) (x : E) (v : ι → ℝ) :
    pointwiseQuadratic (carlemanMatrix e a X C) x v =
      pointwiseQuadratic (carlemanMatrix e a X 0) x v +
        2*C*realQuadratic (fun i j => a i j x) v := by
  have hh (i j : ι) : carlemanMatrix e a X C i j x =
      carlemanMatrix e a X 0 i j x + 2*C*a i j x := by
    simp only [carlemanMatrix_apply]
    rw [ha j i]
    ring
  simp only [pointwiseQuadratic, hh, add_mul, Finset.sum_add_distrib,
    realQuadratic, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma exists_carleman_energy_shift (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (x : E)
    (hx : ψ x = 0) (hpos : Matrix.PosDef (fun i j => a i j x)) :
    ∃ C > 0, ∀ H ≥ 0, ∀ v,
      2 * squareSum v ≤ pointwiseQuadratic
        (carlemanMatrix e a (coefficientGradient e a (convexifyPhase ψ H)) C) x v := by
  obtain ⟨κ, hκ, hκbound⟩ := matrix_positive_coercive (fun i j => a i j x) hpos
  let B := ∑ i, ∑ j, |carlemanMatrix e a (coefficientGradient e a ψ) 0 i j x|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  let C := (B+2)/(2*κ)
  have hC : 0 < C := div_pos (by linarith) (by positivity)
  have hCeq : 2*C*κ = B+2 := by dsimp [C]; field_simp
  refine ⟨C, hC, fun H hH v => ?_⟩
  rw [carlemanMatrix_quadratic_convexify e a ha ψ H C x hx,
    carlemanMatrix_energy_shift e a ha]
  have hbase := realQuadratic_abs_bound
    (fun i j => carlemanMatrix e a (coefficientGradient e a ψ) 0 i j x) v
  change |pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a ψ) 0) x v| ≤
    B * squareSum v at hbase
  have hl := (neg_le_abs (pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a ψ) 0) x v)).trans hbase
  have hp := mul_le_mul_of_nonneg_left (hκbound v) (by positivity : 0 ≤ 2*C)
  have hnormal : 0 ≤ 4*H*(∑ i, coefficientGradient e a ψ i x * v i)^2 := by positivity
  have heq : 2*C*(κ*squareSum v) = (B+2)*squareSum v := by rw [← mul_assoc, hCeq]
  rw [heq] at hp
  nlinarith only [hl, hp, hnormal]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_TestPairSubSquareBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology

lemma carleman_large_parameter (C M : ℝ) : ∃ T > 0, ∀ τ ≥ T,
    0 ≤ τ ∧ τ*M + C^2*τ^2 ≤ (1/2:ℝ)*τ^3 := by
  refine ⟨4*(|M|+C^2+1), by positivity, fun τ hτ => ?_⟩
  have hM := abs_nonneg M
  have hCs := sq_nonneg C
  have ht : 1 ≤ τ := by linarith
  have ht0 : 0 ≤ τ := by linarith
  refine ⟨ht0, ?_⟩
  have hm : M ≤ τ/4 := by linarith [le_abs_self M]
  have hc : C^2 ≤ τ/4 := by linarith
  have hh1 := mul_le_mul_of_nonneg_right hm ht0
  have hh2 := mul_le_mul_of_nonneg_right hc (sq_nonneg τ)
  have hh3 := mul_le_mul_of_nonneg_right ht (sq_nonneg τ)
  nlinarith only [hh1, hh2, hh3]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

theorem exists_local_carleman (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (x₀ : E)
    (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
    (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0) :
    ∃ H > 0, ∃ U ∈ 𝓝 x₀, ∃ T > 0, ∀ (K : Compacts E), (↑K : Set E) ⊆ U →
      ∀ τ ≥ T, ∀ f : EllipticTest K,
        τ * testGradientSquare K e f + (1/2:ℝ)*τ^3*testPair K f f ≤
          testPair K
            (carlemanSymmetric K e a (coefficientNorm e a (convexifyPhase ψ H)) τ f +
              carlemanSkew K e (coefficientGradient e a (convexifyPhase ψ H)) τ f)
            (carlemanSymmetric K e a (coefficientNorm e a (convexifyPhase ψ H)) τ f +
              carlemanSkew K e (coefficientGradient e a (convexifyPhase ψ H)) τ f) := by
  obtain ⟨C, hC, henergy⟩ := exists_carleman_energy_shift e a ha ψ x₀ hψ hpos
  let p₀ := coefficientNorm e a ψ x₀
  let R₀ := coefficientTransport e (coefficientGradient e a ψ) (coefficientNorm e a ψ) x₀
  have hp : 0 < p₀ := coefficientNorm_pos e a ψ x₀ hpos hgrad
  let H := (|2*C*p₀ - 2*R₀| + 2)/(4*p₀^2)
  have hH : 0 < H := div_pos (by positivity) (by positivity)
  have hHeq : 4*H*p₀^2 = |2*C*p₀-2*R₀|+2 := by
    dsimp [H]
    field_simp
  let φ := convexifyPhase ψ H
  let X := coefficientGradient e a φ
  let p := coefficientNorm e a φ
  have hmass : 2 ≤ 2*coefficientTransport e X p x₀ - 2*C*p x₀ := by
    dsimp only [X, p, φ]
    rw [phase_transport_norm_at e a ψ H x₀ hψ, phase_norm_at e a ψ H x₀ hψ]
    change 2 ≤ 2*(R₀+2*H*p₀^2)-2*C*p₀
    linarith [le_abs_self (2*C*p₀-2*R₀)]
  have he : ∀ᶠ x in 𝓝 x₀, ∀ v, squareSum v ≤
      pointwiseQuadratic (carlemanMatrix e a X C) x v :=
    continuous_matrix_lower_near (fun x i j => carlemanMatrix e a X C i j x)
      (fun i j => (SmoothScalar.contDiff _).continuous) x₀ (henergy H hH.le)
  have hmc : Continuous (fun x => 2*coefficientTransport e X p x - 2*C*p x) :=
    (continuous_const.mul (SmoothScalar.contDiff _).continuous).sub
      (continuous_const.mul (SmoothScalar.contDiff _).continuous)
  have hem : ∀ᶠ x in 𝓝 x₀, 1 ≤ 2*coefficientTransport e X p x - 2*C*p x :=
    ((hmc.tendsto x₀).eventually_const_lt (by linarith : (1:ℝ) <
      2*coefficientTransport e X p x₀ - 2*C*p x₀)).mono fun _ h => h.le
  let q := coefficientElliptic e a (coefficientDivergence e X)
  let M := |q x₀|+1
  have heq : ∀ᶠ x in 𝓝 x₀, q x ≤ M :=
    (((SmoothScalar.contDiff q).continuous.tendsto x₀).eventually_lt_const
      (by dsimp [M]; linarith [le_abs_self (q x₀)])).mono fun _ h => h.le
  let U := {x | (∀ v, squareSum v ≤ pointwiseQuadratic (carlemanMatrix e a X C) x v) ∧
    1 ≤ 2*coefficientTransport e X p x - 2*C*p x ∧ q x ≤ M}
  have hU : U ∈ 𝓝 x₀ := he.and (hem.and heq)
  obtain ⟨T, hT, hlarge⟩ := carleman_large_parameter C M
  refine ⟨H, hH, U, hU, T, hT, fun K hKU τ hτ f => ?_⟩
  obtain ⟨ht0, htn⟩ := hlarge τ hτ
  have hgb : (1:ℝ) * testGradientSquare K e f ≤
      carlemanGradient K e a X f + 2*C*testEnergy K e a f f :=
    carleman_gradient_bound K e a X C 1
      (fun x hx v => by simpa only [one_mul, squareSum] using (hKU hx).1 v) f
  have hh := carleman_coercive_of_bounds K e a ha X p τ C 1 M ht0 f hgb
    (fun x hx => (hKU hx).2.1) (fun x hx => (hKU hx).2.2) htn
  simpa only [mul_one] using hh


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma testPair_sub_square_bound (f g : EllipticTest K) :
    testPair K (f-g) (f-g) ≤ 2*testPair K f f + 2*testPair K g g := by
  have h := testPair_nonneg K (f+g)
  simp only [testPair_add_left, testPair_add_right, testPair_comm K g f] at h
  simp only [testPair_sub_left, testPair_sub_right, testPair_comm K g f]
  linarith

lemma testMultiply_square_bound (V : SmoothScalar E) (B : ℝ)
    (hV : ∀ x ∈ K, (V x)^2 ≤ B) (f : EllipticTest K) :
    testPair K (testMultiply K V f) (testMultiply K V f) ≤ B * testPair K f f := by
  rw [← testMultiply_symmetric, ← testMultiply_mul]
  exact weightedPair_le_of_bound K (V*V) B (fun x hx => by
    simpa only [Subalgebra.coe_mul, Pi.mul_apply, pow_two] using hV x hx) f

theorem exists_local_weighted_carleman_oai (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V ψ : SmoothScalar E) (x₀ : E)
    (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
    (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0) :
    ∃ H > 0, ∃ U ∈ 𝓝 x₀, ∃ T > 0, ∀ (K : Compacts E), (↑K : Set E) ⊆ U →
      ∀ τ ≥ T, ∀ u : EllipticTest K,
        testPair K (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u)
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u) ≤
        8 * testPair K
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u))
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u)) := by
  obtain ⟨H,hH,U,hU,T,hT,hest⟩ := exists_local_carleman e a ha ψ x₀ hψ hpos hgrad
  let B := (V x₀)^2+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbnd : ∀ᶠ x in 𝓝 x₀, (V x)^2 ≤ B :=
    ((((SmoothScalar.contDiff V).continuous.pow 2).tendsto x₀).eventually_lt_const
      (by dsimp [B]; linarith)).mono fun _ h => h.le
  refine ⟨H,hH,U ∩ {x | (V x)^2 ≤ B},inter_mem hU hbnd,max T (8*B+1),
    lt_of_lt_of_le hT (le_max_left ..),fun K hK τ hτ u => ?_⟩
  have ht : T ≤ τ := (le_max_left ..).trans hτ
  have htB : 8*B+1 ≤ τ := (le_max_right ..).trans hτ
  have ht1 : 1 ≤ τ := by linarith
  have ht0 : 0 ≤ τ := by linarith
  let φ := convexifyPhase ψ H
  let f := testMultiply K (exponentialWeight φ τ) u
  let r := testMultiply K (exponentialWeight φ τ) (testSchrodinger K e a V u)
  have hcar := hest K (fun x hx => (hK hx).1) τ ht f
  rw [carleman_conjugation] at hcar
  · have hid : testMultiply K (exponentialWeight φ τ) (testElliptic K e a u) =
        r - testMultiply K V f := by
      dsimp only [r, f, testSchrodinger]
      simp only [LinearMap.add_apply, map_add, ← testMultiply_mul]
      rw [mul_comm V (exponentialWeight φ τ)]
      abel
    change τ*testGradientSquare K e f + (1/2:ℝ)*τ^3*testPair K f f ≤
      testPair K (testMultiply K (exponentialWeight φ τ) (testElliptic K e a u))
        (testMultiply K (exponentialWeight φ τ) (testElliptic K e a u)) at hcar
    rw [hid] at hcar
    have hs := testPair_sub_square_bound K r (testMultiply K V f)
    have hv := testMultiply_square_bound K V B (fun x hx => (hK hx).2) f
    have hg : 0 ≤ τ*testGradientSquare K e f := mul_nonneg ht0
      (Finset.sum_nonneg fun _ _ => testPair_nonneg K _)
    have hτcube : 8*B+1 ≤ τ^3 := htB.trans (by
      have h1 := mul_le_mul_of_nonneg_left ht1 ht0
      have h2 := mul_le_mul_of_nonneg_left ht1 (sq_nonneg τ)
      nlinarith)
    have hf0 := testPair_nonneg K f
    have hh := mul_le_mul_of_nonneg_right hτcube hf0
    change testPair K f f ≤ 8*testPair K r r
    have hbf := mul_nonneg hB.le hf0
    have hr0 := testPair_nonneg K r
    nlinarith only [hcar,hs,hv,hg,hh,hf0,hbf,hr0]
  · exact ha



end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.exists_local_weighted_carleman_oai.{u_1, u_2} := @OAI.YauCounterexamples.exists_local_weighted_carleman_oai.{u_1, u_2}
