-- Prove2me | solution 1 for RH.Transport.PhysicalAnalytic.Contours.source_ordered_at_height
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T20:27:06.795309+00:00
-- url     : https://prove2.me/submissions/b6e542ba-d062-48d8-925c-d44f9815bf68

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B008
import Definitions.Def_OAIHecke78B016
import Definitions.Def_OAIHecke78B019
import Definitions.Def_OAIHecke78B021
import Definitions.Def_OAIHecke78B022
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B027
import Definitions.Def_OAIHecke78B028
import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_fixed_principal_z_box_growth
import Theorems.Thm_OAI_SevenEighths_HeckeReciprocalGrowth_reciprocal_subpower
import Theorems.Thm_OAI_SevenEighths_PrincipalMellinGrowth_fixed_principal_w_growth
set_option autoImplicit false

section
-- module Solutions.OAIHecke.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open Polynomial

/-- Backport (Mathlib d13f23b), with Mathlib's own proof. -/
theorem integral_id_div_sq_add_sq {a b c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, x / (c ^ 2 + x ^ 2) =
      (Real.log (c ^ 2 + b ^ 2) - Real.log (c ^ 2 + a ^ 2)) / 2 := by
  rw [sub_div]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => Real.log (c ^ 2 + x ^ 2) / 2)
  · intro x _
    have h := (((hasDerivAt_pow 2 x).const_add (c ^ 2)).log
      (by dsimp; positivity)).div_const 2
    convert! h using 1
    ring
  · exact (continuous_id.div (by fun_prop) fun x => by positivity).intervalIntegrable _ _

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ContinuationPolynomialContour
namespace OAI

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex

open scoped Topology

namespace SevenEighths.Continuation

theorem polynomialGaussian_integrable (n : ℕ) : Integrable (polynomialGaussian n) := by
  have hp := (integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ)<1) (show (-1 : ℝ)<(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  have hg := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have he : (fun y : ℝ => ‖y^(n : ℝ)*Real.exp (-1*y^2)‖) =
      fun y : ℝ => |y|^n*Real.exp (-(y^2)) := by
    funext y
    simp [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [he] at hp
  convert (preTransparency := .instances) hg.add hp using 1
  funext y
  simp [polynomialGaussian, add_mul]

end SevenEighths.Continuation

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section

open MeasureTheory

open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory

open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    rw [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
namespace OAI

noncomputable section

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

end FiniteGaussPhase

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
namespace OAI

noncomputable section

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory Set

open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical

open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap

open scoped Classical FourierTransform SchwartzMap ContDiff

open MeasureTheory

namespace CubicReflectionKernel

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

end CubicReflectionKernel

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
namespace OAI

noncomputable section

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory Set

open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical

open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology

open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology

open MeasureTheory Filter

namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology

open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

end CubicReflectionKernel

open scoped BigOperators Classical

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
namespace OAI

noncomputable section

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory Set

open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical

open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

open scoped Classical FourierTransform SchwartzMap ContDiff Topology

open MeasureTheory Filter

namespace CubicReflectionKernel

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology

open MeasureTheory Filter Set

namespace CubicReflectionKernel

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤
        C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤
      B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology

open MeasureTheory Filter Set

namespace CubicReflectionKernel

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

end CubicReflectionKernel

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section

open Filter Asymptotics Set MeasureTheory

open scoped Topology BigOperators

namespace SevenEighths.HeckeTheta

open EisensteinTheta

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

end SevenEighths.HeckeTheta

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta (continued)
namespace OAI

noncomputable section

open Filter Asymptotics Set MeasureTheory

open scoped Topology BigOperators

namespace SevenEighths.HeckeTheta

open EisensteinTheta

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

end SevenEighths.HeckeTheta

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Family
namespace OAI

noncomputable section

open scoped BigOperators

namespace SevenEighths.HeckeFamily

theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
namespace OAI

noncomputable section

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory Set

open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical

open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical

open Filter MeasureTheory

open scoped Classical BigOperators Topology

namespace CompletedGauss

section

open ActualEisensteinCubic ConcreteTraceCRT

local notation "O" => ActualEisensteinCubic.O

lemma angularFactor_norm_le_one (a : ActualEisensteinCubic.O) : ‖FiniteGaussPhase.angularFactor a‖≤1 := by
  by_cases ha : a=0
  · subst a; simp [FiniteGaussPhase.angularFactor]
  · exact (FiniteGaussPhase.norm_angularFactor a ha).le

end

open Filter MeasureTheory

open scoped Classical BigOperators Topology ContDiff

open ActualEisensteinCubic

local notation "O" => ActualEisensteinCubic.O

end CompletedGauss

open scoped BigOperators Classical

open Finset AddChar MulChar EisensteinEmbedding

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RadialMellin
namespace OAI

noncomputable section

open MeasureTheory Set Filter Asymptotics

open scoped FourierTransform RealInnerProductSpace Topology

namespace SevenEighths.ProbeRadialMellin

lemma mellinConvergent_real (f : ℝ → ℂ) (s : ℝ) :
    MellinConvergent f (s : ℂ) ↔
      IntegrableOn (fun r : ℝ => (r^(s-1) : ℝ) • f r) (Ioi 0) := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma gamma_scaled_integrable {s r : ℝ} (hs : 0<s) (hr : 0< r) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  have hg : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s : ℂ) := by
    rw [mellinConvergent_real]
    simpa only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, mul_comm] using!
      (Real.GammaIntegral_convergent hs).ofReal (𝕜 := ℂ)
  have hh := (MellinConvergent.comp_mul_left (f := fun t : ℝ => (Real.exp (-t) : ℂ))
    (s := (s : ℂ)) hr).mpr hg
  rw [mellinConvergent_real] at hh
  simpa only [RCLike.smul_re, RCLike.ofReal_re] using! hh.re

lemma gamma_scaled_integral {s r : ℝ} (hs : 0<s) (hr : 0< r) :
    (∫ t : ℝ in Ioi 0, t^(s-1)*Real.exp (-(r*t))) =
      r^(-s)*Real.Gamma s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_neg hr.le]

lemma laplace_mellin_integrable (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    Integrable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    exact hf.comp_fst.mul (by fun_prop)
  have hn (r t : ℝ) (ht : 0<t) :
      ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖ =
        ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t))) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_exp]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re]
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply ((gamma_scaled_integrable hs hr).const_mul ‖f r‖).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hn r t ht).le
  · have hw : IntegrableOn (fun r : ℝ => r^(-s.re)*‖f r‖) (Ioi 0) := by
      apply hconv.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.sub_re, Complex.one_re]
      congr 2
      ring
    apply (hw.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hi : (fun t : ℝ => ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hn r t ht
    rw [integral_congr_ae hi]
    rw [integral_const_mul, gamma_scaled_integral hs hr]
    ring

lemma mellin_laplace (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    mellin (laplace f) s = Complex.Gamma s * mellin f (1-s) := by
  have hi := laplace_mellin_integrable f s hs hf hconv
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ r : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) := by
      unfold mellin laplace
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [mul_comm r t]
      ring
    _ = ∫ r : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) :=
      integral_integral_swap hi.swap
    _ = ∫ r : ℝ in Ioi 0, f r*((r:ℂ)^(-s)*Complex.Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [integral_const_mul]
      have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
      simp only [Complex.ofReal_mul] at *
      rw [hh, one_div, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
    _ = _ := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [show 1-s-1 = -s by ring, smul_eq_mul]
      ring

open EisensteinSchwartzPoisson

lemma paperConstant_pos : 0<paperConstant := by
  unfold paperConstant
  positivity

lemma paperConstant_sq : paperConstant^2 = 4*Real.pi^2/3 := by
  unfold paperConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma paperE_norm (z : ℂ) : ‖paperE z‖=1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp

lemma paper_fourier_pairing (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ u : ℂ, paperFourier f u * g u) = ∫ z : ℂ, f z * paperFourier g z := by
  have hi : Integrable (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))*f p.2*g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))) := by
        simp_rw [paperE_eq_exp]
        fun_prop
      exact (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
        hg.aestronglyMeasurable.comp_fst
    · exact Eventually.of_forall fun p => by
        simp only [norm_mul, paperE_norm, one_mul]
        exact le_of_eq (mul_comm _ _)
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (hi.const_mul ((2/Real.sqrt 3:ℝ):ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [mul_comm z u]; ring

lemma paper_gaussian_fourier (t : ℝ) (ht : 0<t) (u : ℂ) :
    paperFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) u =
      (paperConstant/t:ℝ)*Complex.exp (-(paperConstant^2*‖u‖^2/t:ℝ)) := by
  rw [paperFourier_eq_standard,
    fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2:ℂ)≠0), Complex.cpow_one]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, paperFrequency_norm_sq, paperConstant_sq]
  push_cast
  have he : -(Real.pi:ℂ)^2*((4/3:ℝ)*‖u‖^2:ℝ)/(t:ℂ) =
      -((4*Real.pi^2/3*‖u‖^2/t:ℝ):ℂ) := by push_cast; ring
  push_cast at he
  rw [he]
  unfold paperConstant
  push_cast
  ring

lemma radial_continuous (W : SchwartzMap ℝ ℂ) : Continuous (paperRadialFourier W) := by
  rw [paperRadialFourier_eq_ray]
  exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt

lemma radial_isBigO_top (W : SchwartzMap ℝ ℂ) (A : ℕ) :
    paperRadialFourier W =O[atTop] (fun r : ℝ => r^(-(A:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W A 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hh := hb 0 (by omega) r hr
  simp only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hh
  have hp : r^A * ‖paperRadialFourier W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le (by linarith : r≤1+r) A)
      (norm_nonneg _)).trans hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa [mul_comm] using hp)

lemma radial_isBigO_zero (W : SchwartzMap ℝ ℂ) :
    paperRadialFourier W =O[𝓝[>] 0] (fun r : ℝ => r^(-(0:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W 0 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa [LocalLogFourier.eulerDeriv] using hb 0 (by omega) r hr

theorem radial_mellin_convergent (W : SchwartzMap ℝ ℂ) (z : ℂ) (hz : 0<z.re) :
    MellinConvergent (paperRadialFourier W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz

theorem radial_mellin_differentiable (W : SchwartzMap ℝ ℂ) :
    DifferentiableOn ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} := by
  intro z hz
  obtain ⟨A,hA⟩ := exists_nat_gt z.re
  exact (mellin_differentiableAt_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz).differentiableWithinAt

lemma radial_laplace_duality (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0<t) :
    laplace (paperRadialFourier W) t =
      (paperConstant/t:ℝ)*laplace W (paperConstant^2/t) := by
  have hf : Integrable (fun z : ℂ => W (‖z‖^2)) := (radialTestCLM W).integrable
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) 0 (0:ℂ)
  have h := paper_fourier_pairing _ _ hf hg
  have hleft : (∫ u : ℂ, paperFourier (fun z : ℂ => W (‖z‖^2)) u *
      Complex.exp (-(t:ℂ)*‖u‖^2)) = (Real.pi:ℂ)*laplace (paperRadialFourier W) t := by
    simp_rw [paperFourier_radial]
    rw [laplace, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [Complex.ofReal_mul]
  have hright : (∫ z : ℂ, W (‖z‖^2)*paperFourier
      (fun u : ℂ => Complex.exp (-(t:ℂ)*‖u‖^2)) z) =
      (Real.pi:ℂ)*((paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) := by
    simp_rw [paper_gaussian_fourier t ht]
    rw [laplace, ← integral_const_mul, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      have he : paperConstant^2*‖u‖^2/t = paperConstant^2/t*‖u‖^2 := by ring
      rw [he]
      ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

lemma mellin_reciprocal_laplace (W : ℝ → ℂ) (z : ℂ) :
    mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) =
      (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*mellin (laplace W) z := by
  have hfun : (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) =
      (fun t : ℝ => (paperConstant:ℂ) • ((t:ℂ)^(-1:ℂ) •
        laplace W (paperConstant^2*t⁻¹))) := by
    funext t
    simp [Complex.cpow_neg_one, div_eq_mul_inv, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_const_smul, mellin_cpow_smul]
  rw [show 1-z+(-1) = -z by ring]
  have hh := mellin_comp_inv (fun t : ℝ => laplace W (paperConstant^2*t)) (-z)
  rw [neg_neg] at hh
  rw [hh, mellin_comp_mul_left _ _ (sq_pos_of_pos paperConstant_pos)]
  simp only [smul_eq_mul]
  ring

theorem radial_mellin_gamma (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*Complex.Gamma z /
        Complex.Gamma (1-z))*mellin W (1-z) := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (1-z)
  have hL := mellin_laplace (paperRadialFourier W) (1-z)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    ((radial_continuous W).aestronglyMeasurable)
    (by simpa only [sub_sub_cancel] using radial_mellin_convergent W z hz)
  have hR := mellin_laplace W z hz W.continuous.aestronglyMeasurable hc
  have he : mellin (laplace (paperRadialFourier W)) (1-z) =
      mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [radial_laplace_duality W t ht]
  rw [hL, sub_sub_cancel, mellin_reciprocal_laplace, hR] at he
  have hg : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)
  apply (mul_left_cancel₀ hg)
  rw [he]
  field_simp

lemma paper_prefactor (z : ℂ) :
    (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z) =
      (paperConstant:ℂ)^(1-2*z) := by
  have hn : (paperConstant:ℂ)≠0 := Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'
  have hh := Complex.cpow_nat_mul' (x := (paperConstant:ℂ)) (n := 2)
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_pos])
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_nonneg]) (-z)
  push_cast
  rw [← hh, show 1-2*z = 1+2*(-z) by ring, Complex.cpow_add _ _ hn,
    Complex.cpow_one]
  norm_num

theorem radial_mellin_identity (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  rw [radial_mellin_gamma W a b ha hW z hz hz1, paper_prefactor]

theorem radial_mellin_identity_right (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  let D : Set ℂ := {z | 0<z.re}
  let G : ℂ → ℂ := fun z =>
    ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
      mellin W (1-z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) D :=
    (radial_mellin_differentiable W).analyticOnNhd hop
  have hG : DifferentiableOn ℂ G D := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (paperConstant:ℂ)^(1-2*z)) w :=
      (differentiableAt_const _ |>.sub (differentiableAt_id.const_mul 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'))
    have h2 := CubicReflectionKernel.Gamma_differentiableAt_of_re_pos w hw
    have h3 := (Complex.differentiable_one_div_Gamma (1-w)).comp w
      (differentiableAt_const _ |>.sub differentiableAt_id)
    have h4 := (CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hW
      (W.smooth ⊤) (1-w)).comp w (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! (((h1.mul h2).mul h3).mul h4).differentiableWithinAt
  have hev : mellin (paperRadialFourier W) =ᶠ[𝓝 (1/2:ℂ)] G := by
    have hstrip : IsOpen {w:ℂ | 0<w.re ∧ w.re<1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with w hw
    exact radial_mellin_identity W a b ha hW w hw.1 hw.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hz

lemma gamma_quotient_strip (lo hi : ℝ) (hlo : 0<lo) :
    ∃ (n : ℕ) (C : ℝ), 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖Complex.Gamma ((σ:ℂ)+t*Complex.I) / Complex.Gamma (1-((σ:ℂ)+t*Complex.I))‖ ≤
        C*(1+|t|)^n := by
  obtain ⟨A,hA⟩ := exists_nat_gt hi
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.Gamma_pair_strip_bound 1 (by norm_num) A
  refine ⟨2*A+2,C/lo,div_pos hC hlo,?_⟩
  intro σ hσ t
  have hσ0 : 0<σ := hlo.trans_le hσ.1
  have hz : (σ:ℂ)+t*Complex.I≠0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
    linarith
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  norm_num only [Complex.ofReal_one] at hh
  rw [add_comm (1:ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : lo≤‖(σ:ℂ)+t*Complex.I‖ := by
    apply hσ.1.trans
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ:ℂ)+t*Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

theorem radial_mellin_strip_decay (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      (1+|t|)^N * ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C := by
  obtain ⟨n,Cg,hCg,hg⟩ := gamma_quotient_strip lo hi hlo
  obtain ⟨Cw,hCw,hw⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1-hi) (1-lo) (n+N)
  have hc : Continuous (fun σ : ℝ => paperConstant^(1-2*σ)) :=
    (Real.continuous_const_rpow paperConstant_pos.ne').comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc lo hi))
  let Cp := |B|+1
  have hCp : 0<Cp := by dsimp [Cp]; positivity
  refine ⟨Cp*Cg*Cw,by positivity,?_⟩
  intro σ hσ t
  have hp : ‖(paperConstant:ℂ)^(1-2*((σ:ℂ)+t*Complex.I))‖≤Cp := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos paperConstant_pos]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      show (2:ℂ).re=2 by rfl, show (2:ℂ).im=0 by rfl, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact (hB (mem_image_of_mem _ hσ)).trans (by change B≤|B|+1; linarith [le_abs_self B])
  have hwb := hw (1-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1-σ:ℝ):ℂ)+(-t:ℝ)*Complex.I = 1-((σ:ℂ)+t*Complex.I) by
    push_cast; ring] at hwb
  rw [radial_mellin_identity_right W a b ha hW _ (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact hlo.trans_le hσ.1), mul_div_assoc, norm_mul, norm_mul]
  calc
    _ ≤ (1+|t|)^N*(Cp*(Cg*(1+|t|)^n)*
        ‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = (Cp*Cg)*((1+|t|)^(n+N)*‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwb (by positivity)

end SevenEighths.ProbeRadialMellin

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
namespace OAI

noncomputable section

open scoped BigOperators

namespace SevenEighths.HeckeCharacterAnalytic

theorem continuedLattice_differentiableAt_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))

end SevenEighths.HeckeCharacterAnalytic

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealBridge
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace SevenEighths.HeckeFamily

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

end SevenEighths.HeckeFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
namespace OAI

noncomputable section

namespace SevenEighths.HeckeZeroSupremum

open HeckeFamily

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

end SevenEighths.HeckeZeroSupremum

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum (continued)
namespace OAI

noncomputable section

namespace SevenEighths.HeckeZeroSupremum

open HeckeFamily

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

end SevenEighths.HeckeZeroSupremum

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal
namespace OAI

noncomputable section

open scoped Classical BigOperators

namespace SevenEighths.HeckeReciprocal

open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

end SevenEighths.HeckeReciprocal

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal (continued)
namespace OAI

noncomputable section

open scoped Classical BigOperators

namespace SevenEighths.HeckeReciprocal

open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem reciprocal_eq_inv (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    reciprocal χ s = (LFunction χ s)⁻¹ := by
  unfold reciprocal
  split_ifs
  · rw [regularizedL_eq χ h0 h1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr h1), one_div]
  · rfl

end SevenEighths.HeckeReciprocal

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal (continued)
namespace OAI

noncomputable section

open scoped Classical BigOperators

namespace SevenEighths.HeckeReciprocal

open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_ne_zero (χ : Character) (hχ : χ.residue = 1) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regularizedL χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact regularizedL_ne_zero_at_one χ hχ
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  rw [regularizedL_eq χ h0 h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1)
    (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inl h1))

theorem reciprocal_differentiableAt (χ : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  by_cases hχ : χ.residue = 1
  · have heq : reciprocal χ = fun z => (z - 1) / regularizedL χ z := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (regularizedL_differentiableAt χ h0) (regularizedL_ne_zero χ hχ hs)
  · have heq : reciprocal χ = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv
      (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inr hχ))

end SevenEighths.HeckeReciprocal

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Row
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace SevenEighths.ProbeRow

open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion

open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

end SevenEighths.ProbeRow

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalMellinResidues (continued)
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology

namespace SevenEighths.PrincipalMellinResidues

open ProbePhysical

lemma inverse_vertical_continuous (c : ℝ) (hc : c≠0) :
    Continuous (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t h
  have he := congrArg Complex.re h
  simp at he
  exact hc he

lemma inverse_vertical_truncated (c T : ℝ) (hc : c≠0) :
    (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) = (2*Real.arctan (T/c):ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) volume (-T) T :=
    (inverse_vertical_continuous c hc).intervalIntegrable (-T) T
  apply Complex.ext
  · have hh := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).re at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).re) =
        (fun t : ℝ => c/(c^2+t^2)) := by
      funext t
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [he, integral_div_sq_add_sq]
    simp [neg_div, Real.arctan_neg, -Complex.ofReal_arctan]
    ring
  · have hh := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).im at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).im) =
        (fun t : ℝ => -(t/(c^2+t^2))) := by
      funext t
      simp [Complex.inv_im, Complex.normSq_apply, pow_two, neg_div]
    rw [he, intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc]
    simp [-Complex.ofReal_arctan]

lemma inverse_vertical_limit_pos (c : ℝ) (hc : 0<c) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (Real.pi:ℂ)) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne']
  have ht := Real.tendsto_arctan_atTop.comp (Filter.tendsto_id.atTop_div_const hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert (preTransparency := .instances) hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_vertical_limit_neg (c : ℝ) (hc : c<0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (-(Real.pi:ℂ))) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne]
  have ht := Real.tendsto_arctan_atBot.comp (Filter.tendsto_id.atTop_div_const_of_neg hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert (preTransparency := .instances) hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_horizontal_limit (a b p : ℝ) (ε : ℝ) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ T : ℝ in atTop, ‖∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹‖ ≤ T⁻¹ * |b-a| from ?_) ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_inv]
    apply inv_anti₀ hT
    have h := Complex.abs_im_le_norm ((x:ℂ)+(ε*T)*I-p)
    simpa [abs_mul, hε, abs_of_pos hT] using h
  · simpa using (tendsto_inv_atTop_zero.mul_const |b-a|)

lemma dslope_eq_sub_pole {A F : ℂ → ℂ} {p z : ℂ} (hz : z≠p)
    (hF : F z = A z / (z-p)) :
    dslope A p z = F z - A p * (z-p)⁻¹ := by
  rw [dslope_of_ne A hz, slope, hF]
  simp only [smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

lemma dslope_vertical_truncated (A F : ℂ → ℂ) (p x T : ℝ) (hx : x≠p)
    (hF : ∀ z : ℂ, z.re = x → F z = A z / (z-p))
    (hi : Integrable (fun t : ℝ => F ((x:ℂ)+t*I))) :
    (∫ t : ℝ in -T..T, dslope A (p:ℂ) ((x:ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((x:ℂ)+t*I)) -
        A p * (∫ t : ℝ in -T..T, (((x-p:ℝ):ℂ)+t*I)⁻¹) := by
  have he (t : ℝ) : dslope A (p:ℂ) ((x:ℂ)+t*I) =
      F ((x:ℂ)+t*I) - A p * ((((x-p:ℝ):ℂ)+t*I)⁻¹) := by
    have hn : (x:ℂ)+t*I ≠ p := by
      intro h
      exact hx (by simpa using congrArg Complex.re h)
    have h := dslope_eq_sub_pole hn (hF _ (by simp))
    convert (preTransparency := .instances) h using 1; push_cast; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi.intervalIntegrable
    (((inverse_vertical_continuous (x-p) (sub_ne_zero.mpr hx)).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

lemma rectangle_limits (G : ℂ → ℂ) {a b : ℝ} (hab : a≤b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a≤z.re ∧ z.re≤b})
    {Va Vb : ℂ}
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) atTop (𝓝 Va))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) atTop (𝓝 Vb))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    Va = Vb := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) -
      (∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a:ℂ)+(-T)*I) ((b:ℂ)+T*I) (hG.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      simpa [uIcc_of_le hab] using hz.1
  have hlim := ((hbot.sub htop).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : (0:ℂ)-0+I*Vb-I*Va=0 := tendsto_nhds_unique hlim
    (by simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)))
  exact (mul_left_cancel₀ I_ne_zero (show I*Vb=I*Va by simpa using sub_eq_zero.mp hz)).symm

lemma horizontal_quotient_continuousOn (A : ℂ → ℂ) {a b p y : ℝ}
    (hab : a≤b) (hy : y≠0)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b}) :
    ContinuousOn (fun x : ℝ => A ((x:ℂ)+y*I) / ((x:ℂ)+y*I-p)) (uIcc a b) := by
  apply ContinuousOn.div
  · apply hA.continuousOn.comp (by fun_prop)
    intro x hx
    simpa [uIcc_of_le hab] using hx
  · fun_prop
  · intro x hx h
    have hh := congrArg Complex.im h
    exact hy (by simpa using hh)

lemma dslope_horizontal_limit (A F : ℂ → ℂ) {a b p : ℝ} (hab : a≤b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ε : ℝ) (hε : |ε|=1)
    (hlim : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, dslope A p ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
  have hl := hlim.sub ((inverse_horizontal_limit a b p ε hε).const_mul (A p))
  simp only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hy : ε*T≠0 := mul_ne_zero (by intro h; simp [h] at hε) hT.ne'
  have hn (x : ℝ) : (x:ℂ)+(ε*T)*I≠p := by
    intro h
    exact hy (by simpa using congrArg Complex.im h)
  have he (x : ℝ) (hx : x∈uIcc a b) := hF ((x:ℂ)+(ε*T)*I)
    (by have := (uIcc_of_le hab ▸ hx).1; simpa using this)
    (by have := (uIcc_of_le hab ▸ hx).2; simpa using this) (hn x)
  have hfi : IntervalIntegrable (fun x : ℝ => F ((x:ℂ)+(ε*T)*I)) volume a b := by
    apply ((horizontal_quotient_continuousOn A (p:=p) hab hy hA).congr ?_).intervalIntegrable
    intro x hx
    simpa using he x hx
  have hki : IntervalIntegrable (fun x : ℝ => ((x:ℂ)+(ε*T)*I-p)⁻¹) volume a b := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    exact hn x (sub_eq_zero.mp h)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hfi (hki.const_mul _)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (dslope_eq_sub_pole (hn x) (he x hx)).symm

theorem verticalIntegral_simple_pole (A F : ℂ → ℂ) {a b p : ℝ}
    (hap : a<p) (hpb : p<b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ha : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    verticalIntegral b F = verticalIntegral a F + A p := by
  have hab := hap.le.trans hpb.le
  have hnb : {z : ℂ | a≤z.re ∧ z.re≤b} ∈ 𝓝 (p:ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a<(p:ℂ).re ∧ (p:ℂ).re<b from ⟨hap,hpb⟩))
    intro z hz
    exact ⟨hz.1.le,hz.2.le⟩
  have hG := (Complex.differentiableOn_dslope hnb).mpr hA
  have haF := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbF := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have haG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((a:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((a:ℂ)+t*I)) - A p * (-(Real.pi:ℂ)))) := by
    simp_rw [dslope_vertical_truncated A F p a _ hap.ne
      (fun z hz => hF z (by simp [hz]) (by simpa [hz] using hab)
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hap.ne this)) ha]
    exact haF.sub ((inverse_vertical_limit_neg (a-p) (sub_neg.mpr hap)).const_mul (A p))
  have hbG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((b:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((b:ℂ)+t*I)) - A p * (Real.pi:ℂ))) := by
    simp_rw [dslope_vertical_truncated A F p b _ hpb.ne'
      (fun z hz => hF z (by simpa [hz] using hab) (by simp [hz])
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hpb.ne' this)) hb]
    exact hbF.sub ((inverse_vertical_limit_pos (b-p) (sub_pos.mpr hpb)).const_mul (A p))
  have hbotG := dslope_horizontal_limit A F hab hA hF (-1) (by norm_num)
    (by simpa using hbot)
  have htopG := dslope_horizontal_limit A F hab hA hF 1 (by norm_num)
    (by simpa using htop)
  have he := rectangle_limits (dslope A p) hab hG haG hbG
    (by simpa using hbotG) (by simpa using htopG)
  have he' : (∫ t : ℝ, F ((b:ℂ)+t*I)) =
      (∫ t : ℝ, F ((a:ℂ)+t*I)) + 2*(Real.pi:ℂ)*A p := by
    linear_combination -he
  unfold verticalIntegral
  rw [he']
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [mul_comm]

open HeckeFamily

theorem verticalIntegral_hecke (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0<a) (ha1 : a<1) (h1b : 1<b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤z.re ∧ z.re≤b})
    (hB : BoundaryControl (fun z => K z * LFunction χ z) a b) :
    verticalIntegral b (fun z => K z * LFunction χ z) =
      verticalIntegral a (fun z => K z * LFunction χ z) +
        K 1 * HeckeReciprocal.regularizedL χ 1 := by
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ z)
    (fun z => K z * LFunction χ z) ha1 h1b
    (hK.mul (HeckeOrigin.poleRemoved_entire χ).differentiableOn) ?_
    hB.left hB.right hB.lower hB.upper
  · simpa [HeckeOrigin.poleRemoved_one] using h
  · intro z hza hzb hzp
    have hz0 : z≠0 := by intro h; subst z; simp at hza; linarith
    have hz1 : z≠1 := by simpa using hzp
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    norm_num
    field_simp

theorem verticalIntegral_hecke_six (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0<a) (hap : a<1/6) (hpb : 1/6<b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤z.re ∧ z.re≤b})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) a b) :
    verticalIntegral b (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral a (fun z => K z * LFunction χ (6*z)) +
        K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 := by
  have hhol : Differentiable ℂ (fun z => HeckeOrigin.poleRemoved χ (6*z)) :=
    (HeckeOrigin.poleRemoved_entire χ).comp (differentiable_id.const_mul 6)
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ (6*z) / 6)
    (fun z => K z * LFunction χ (6*z)) hap hpb
    ((hK.mul hhol.differentiableOn).div_const 6) ?_
    hB.left hB.right hB.lower hB.upper
  · norm_num [HeckeOrigin.poleRemoved_one] at h ⊢
    exact h
  · intro z hza hzb hzp
    have hz0 : 6*z≠0 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      have : z.re=0 := by linarith
      linarith
    have hz1 : 6*z≠1 := by
      intro h
      apply hzp
      push_cast
      linear_combination h / 6
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    have hden : z-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hzp)
    push_cast
    field_simp

theorem source_residue_z_shift (χ : Character) (K : ℂ → ℂ) {e : ℝ} (he : 0<e)
    (hK : DifferentiableOn ℂ K {z : ℂ | 33/200≤z.re ∧ z.re≤1/6+e})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) (33/200) (1/6+e)) :
    verticalIntegral (1/6+e) (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral (33/200) (fun z => K z * LFunction χ (6*z)) +
      K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 :=
  verticalIntegral_hecke_six χ K (by norm_num) (by norm_num) (by linarith) hK hB

lemma verticalIntegral_add (a : ℝ) (F G : ℂ → ℂ)
    (hF : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hG : Integrable (fun t : ℝ => G ((a:ℂ)+t*I))) :
    verticalIntegral a (fun z => F z + G z) = verticalIntegral a F + verticalIntegral a G := by
  unfold verticalIntegral
  rw [integral_add hF hG, mul_add]

lemma verticalIntegral_mul_const (a : ℝ) (F : ℂ → ℂ) (c : ℂ) :
    verticalIntegral a (fun z => F z * c) = verticalIntegral a F * c := by
  unfold verticalIntegral
  rw [integral_mul_const]
  ring

theorem source_ordered_double_shift (χ : Character) (K : ℂ → ℂ → ℂ)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e)
    (hwK : ∀ z : ℂ, z.re=1/6+e → DifferentiableOn ℂ (fun w => K w z)
      {w : ℂ | 19/20≤w.re ∧ w.re≤ cw})
    (hwB : ∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w) (19/20) cw)
    (hzK : DifferentiableOn ℂ (fun z => K 1 z)
      {z : ℂ | 33/200≤z.re ∧ z.re≤1/6+e})
    (hzB : BoundaryControl (fun z => K 1 z * LFunction χ (6*z)) (33/200) (1/6+e))
    (houter : Integrable (fun t : ℝ => verticalIntegral (19/20)
      (fun w => K w ((1/6+e:ℝ)+t*I) *
        LFunction χ (6*((1/6+e:ℝ)+t*I)) * LFunction χ w))) :
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) +
    HeckeReciprocal.regularizedL χ 1 *
      verticalIntegral (33/200) (fun z => K 1 z * LFunction χ (6*z)) +
    (HeckeReciprocal.regularizedL χ 1)^2 / 6 * K 1 (1/6) := by
  have hw (z : ℂ) (hz : z.re=1/6+e) := verticalIntegral_hecke χ
    (fun w => K w z * LFunction χ (6*z)) (by norm_num : (0:ℝ)<19/20)
    (by norm_num : (19/20:ℝ)<1) hcw ((hwK z hz).mul_const _) (hwB z hz)
  have hpoint : verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z * LFunction χ (6*z) * LFunction χ w) +
        (K 1 z * LFunction χ (6*z)) * HeckeReciprocal.regularizedL χ 1) := by
    unfold verticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    exact hw _ (by simp)
  rw [hpoint, verticalIntegral_add _ _ _ houter (hzB.right.mul_const _),
    verticalIntegral_mul_const, source_residue_z_shift χ (fun z => K 1 z) he hzK hzB]
  ring

end SevenEighths.PrincipalMellinResidues

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MellinBoundary
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology

namespace SevenEighths.ProbeMellinBoundary

open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

lemma height_pos (t : ℝ) : 0<height t := by unfold height; positivity

lemma height_one_le (t : ℝ) : 1≤height t := by simp [height]

lemma cauchy_nonneg (t : ℝ) : 0≤ cauchy t := by unfold cauchy; positivity

lemma cauchy_integrable : Integrable cauchy := integrable_inv_one_add_sq

lemma jointHeight_pos (t v w : ℝ) : 0<jointHeight t v w := by unfold jointHeight; positivity

lemma gaussianMoment_nonneg (n : ℕ) (u : ℝ) : 0≤gaussianMoment n u := by
  unfold gaussianMoment height
  positivity

lemma gaussianMoment_integrable (n : ℕ) : Integrable (gaussianMoment n) := by
  apply ((Continuation.polynomialGaussian_integrable n).const_mul ((2:ℝ)^(n-1))).mono'
  · unfold gaussianMoment height
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianMoment_nonneg n u)]
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg u) n
    simpa [gaussianMoment,height,Continuation.polynomialGaussian,mul_assoc] using
      mul_le_mul_of_nonneg_right h (Real.exp_pos (-(u^2))).le

lemma jointHeight_le_shear (t v w : ℝ) :
    jointHeight t v w≤2*height (t+v)*height v*height w := by
  have ht : |t|≤|t+v|+|v| := by simpa using (abs_sub_le (t+v) 0 v)
  have huv : 1≤height (t+v)*height v := one_le_mul_of_one_le_of_one_le (height_one_le _) (height_one_le _)
  have h1 : 1+|t|+|v|≤2*height (t+v)*height v := by
    unfold height
    nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]
  unfold jointHeight
  change 1+|t|+|v|+|w|≤2*height (t+v)*height v*(1+|w|)
  calc
    _ ≤ 2*height (t+v)*height v+|w| := by linarith [h1]
    _ ≤ 2*height (t+v)*height v+(2*height (t+v)*height v)*|w| := by
      have hh : 1≤2*height (t+v)*height v := by nlinarith
      have hhh := mul_le_mul_of_nonneg_right hh (abs_nonneg w)
      linarith
    _ = _ := by ring

lemma weighted_to_cauchy {f C : ℝ} (J : ℕ) (t : ℝ) (hf : 0≤f)
    (h : height t^(J+2)*f≤C) : height t^J*f≤C*cauchy t := by
  have hh : (1+|t|)^2*(height t^J*f)≤C := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using h
  exact CubicReflectionKernel.weighted_two_to_cauchy
    (mul_nonneg (pow_nonneg (height_pos t).le _) hf) t hh

lemma weighted_coupled_cauchy (J : ℕ) (t v w A B C D : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (_hD : 0≤D)
    (ha : height v^(J+2)*A≤C) (hb : height w^(J+2)*B≤D) :
    jointHeight t v w^J * Real.exp (-((t+v)^2))*A*B ≤
      (2:ℝ)^J*C*D*(gaussianMoment J (t+v)*cauchy v*cauchy w) := by
  have hpow := pow_le_pow_left₀ (jointHeight_pos t v w).le (jointHeight_le_shear t v w) J
  have ha' := weighted_to_cauchy J v hA ha
  have hb' := weighted_to_cauchy J w hB hb
  calc
    _ ≤ (2*height (t+v)*height v*height w)^J * Real.exp (-((t+v)^2))*A*B := by gcongr
    _ = (2:ℝ)^J * gaussianMoment J (t+v) * (height v^J*A)*(height w^J*B) := by
      simp only [mul_pow,gaussianMoment]
      ring
    _ ≤ (2:ℝ)^J * gaussianMoment J (t+v) * (C*cauchy v)*(D*cauchy w) := by
      have hg := gaussianMoment_nonneg J (t+v)
      have hc := cauchy_nonneg v
      have hd := cauchy_nonneg w
      have hw := (height_pos w).le
      have hv := (height_pos v).le
      gcongr
    _ = _ := by ring

lemma onLines_norm (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) :
    ‖onLines W0 W1 σ ξ υ p‖ = Real.exp ((σ+ξ-1)^2)*Real.exp (-((p.1.1+p.1.2)^2))*
      ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ *
      ‖mellin W1 ((υ:ℂ)+p.2*I)‖ := by
  unfold onLines profile
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have hr : ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)^2).re =
      (σ+ξ-1)^2+(-((p.1.1+p.1.2)^2)) := by simp [pow_two]; ring
  rw [hr,Real.exp_add]

lemma onLines_continuous (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (σ ξ υ : ℝ) (hξ : 0<ξ) : Continuous (onLines W0 W1 σ ξ υ) := by
  have hR : Continuous (fun t : ℝ => mellin (paperRadialFourier W0) ((ξ:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t; simpa using hξ)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous
  unfold onLines profile
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · exact hR.comp (continuous_snd.comp continuous_fst)
  · exact hW.comp (by fun_prop)

lemma realGaussianBound_pos (slo shi zlo zhi : ℝ) : 0< realGaussianBound slo shi zlo zhi :=
  Real.exp_pos _

lemma realGaussian_le {slo shi zlo zhi σ ξ : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi) :
    Real.exp ((σ+ξ-1)^2)≤ realGaussianBound slo shi zlo zhi := by
  have hs : |σ|≤|slo|+|shi| := by
    rw [abs_le]
    constructor <;> linarith [hσ.1,hσ.2,neg_abs_le slo,le_abs_self shi,abs_nonneg slo,abs_nonneg shi]
  have hz : |ξ|≤|zlo|+|zhi| := by
    rw [abs_le]
    constructor <;> linarith [hξ.1,hξ.2,neg_abs_le zlo,le_abs_self zhi,abs_nonneg zlo,abs_nonneg zhi]
  have hh : |σ+ξ-1|≤|slo|+|shi|+|zlo|+|zhi|+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le σ,le_abs_self σ,neg_abs_le ξ,le_abs_self ξ]
  apply Real.exp_le_exp.mpr
  have hp := pow_le_pow_left₀ (abs_nonneg (σ+ξ-1)) hh 2
  simpa [sq_abs] using hp

lemma profile_moment_majorant (W0 W1 : SchwartzMap ℝ ℂ) (J : ℕ)
    {slo shi zlo zhi σ ξ υ C D : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi)
    (hC : 0≤C) (hD : 0≤D)
    (hR : ∀v : ℝ, height v^(J+2)*‖mellin (paperRadialFourier W0) ((ξ:ℂ)+v*I)‖≤C)
    (hW : ∀w : ℝ, height w^(J+2)*‖mellin W1 ((υ:ℂ)+w*I)‖≤D) (p : HeightSpace) :
    jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ≤
      (realGaussianBound slo shi zlo zhi*2^J*C*D)*jointEnvelope J p := by
  have hb := weighted_coupled_cauchy J p.1.1 p.1.2 p.2
    ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ ‖mellin W1 ((υ:ℂ)+p.2*I)‖ C D
    (norm_nonneg _) (norm_nonneg _) hC hD (hR _) (hW _)
  rw [onLines_norm]
  calc
    _ = Real.exp ((σ+ξ-1)^2) * (jointHeight p.1.1 p.1.2 p.2^J*
        Real.exp (-((p.1.1+p.1.2)^2))*
        ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖*‖mellin W1 ((υ:ℂ)+p.2*I)‖) := by ring
    _ ≤ realGaussianBound slo shi zlo zhi *
        ((2:ℝ)^J*C*D*(gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2)) :=
      mul_le_mul (realGaussian_le hσ hξ) hb
        (by have := (jointHeight_pos p.1.1 p.1.2 p.2).le; positivity)
        (realGaussianBound_pos _ _ _ _).le
    _ = _ := by unfold jointEnvelope; ring

end SevenEighths.ProbeMellinBoundary

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MellinBoundary (continued)
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology

namespace SevenEighths.ProbeMellinBoundary

open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

lemma cauchy_le_one (t : ℝ) : cauchy t≤1 := by
  simpa [cauchy] using inv_anti₀ (by norm_num : (0:ℝ)<1)
    (show 1≤1+t^2 by nlinarith [sq_nonneg t])

end SevenEighths.ProbeMellinBoundary

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MellinBoundary (continued)
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology

namespace SevenEighths.ProbeMellinBoundary

open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

lemma sliceMap_continuous (axis : SliceAxis) (T : ℝ) : Continuous (sliceMap axis T) := by
  cases axis <;> unfold sliceMap <;> fun_prop

lemma slice_height_le (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) :
    height T≤jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2 := by
  cases axis <;> unfold sliceMap height jointHeight <;>
    linarith [abs_nonneg q.1,abs_nonneg q.2]

lemma jointEnvelope_slice_le (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointEnvelope J (sliceMap axis T q)≤ sliceEnvelope axis J T q := by
  cases axis
  · change gaussianMoment J (T+q.1)*cauchy q.1*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one q.1) (gaussianMoment_nonneg J (T+q.1))) (cauchy_nonneg q.2)
    simpa using hh
  · change gaussianMoment J (q.1+T)*cauchy T*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one T) (gaussianMoment_nonneg J (q.1+T))) (cauchy_nonneg q.2)
    simpa [add_comm] using hh
  · change gaussianMoment J (q.1+q.2)*cauchy q.2*cauchy T ≤ gaussianMoment J (q.1+q.2)*cauchy q.2
    simpa using mul_le_mul_of_nonneg_left (cauchy_le_one T)
      (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _))

lemma pairEnvelope_integrable (J : ℕ) :
    Integrable (fun q : ℝ×ℝ => gaussianMoment J (q.1+q.2)*cauchy q.2) (volume.prod volume) := by
  have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
      (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
  have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
  have hi := hp1.integrable_comp_of_integrable ((gaussianMoment_integrable J).mul_prod cauchy_integrable)
  simpa only [Function.comp_def,Prod.swap,add_comm] using! hi

lemma sliceEnvelope_integrable (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    Integrable (sliceEnvelope axis J T) (volume.prod volume) := by
  cases axis
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact pairEnvelope_integrable J

lemma sliceEnvelope_integral (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    (∫q : ℝ×ℝ, sliceEnvelope axis J T q ∂volume.prod volume)=sliceMass J := by
  cases axis
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (q.1+q.2)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_symm _ (pairEnvelope_integrable J)]
    simp_rw [integral_mul_const,integral_add_right_eq_self]
    exact integral_const_mul _ _

lemma weighted_slice_pointwise (f : HeightSpace → ℂ) (axis : SliceAxis) (J N : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
      ‖f (sliceMap axis T q)‖ ≤
    (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
      ‖f (sliceMap axis T q)‖)/height T^N := by
  apply (le_div_iff₀ (pow_pos (height_pos T) N)).mpr
  have hn := pow_le_pow_left₀ (height_pos T).le (slice_height_le axis T q) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos (sliceMap axis T q).1.1
      (sliceMap axis T q).1.2 (sliceMap axis T q).2).le J) (norm_nonneg (f (sliceMap axis T q))))
  convert (preTransparency := .instances) hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T : ℝ,
      Integrable (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)≤K/height T^N := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    zlo zhi hzlo (J+N+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+N+2)
  let A := realGaussianBound slo shi zlo zhi*2^(J+N)*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|sliceMass (J+N)|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ axis T
  have hb := profile_moment_majorant W0 W1 (J+N) hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  let f (q : ℝ×ℝ) := jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
    (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖
  have hbound (q : ℝ×ℝ) : f q≤(A/height T^N)*sliceEnvelope axis (J+N) T q := by
    calc
      _ ≤ (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
          ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖)/height T^N :=
        weighted_slice_pointwise _ axis J N T q
      _ ≤ (A*jointEnvelope (J+N) (sliceMap axis T q))/height T^N :=
        div_le_div_of_nonneg_right (hb _) (pow_nonneg (height_pos T).le N)
      _ ≤ (A*sliceEnvelope axis (J+N) T q)/height T^N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (jointEnvelope_slice_le _ _ _ _) hA.le)
          (pow_nonneg (height_pos T).le N)
      _ = _ := by ring
  have hfnonneg (q : ℝ×ℝ) : 0≤f q := mul_nonneg
    (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
  have hf : Integrable f (volume.prod volume) := by
    apply ((sliceEnvelope_integrable axis (J+N) T).const_mul (A/height T^N)).mono'
    · have hc := (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)
      exact ((by cases axis <;> unfold sliceMap jointHeight <;> fun_prop : Continuous (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J)).mul hc.norm).aestronglyMeasurable
    · exact Eventually.of_forall (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)]; exact hbound q)
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ, (A/height T^N)*sliceEnvelope axis (J+N) T q ∂volume.prod volume :=
      integral_mono hf ((sliceEnvelope_integrable axis (J+N) T).const_mul _) hbound
    _ = (A/height T^N)*sliceMass (J+N) := by rw [integral_const_mul,sliceEnvelope_integral]
    _ ≤ (A/height T^N)*(1+|sliceMass (J+N)|) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hA.le (pow_nonneg (height_pos T).le N))
      linarith [le_abs_self (sliceMass (J+N))]
    _ = _ := by ring

end SevenEighths.ProbeMellinBoundary

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MellinBoundary (continued)
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology

namespace SevenEighths.ProbeMellinBoundary

open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

lemma cauchy_tendsto : Tendsto cauchy atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop (1:ℝ) (tendsto_pow_atTop (by decide : 2≠0)))

theorem boundaryControl_of_cauchy (F : ℂ → ℂ) {a b C : ℝ}
    (ha : Continuous (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Continuous (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hla : ∀t : ℝ, ‖F ((a:ℂ)+t*I)‖≤C*cauchy t)
    (hlb : ∀t : ℝ, ‖F ((b:ℂ)+t*I)‖≤C*cauchy t)
    (hjoin : ∀x∈uIcc a b, ∀t : ℝ, 1≤|t| → ‖F ((x:ℂ)+t*I)‖≤C*cauchy t) :
    BoundaryControl F a b := by
  have hi (h : Continuous (fun t : ℝ => F ((a:ℂ)+t*I))) :=
    (cauchy_integrable.const_mul C).mono' h.aestronglyMeasurable (Eventually.of_forall hla)
  have hj (ε : ℝ) (hε : |ε|=1) :
      Tendsto (fun T : ℝ => ∫x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (by simpa using (cauchy_tendsto.const_mul C).mul_const |b-a|)
    filter_upwards [eventually_ge_atTop 1] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have ht : |ε*T|=T := by rw [abs_mul,hε,one_mul,abs_of_nonneg (by linarith)]
    have hh := hjoin x (uIoc_subset_uIcc hx) (ε*T) (by simpa [ht] using hT)
    have he : cauchy (ε*T)=cauchy T := by
      unfold cauchy
      have hs : (ε*T)^2=T^2 := by nlinarith [sq_abs (ε*T)]
      rw [hs]
    simpa [he] using hh
  refine ⟨hi ha, (cauchy_integrable.const_mul C).mono' hb.aestronglyMeasurable
    (Eventually.of_forall hlb), ?_, ?_⟩
  · simpa using hj (-1) (by norm_num)
  · simpa using hj 1 (by norm_num)

lemma pole_distance_vertical (p x t : ℝ) : |x-p|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_re_le_norm ((x:ℂ)+t*I-p)

lemma pole_distance_horizontal (p x t : ℝ) : |t|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_im_le_norm ((x:ℂ)+t*I-p)

theorem boundaryControl_of_pole_product (F V G : ℂ → ℂ) {a b p C D δ : ℝ} (J : ℕ)
    (hδ : 0<δ) (hδ1 : δ≤1) (hpa : δ≤|a-p|) (hpb : δ≤|b-p|)
    (hF : ∀x∈uIcc a b, ∀t : ℝ, (x:ℂ)+t*I≠p →
      F ((x:ℂ)+t*I)=V ((x:ℂ)+t*I)*G ((x:ℂ)+t*I)/((x:ℂ)+t*I-p))
    (hV : ContinuousOn V {z : ℂ | z.re∈uIcc a b})
    (hG : ContinuousOn G {z : ℂ | z.re∈uIcc a b})
    (_hC : 0≤C) (hD : 0≤D)
    (hVbd : ∀x∈uIcc a b, ∀t : ℝ, height t^(J+2)*‖V ((x:ℂ)+t*I)‖≤C)
    (hGbd : ∀x∈uIcc a b, ∀t : ℝ, (x=a ∨ x=b ∨ 1≤|t|) →
      ‖G ((x:ℂ)+t*I)‖≤D*height t^J) :
    BoundaryControl F a b := by
  have hne (x t : ℝ) (hd : δ≤‖(x:ℂ)+t*I-p‖) : (x:ℂ)+t*I≠p := by
    intro h
    rw [h, sub_self, norm_zero] at hd
    linarith
  have hc (x : ℝ) (hx : x∈uIcc a b) (hd : δ≤|x-p|) :
      Continuous (fun t : ℝ => F ((x:ℂ)+t*I)) := by
    have hn (t : ℝ) : (x:ℂ)+t*I≠p := hne x t (hd.trans (pole_distance_vertical p x t))
    have hv := hV.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    have hg := hG.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    exact ((hv.mul hg).div (by fun_prop) (fun t => sub_ne_zero.mpr (hn t))).congr
      (fun t => (hF x hx t (hn t)).symm)
  have hbound (x : ℝ) (hx : x∈uIcc a b) (t : ℝ)
      (hd : δ≤‖(x:ℂ)+t*I-p‖) (hboundary : x=a ∨ x=b ∨ 1≤|t|) : ‖F ((x:ℂ)+t*I)‖≤(C*D/δ)*cauchy t := by
    have hn := hne x t hd
    have hv : height t^2 * (height t^J*‖V ((x:ℂ)+t*I)‖)≤C := by
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hVbd x hx t
    have hv' := CubicReflectionKernel.weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le _) (norm_nonneg _)) t hv
    change height t^J*‖V ((x:ℂ)+t*I)‖≤C*cauchy t at hv'
    rw [hF x hx t hn, norm_div, norm_mul]
    apply (div_le_div₀ (mul_nonneg (norm_nonneg _) (mul_nonneg hD (pow_nonneg (height_pos t).le _)))
      (mul_le_mul_of_nonneg_left (hGbd x hx t hboundary) (norm_nonneg _)) hδ hd).trans
    calc
      ‖V ((x:ℂ)+t*I)‖*(D*height t^J)/δ = D/δ*(height t^J*‖V ((x:ℂ)+t*I)‖) := by ring
      _ ≤ D/δ*(C*cauchy t) := mul_le_mul_of_nonneg_left hv' (div_nonneg hD hδ.le)
      _ = _ := by ring
  apply boundaryControl_of_cauchy F (hc a (left_mem_uIcc) hpa) (hc b (right_mem_uIcc) hpb)
  · intro t
    exact hbound a left_mem_uIcc t (hpa.trans (pole_distance_vertical p a t)) (Or.inl rfl)
  · intro t
    exact hbound b right_mem_uIcc t (hpb.trans (pole_distance_vertical p b t)) (Or.inr (Or.inl rfl))
  · intro x hx t ht
    exact hbound x hx t ((hδ1.trans ht).trans (pole_distance_horizontal p x t)) (Or.inr (Or.inr ht))

lemma scaleBound_pos (q lo hi : ℝ) : 0<scaleBound q lo hi := Real.exp_pos _

lemma rpow_le_scaleBound {q lo hi x : ℝ} (hq : 0<q) (hx : x∈Icc lo hi) :
    q^x≤ scaleBound q lo hi := by
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  by_cases hl : 0≤Real.log q
  · exact (mul_le_mul_of_nonneg_left hx.2 hl).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hl)).trans (le_max_left _ _)

lemma cpow_le_scaleBound {q lo hi : ℝ} (hq : 0<q) (z : ℂ) (hz : z.re∈Icc lo hi) :
    ‖(q:ℂ)^z‖≤ scaleBound q lo hi := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
  exact rpow_le_scaleBound hq hz

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH AL : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (hAL : 0≤AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤ cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH)
    (hLbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤AL*height t^JL) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  let δ : ℝ := min (1/20) (cw-1)
  have hδ : 0<δ := lt_min (by norm_num) (sub_pos.mpr hcw)
  have hab : (19/20:ℝ)≤ cw := by linarith
  have hu : uIcc (19/20:ℝ) cw=Icc (19/20:ℝ) cw := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) (19/20) cw (JH+JL+2)
  let G (w : ℂ) := wScalar W0 X Z eta s z * (Y:ℂ)^(w-1) *
    (H w z*B w z) * HeckeOrigin.poleRemoved (fixedPrincipal M) w
  have hGc : ContinuousOn G {w : ℂ | w.re∈uIcc (19/20:ℝ) cw} := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact (continuous_const.mul ((continuous_id.sub continuous_const).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne')))).continuousOn
      · rw [hu]; exact hHB
    · exact (HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.continuousOn
  apply boundaryControl_of_pole_product _ (mellin W1) G (p:=1) (δ:=δ) (C:=C)
    (D:=‖wScalar W0 X Z eta s z‖*scaleBound Y (19/20-1) (cw-1)*AH*AL) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [abs_of_pos (sub_pos.mpr hcw)]; exact min_le_right _ _) ?_
    (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
      (W1.smooth ⊤)).continuous.continuousOn hGc hC.le
    (by unfold scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : (x:ℂ)+t*I≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : (x:ℂ)+t*I≠1 := by simpa using hn
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    unfold sourceMultiplier wScalar
    norm_num only [Complex.ofReal_one]
    field_simp [hEta]
  · intro x hx t hboundary
    have hv := cpow_le_scaleBound hY (((x:ℂ)+t*I)-1)
      (show (((x:ℂ)+t*I)-1).re∈Icc (19/20-1) (cw-1) by
        simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,zero_mul,
          sub_zero,add_zero,one_re]
        exact ⟨sub_le_sub_right (hu ▸ hx).1 1, sub_le_sub_right (hu ▸ hx).2 1⟩)
    dsimp only [G]
    rw [norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ ‖wScalar W0 X Z eta s z‖ * scaleBound Y (19/20-1) (cw-1) *
          (AH*height t^JH) * (AL*height t^JL) := by
        have hscale := (scaleBound_pos Y (19/20-1) (cw-1)).le
        have hp := (height_pos t).le
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity))
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

end SevenEighths.ProbeMellinBoundary

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MellinBoundary (continued)
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology

namespace SevenEighths.ProbeMellinBoundary

open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

lemma gaussian_strip_norm_le (s : ℂ) {a b x : ℝ} (ha : 0<a) (hx : x∈Icc a b) (t : ℝ) :
    ‖Complex.exp ((s+((x:ℂ)+t*I)-1)^2)‖≤Real.exp ((|s.re|+b+1)^2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hr : ((s+((x:ℂ)+t*I)-1)^2).re = (s.re+x-1)^2-(s.im+t)^2 := by simp [pow_two]
  rw [hr]
  have hxb : 0<x := ha.trans_le hx.1
  have hK : 0≤|s.re|+b+1 := by linarith [abs_nonneg s.re, hx.2]
  have hA : |s.re+x-1|≤|s.re|+b+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le s.re, le_abs_self s.re, hx.2]
  have hsq := pow_le_pow_left₀ (abs_nonneg (s.re+x-1)) hA 2
  rw [sq_abs] at hsq
  nlinarith [sq_nonneg (s.im+t)]

lemma zScalar_continuous (W1 : SchwartzMap ℝ ℂ) {X Z : ℝ} (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) : Continuous (zScalar W1 X Z eta s) := by
  unfold zScalar
  apply Continuous.div_const
  apply Continuous.mul_const
  apply Continuous.mul
  · exact (((continuous_const.sub continuous_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (((continuous_const.add continuous_id).sub continuous_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))))
  · fun_prop

lemma zScalar_norm_le (W1 : SchwartzMap ℝ ℂ) {X Z a b x : ℝ}
    (hX : 0<X) (hZ : 0<Z) (ha : 0<a) (hx : x∈Icc a b)
    (eta : Character) (s : ℂ) (t : ℝ) :
    ‖zScalar W1 X Z eta s ((x:ℂ)+t*I)‖≤zScaleBound W1 X Z eta s a b := by
  unfold zScalar zScaleBound
  simp only [norm_div,norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul
  · apply mul_le_mul
    · apply cpow_le_scaleBound hX
      simpa using And.intro (sub_le_sub_left hx.2 (1/2)) (sub_le_sub_left hx.1 (1/2))
    · apply cpow_le_scaleBound hZ
      simpa using And.intro (by linarith [hx.1] : s.re+a-1≤ s.re+x-1)
        (by linarith [hx.2] : s.re+x-1≤ s.re+b-1)
    · exact norm_nonneg _
    · exact (scaleBound_pos _ _ _).le
  · exact gaussian_strip_norm_le s ha hx t
  · exact norm_nonneg _
  · exact mul_nonneg (scaleBound_pos _ _ _).le (scaleBound_pos _ _ _).le

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH AL : ℝ}
    (he : 0<e) (hAH : 0≤AH) (hAL : 0≤AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤AH*height t^JH)
    (hLbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤AL*height t^JL) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  let δ : ℝ := min (1/600) e
  have hδ : 0<δ := lt_min (by norm_num) he
  have hab : (33/200:ℝ)≤1/6+e := by linarith
  have hu : uIcc (33/200:ℝ) (1/6+e)=Icc (33/200:ℝ) (1/6+e) := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    (33/200) (1/6+e) (by norm_num) (JH+JL+2)
  let G (z : ℂ) := zScalar W1 X Z eta s z * (H 1 z*B 1 z) *
    HeckeOrigin.poleRemoved (fixedPrincipal M) (6*z) / 6
  have hGc : ContinuousOn G {z : ℂ | z.re∈uIcc (33/200:ℝ) (1/6+e)} := by
    apply ContinuousOn.div_const
    apply ContinuousOn.mul
    · exact (zScalar_continuous W1 hX hZ eta s).continuousOn.mul (by rw [hu]; exact hHB)
    · exact ((HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.comp
        (continuous_const.mul continuous_id)).continuousOn
  apply boundaryControl_of_pole_product _ (mellin (paperRadialFourier W0)) G
    (p:=1/6) (δ:=δ) (C:=C)
    (D:=zScaleBound W1 X Z eta s (33/200) (1/6+e)*AH*AL/6) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [show (1/6+e:ℝ)-1/6=e by ring, abs_of_pos he]; exact min_le_right _ _)
    ?_ ?_ hGc hC.le (by unfold zScaleBound scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : 6*((x:ℂ)+t*I)≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : 6*((x:ℂ)+t*I)≠1 := by
      intro h
      apply hn
      push_cast
      linear_combination h/6
    have hd : (x:ℂ)+t*I-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hn)
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    apply (eq_div_iff hd).mpr
    unfold sourceMultiplier zScalar
    norm_num only [sub_self,Complex.cpow_zero,mul_one]
    field_simp [hEta]
  · apply (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.mono
    intro z hz
    have := (hu ▸ hz).1
    change 0<z.re
    linarith
  · intro x hx t hboundary
    dsimp only [G]
    rw [norm_div,norm_mul,norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ (zScaleBound W1 X Z eta s (33/200) (1/6+e) *
          (AH*height t^JH) * (AL*height t^JL))/6 := by
        have hS : 0≤zScaleBound W1 X Z eta s (33/200) (1/6+e) := by
          unfold zScaleBound scaleBound
          positivity
        have hp := (height_pos t).le
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤6)
        exact mul_le_mul
          (mul_le_mul (zScalar_norm_le W1 hX hZ (by norm_num) (hu ▸ hx) eta s t)
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) hS)
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

end SevenEighths.ProbeMellinBoundary

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MellinBoundary (continued)
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology

namespace SevenEighths.ProbeMellinBoundary

open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

theorem profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T A : ℝ, 0≤A → ∀G : ℝ×ℝ → ℂ,
      AEStronglyMeasurable G (volume.prod volume) →
      (∀q, ‖G q‖≤A*jointHeight (sliceMap axis T q).1.1
        (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ, ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)
        ≤ A*K/height T^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA G hG hbound
  obtain ⟨hm,hmb⟩ := hM σ hσ ξ hξ υ hυ axis T
  have hdom (q : ℝ×ℝ) : ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖≤
      A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
        (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) := by
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg _)
  have hi : Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q))
      (volume.prod volume) := by
    apply (hm.const_mul A).mono'
    · exact hG.mul (((onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)).aestronglyMeasurable)
    · exact Eventually.of_forall hdom
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ,
        A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) ∂volume.prod volume :=
      integral_mono hi.norm (hm.const_mul A) hdom
    _ = A*(∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume) :=
      integral_const_mul _ _
    _ ≤ A*(K/height T^N) := mul_le_mul_of_nonneg_left hmb hA
    _ = _ := by ring

end SevenEighths.ProbeMellinBoundary

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Euler
namespace OAI

noncomputable section

namespace SevenEighths.ProbeEuler

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Local
namespace OAI

namespace SevenEighths.ProbeLocal

noncomputable section

theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

end

end SevenEighths.ProbeLocal

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CorrectionBounds
namespace OAI

noncomputable section

namespace SevenEighths.ProbeLocal

lemma one_sub_ne_zero_of_norm_le_half (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  norm_num at ha

lemma inv_one_sub_norm_le_two (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith

theorem unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by
  rw [ProbeEuler.unramified_marked_error R V qInv K W D
    (one_sub_ne_zero_of_norm_le_half R hR) (one_sub_ne_zero_of_norm_le_half V hV),
    div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  have hnum : ‖R*((1-qInv)+(1-V)*(W-D))-K*V‖ ≤
      ‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖ := by
    calc
      _ ≤ ‖R*((1-qInv)+(1-V)*(W-D))‖ + ‖K*V‖ := norm_sub_le _ _
      _ = ‖R‖ * ‖(1-qInv)+(1-V)*(W-D)‖ + ‖K‖*‖V‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖R‖ * (‖1-qInv‖ + ‖1-V‖*‖W-D‖) + ‖K‖*‖V‖ := by
        gcongr
        simpa only [norm_mul] using norm_add_le (1-qInv) ((1-V)*(W-D))
      _ ≤ ‖R‖ * (2 + (1+‖V‖)*(‖W‖+‖D‖)) + ‖K‖*‖V‖ := by
        gcongr
        · calc ‖1-qInv‖ ≤ ‖(1:ℂ)‖+‖qInv‖ := norm_sub_le _ _
               _ ≤ 2 := by simp only [norm_one]; linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) V
        · exact norm_sub_le W D
  have hv := inv_one_sub_norm_le_two V hV
  have hr := inv_one_sub_norm_le_two R hR
  calc
    _ ≤ (‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖) * (2*2) := by
      gcongr
    _ ≤ 12 * ‖R‖ * (1+‖W‖) + 4*‖K‖*‖V‖ := by
      have he : 2 + (1+‖V‖)*(‖W‖+‖D‖) ≤ 3*(1+‖W‖) := by
        have : (1+‖V‖)*(‖W‖+‖D‖) ≤ (3/2:ℝ)*(‖W‖+1/2) := by gcongr ; linarith
        nlinarith [norm_nonneg W]
      nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg R)]

theorem continuedCorrection_defect_bound (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring

end SevenEighths.ProbeLocal

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.EulerCoordinates
namespace OAI

noncomputable section

namespace SevenEighths.ProbeEuler

open ActualEisensteinCubic CompletedGauss

local notation "O" => ActualEisensteinCubic.O

lemma actualAPhase_norm_le_one (eta : HeckeFamily.Character) (p : O) :
    ‖actualAPhase eta p‖ ≤ 1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CompletedGauss.angularFactor_norm_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (ProbeRow.targetMonoid_norm_le_one eta p))

lemma coordV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖coordV Q z‖ = Q ^ (-6*z.re) := by
  rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

lemma coordR_norm_le (Q : ℝ) (hQ : 0 < Q) (A x z : ℂ) (hA : ‖A‖ ≤ 1) :
    ‖coordR Q A x z‖ ≤ Q ^ (4-6*x.re-6*z.re) := by
  rw [coordR, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hA

lemma coordW_norm_le (Q : ℝ) (hQ : 0 < Q) (v w : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖coordW Q v w‖ ≤ Q ^ (-w.re) := by
  rw [coordW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hv

lemma coordD_norm_le (Q : ℝ) (hQ : 0 < Q) (eta v x : ℂ)
    (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖coordD Q eta v x‖ ≤ Q ^ (-x.re) := by
  rw [coordD, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hv

lemma coordK_norm_le (Q : ℝ) (hQ : 1 ≤ Q) (eta x w : ℂ) (he : ‖eta‖ ≤ 1) :
    ‖coordK Q eta x w‖ ≤ Q ^ (1-x.re-w.re) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsub : ‖(Q:ℂ)-1‖ = Q-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hQ)]
  rw [coordK, norm_mul, norm_mul, hsub, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have heq : (1-x.re-w.re) = 1 + (-x.re-w.re) := by ring
  rw [heq, Real.rpow_add hQ0, Real.rpow_one]
  simp only [Complex.sub_re, Complex.neg_re]
  gcongr
  calc ‖eta‖*(Q-1) ≤ 1*(Q-1) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hQ)
       _ ≤ Q := by linarith

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.EulerRegion
namespace OAI

noncomputable section

namespace SevenEighths.ProbeEuler

lemma rpow_le_half (Q a : ℝ) (hQ : 4 ≤ Q) (ha : a ≤ -(1/2)) : Q^a ≤ 1/2 := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc
    Q^a ≤ Q^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by rw [← one_div, div_le_iff₀ hs]; nlinarith [Real.sqrt_nonneg Q]

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GlobalHolomorphic
namespace OAI

noncomputable section

namespace SevenEighths.ProbeEuler

lemma coordV_differentiable (Q : ℝ) (hQ : 0<Q) : Differentiable ℂ (coordV Q) := by
  unfold coordV
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.const_mul (-6)).const_cpow (Or.inl hn)

lemma coordW_differentiable (Q : ℝ) (hQ : 0<Q) (v : ℂ) : Differentiable ℂ (coordW Q v) := by
  unfold coordW
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul v

lemma coordK_w_differentiable (Q : ℝ) (hQ : 0<Q) (eta x : ℂ) :
    Differentiable ℂ (fun w=>coordK Q eta x w) := by
  unfold coordK
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_sub (-x)).const_cpow (Or.inl hn)).const_mul (eta*(Q-1))

lemma unramifiedClosed_differentiableAt_w (Q : ℝ) (hQ : 0<Q) (A eta v x w z : ℂ)
    (_hR : 1-coordR Q A x z≠0) (_hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x t z) w := by
  have hw := coordW_differentiable Q hQ v
  have hk := coordK_w_differentiable Q hQ eta x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta x t) (-coordD Q eta v x+coordW Q v t*coordR Q A x z) 1) w := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GlobalHolomorphic (continued)
namespace OAI

noncomputable section

namespace SevenEighths.ProbeEuler

lemma coordR_z_differentiable (Q : ℝ) (hQ : 0<Q) (A x : ℂ) :
    Differentiable ℂ (fun z=>coordR Q A x z) := by
  unfold coordR
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (((differentiable_id.const_mul 6).const_sub (4-6*x)).const_cpow (Or.inl hn)).const_mul A

lemma unramifiedClosed_differentiableAt_z (Q : ℝ) (hQ : 0<Q) (A eta v x w z : ℂ)
    (hR : 1-coordR Q A x z≠0) (hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x w t) z := by
  have hv := coordV_differentiable Q hQ
  have hr := coordR_z_differentiable Q hQ A x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x t) (coordV Q t) (Q:ℂ)⁻¹
        (coordK Q eta x w) (-coordD Q eta v x+coordW Q v w*coordR Q A x t) 1) z := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DeletionBounds
namespace OAI

noncomputable section

open scoped Classical BigOperators

namespace SevenEighths.HeckeDeletionBounds

open HeckeFamily

theorem localBound_pos {σ : ℝ} (hσ : 0 < σ) : 0 < localBound σ := by
  unfold localBound
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

end SevenEighths.HeckeDeletionBounds

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.NormalProduct
namespace OAI

noncomputable section

open scoped BigOperators

namespace SevenEighths.ProbeEuler

lemma factor_ne_zero_of_defect (a : ℂ) (ha : ‖a-1‖ ≤ 1/2) : a ≠ 0 := by
  intro h
  rw [h] at ha
  norm_num at ha

lemma norm_log_le_defect (a : ℂ) (ha : ‖a-1‖ ≤ 1/2) :
    ‖Complex.log a‖ ≤ (3/2:ℝ)*‖a-1‖ := by
  simpa only [add_sub_cancel] using Complex.norm_log_one_add_half_le_self ha

lemma log_summable_of_defect {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    Summable (fun i => ‖Complex.log (F i)‖) := by
  apply (hb.mul_left (3/2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  exact (norm_log_le_defect _ ((hF i).trans (hhalf i))).trans
    (mul_le_mul_of_nonneg_left (hF i) (by norm_num))

lemma product_eq_exp_log {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    (∏' i, F i) = Complex.exp (∑' i, Complex.log (F i)) := by
  apply HasProd.tprod_eq
  apply ((log_summable_of_defect F b hb hF hhalf).of_norm.hasSum.cexp).congr
  intro s
  apply Finset.prod_congr rfl
  intro i hi
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hF i).trans (hhalf i)))

theorem normalProduct_analytic {ι : Type*} (F : ι → ℂ → ℂ) (b : ι → ℝ)
    (U : Set ℂ) (hU : IsOpen U) (hb : Summable b)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (hbound : ∀ i s, s ∈ U → ‖F i s-1‖ ≤ b i)
    (hhalf : ∀ i, b i ≤ 1/2) :
    AnalyticOnNhd ℂ (fun s => ∏' i, F i s) U := by
  have hlogs : ∀ i, DifferentiableOn ℂ (fun s => Complex.log (F i s)) U := by
    intro i
    apply (hF i).differentiableOn.clog
    intro s hs
    have hsmall : ‖F i s-1‖ < 1 := lt_of_le_of_lt ((hbound i s hs).trans (hhalf i)) (by norm_num)
    simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hd := Complex.differentiableOn_tsum_of_summable_norm (hb.mul_left (3/2)) hlogs hU
    (fun i s hs => (norm_log_le_defect _ ((hbound i s hs).trans (hhalf i))).trans
      (mul_le_mul_of_nonneg_left (hbound i s hs) (by norm_num)))
  apply DifferentiableOn.analyticOnNhd _ hU
  apply hd.cexp.congr
  intro s hs
  exact product_eq_exp_log (fun i => F i s) b hb (fun i => hbound i s hs) hhalf

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.NormalProduct (continued)
namespace OAI

noncomputable section

open scoped BigOperators

namespace SevenEighths.ProbeEuler

lemma norm_log_sum_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    ‖∑' i, Complex.log (F i)‖ ≤ (3/2:ℝ) * ∑' i, b i := by
  have hs := log_summable_of_defect F b hb hF hhalf
  calc
    _ ≤ ∑' i, ‖Complex.log (F i)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' i, (3/2:ℝ)*b i := Summable.tsum_le_tsum
      (fun i => (norm_log_le_defect _ ((hF i).trans (hhalf i))).trans
        (mul_le_mul_of_nonneg_left (hF i) (by norm_num))) hs (hb.mul_left _)
    _ = _ := tsum_mul_left

theorem product_defect_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2)
    (hsmall : (∑' i, b i) ≤ 1/6) : ‖(∏' i, F i)-1‖ ≤ 1/2 := by
  have hlog := norm_log_sum_le F b hb hF hhalf
  have hlog1 : ‖∑' i, Complex.log (F i)‖ ≤ 1 := by linarith
  rw [product_eq_exp_log F b hb hF hhalf]
  exact (Complex.norm_exp_sub_one_le hlog1).trans (by linarith)

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
namespace OAI

noncomputable section

open scoped Classical BigOperators

namespace SevenEighths.ProbePhysical

open ActualEisensteinCubic ProbeEuler CompletedGauss

local notation "O" => ActualEisensteinCubic.O

local notation "Id" => Ideal O

lemma CorrectionTail.half {S : Finset Id} (h : CorrectionTail S)
    (P : {P : PrimeIdeal // P.val∉S}) : globalPrimeDefectBound P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>globalPrimeDefectBound_nonneg Q.val)
  linarith [h.small]

end SevenEighths.ProbePhysical

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Strip
namespace OAI

noncomputable section

open scoped Classical Topology

open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

theorem gammaConstant_pos : 0 < gammaConstant :=
  div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))

theorem leftConstant_pos : 0 < leftConstant :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) gammaConstant_pos

end SevenEighths.HeckeStrip

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput (continued)
namespace OAI

noncomputable section

open scoped Classical Topology

open Set

namespace SevenEighths.HeckeLogarithmicInput

open HeckeFamily

theorem uniformConstant_nonneg : 0 ≤ uniformConstant := by
  have hc := HeckeStrip.leftConstant_pos
  have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
  unfold uniformConstant
  positivity

end SevenEighths.HeckeLogarithmicInput

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth
namespace OAI

noncomputable section

open scoped Classical

namespace SevenEighths.HeckeReciprocalGrowth

open HeckeFamily HeckeLogarithmic HeckeDeletionBounds

theorem polynomial_reciprocal_bound (χ : Character) (a : ℝ)
    (hβ : HeckeZeroSupremum.beta < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2) := by
  let e : ℝ := min (1/2000) ((a-HeckeZeroSupremum.beta)/16)
  have he : 0<e := lt_min (by norm_num) (by linarith)
  have he' : e<1/1000 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hmargin : HeckeZeroSupremum.beta+8*e ≤ a := by
    have hh := min_le_right (1/2000 : ℝ) ((a-HeckeZeroSupremum.beta)/16)
    change e ≤ (a-HeckeZeroSupremum.beta)/16 at hh
    linarith
  obtain ⟨C,hC,hbound⟩ := reciprocal_subpower e 1 he he' (by norm_num)
  let K : ℝ := C*((radical χ.modulus).absNorm : ℝ)*(2*(χ.modulus.absNorm : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨18*K, by positivity, ?_⟩
  intro s hs
  have h := hbound χ s (hmargin.trans hs)
  have hheight : (3+|s.im|)^2 ≤ 18*(1+|s.im|^2) := by
    nlinarith [sq_nonneg (|s.im|-1), sq_nonneg |s.im|]
  rw [Real.rpow_one] at h
  calc
    _ ≤ K*(3+|s.im|)^2 := by
      convert (preTransparency := .instances) h using 1 ; unfold K presentationComplexity complexity ; ring
    _ ≤ K*(18*(1+|s.im|^2)) := mul_le_mul_of_nonneg_left hheight hK
    _ = _ := by ring

end SevenEighths.HeckeReciprocalGrowth

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalMellinGrowth
namespace OAI

noncomputable section

open scoped Classical Topology

open Complex Set

namespace SevenEighths.PrincipalMellinGrowth

open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

theorem principalConstant_pos (M : Ideal HeckeFamily.O) [NeZero M] :
    0<principalConstant M := by
  have hQ : 0<(M.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  exact mul_pos (mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg])
    (Real.rpow_pos_of_pos hQ _)) (pow_pos (HeckeDeletionBounds.localBound_pos (by norm_num)) _)

end SevenEighths.PrincipalMellinGrowth

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalMellinGrowth (continued)

namespace OAI

noncomputable section

open scoped Classical Topology

open Complex Set

namespace SevenEighths.PrincipalMellinGrowth

open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

theorem wAmplitude_pos (M : Ideal HeckeFamily.O) [NeZero M] {cw : ℝ} (hcw : 1<cw) :
    0<wAmplitude M cw := by
  unfold wAmplitude
  exact mul_pos (mul_pos (by norm_num) (by linarith)) (principalConstant_pos M)

end SevenEighths.PrincipalMellinGrowth

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalMellinGrowth (continued)

namespace OAI

noncomputable section

open scoped Classical Topology

open Complex Set

namespace SevenEighths.PrincipalMellinGrowth

open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤ cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply ProbeMellinBoundary.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY eta s z hEta H B
    (AL:=wAmplitude M cw) hcw hAH (wAmplitude_pos M hcw).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_w_growth M hcw hx t

end SevenEighths.PrincipalMellinGrowth

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalMellinGrowth (continued)

namespace OAI

noncomputable section

open scoped Classical Topology

open Complex Set

namespace SevenEighths.PrincipalMellinGrowth

open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

end SevenEighths.PrincipalMellinGrowth

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds (continued)
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory

namespace SevenEighths.ProbeFiniteProductBounds

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal

open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

lemma replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith

lemma localBound_nonneg (Bx Bz : ℝ) (P : PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

lemma slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (localBound_nonneg Bx Bz P))

lemma boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

end SevenEighths.ProbeFiniteProductBounds

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FiniteProductX
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory

namespace SevenEighths.ProbeFiniteProductX

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal

open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds

local notation "Id" => Ideal ActualEisensteinCubic.O

theorem continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

end SevenEighths.ProbeFiniteProductX

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

lemma zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0≤zBoxAmplitude M Bz := by
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ≤‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖≤A) :
    ‖LFunction χ s‖≤A/δ := by
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _ ≤ A := hA

lemma height_le_joint_s (t v u : ℝ) : height t≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]

lemma height_le_joint_z (t v u : ℝ) : height v≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

local instance instCountableO : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

local instance instCountableIdealO : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

lemma ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => ideal_correction_measurable η P.val x w z hx hw hz)

lemma local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (local_multiplier_measurable η P x w z hx hw hz)

lemma LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta<a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : HeckeZeroSupremum.beta<a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun p : HeightSpace => 6*p.1.2))
  have hZL' : Measurable (fun p : HeightSpace => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+p.1.2*I))) := by
    convert (preTransparency := .instances) hZL using 1
    funext p
    congr 1
    push_cast
    ring
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma height_le_joint_w (t v u : ℝ) : height u≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

lemma boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0<boxScale X Y Z a Bs Bz cw := by
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

lemma arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1<cw) (hC : 0≤C) (hw : 0≤δw) (hz : 0≤δz) :
    0≤arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (boxScale_pos X Y Z a Bs Bz cw).le
  have hb := slotBound_nonneg J T b Bs Bz
  have hza := zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalContours (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

end SevenEighths.ProbePrincipalContours

end

end OAI

end

section
-- module Transport.TunedCandidate (LW56e2)
namespace RH.Transport.TunedCandidate

open RH.Transport.LocalBounds

noncomputable section

theorem p_lt_one_thousandth : p < 1 / 1000 := by norm_num [p]

end

end RH.Transport.TunedCandidate

end

section
-- module Transport.PhysicalAnalytic.GlobalCorrection (LW56e2)
namespace RH.Transport.PhysicalAnalytic

noncomputable section

open scoped Classical BigOperators

open OAI OAI.SevenEighths

open ActualEisensteinCubic ProbeEuler ProbePhysical CompletedGauss

local notation "O" => ActualEisensteinCubic.O

local notation "Id" => Ideal O

theorem unramifiedClosed_transported_open_region_bound
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  dsimp [Geometry.boundary] at hx
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(221/100:ℝ) + 3*p/2) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7/8:ℝ) + p/4) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(31/40:ℝ) + p/4) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by linarith))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by linarith)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by linarith)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by linarith)
      _ = _ := by ring
  nlinarith

theorem transported_open_region_denominators
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    1 - coordR Q A x z ≠ 0 ∧ 1 - coordV Q z ≠ 0 ∧
      1 - coordD Q eta v x ≠ 0 := by
  dsimp [Geometry.boundary] at hx
  have hQ0 : 0 < Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1 / 2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖ ≤ 1 / 2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_transported_analytic_w
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => unramifiedClosed Q A eta v x w z)
      {w : ℂ | (9 / 10 : ℝ) < w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w _
  have hd := transported_open_region_denominators p hp Q A eta v x z
    hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_transported_analytic_z
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) :
    AnalyticOnNhd ℂ (fun z => unramifiedClosed Q A eta v x w z)
      {z : ℂ | (4 / 25 : ℝ) < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := transported_open_region_denominators p hp Q A eta v x z
    hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem idealClosedCorrection_transported_bound
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : Geometry.boundary p ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    ‖idealClosedCorrection η P x w z - 1‖ ≤ globalPrimeDefectBound P := by
  apply unramifiedClosed_transported_open_region_bound p hp
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_transported_bound
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ) (hx : Geometry.boundary p ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    ‖globalClosedCorrection η S x w z - 1‖ ≤ (1 / 2 : ℝ) :=
  product_defect_le _ _ hS.summable
    (fun P => idealClosedCorrection_transported_bound p hp η P.val
      (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem globalClosedCorrection_transported_analytic_w
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ)
    (hx : Geometry.boundary p ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z)
      {w : ℂ | (9 / 10 : ℝ) < w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_transported_analytic_w p hp
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_transported_bound p hp η P.val
      (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_transported_analytic_z
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ)
    (hx : Geometry.boundary p ≤ x.re) (hw : (9 / 10 : ℝ) ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z)
      {z : ℂ | (4 / 25 : ℝ) < z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_transported_analytic_z p hp
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_transported_bound p hp η P.val
      (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end

end RH.Transport.PhysicalAnalytic

end

section
-- module Transport.PhysicalAnalytic.FiniteProducts (LW56e2)
namespace RH.Transport.PhysicalAnalytic.FiniteProducts

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory

open OAI OAI.SevenEighths

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal

open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

open ProbeFiniteProductBounds ProbeFiniteProductX

local notation "Id" => Ideal ActualEisensteinCubic.O

theorem correction_lower_bound (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hb := (idealClosedCorrection_transported_bound τ hτ η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem correction_ne_zero (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (correction_lower_bound τ hτ η S hS P hP x w z hx hw hz))

theorem correction_inverse_bound (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hh := correction_lower_bound τ hτ η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma marked_differentiableAt_w (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : Geometry.boundary τ ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := transported_open_region_denominators τ hτ (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : Geometry.boundary τ ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := transported_open_region_denominators τ hτ (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := transported_open_region_denominators τ hτ (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := unramifiedClosed_transported_analytic_w τ hτ (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := marked_differentiableAt_w τ hτ η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := correction_ne_zero τ hτ η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_transported_analytic_z τ hτ (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := transported_open_region_denominators τ hτ (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := marked_differentiableAt_z τ hτ η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := correction_ne_zero τ hτ η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma marked_bound (τ : ℝ) (hτ : τ < 1 / 1000) (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : Geometry.boundary τ ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

theorem local_norm_bound (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (Geometry.boundary τ) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    marked_bound τ hτ Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := correction_inverse_bound τ hτ η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

theorem slot_analytic_w (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_w τ hτ η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_z τ hτ η S hS P (hT j hj P hp) x w hx hw)

theorem slot_norm_bound (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (Geometry.boundary τ) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (local_norm_bound τ hτ η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma global_norm_bound (τ : ℝ) (hτ : τ < 1 / 1000) (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : Geometry.boundary τ ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  have hb := globalClosedCorrection_transported_bound τ hτ η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem combined_slot_analytic_w (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (globalClosedCorrection_transported_analytic_w τ hτ η S hS x z hx hz).mul (slot_analytic_w τ hτ η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : Geometry.boundary τ ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (globalClosedCorrection_transported_analytic_z τ hτ η S hS x w hx hw).mul (slot_analytic_z τ hτ η S hS J T b hT x w hx hw)

theorem combined_slot_bound (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (Geometry.boundary τ) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  have hτbound : (4 / 5 : ℝ) ≤ Geometry.boundary τ := by
    dsimp [Geometry.boundary]; linarith
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound τ hτ η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (slot_norm_bound τ hτ η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem source_w_boundary (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : Geometry.boundary τ ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1< cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_w τ hτ η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound τ hτ η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem source_multiplier_differentiable_w (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : Geometry.boundary τ ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (combined_slot_analytic_w τ hτ η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y:ℂ)^(w-1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem source_multiplier_differentiable_z (τ : ℝ) (hτ : τ < 1 / 1000) {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : Geometry.boundary τ ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (combined_slot_analytic_z τ hτ η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

end

end RH.Transport.PhysicalAnalytic.FiniteProducts

end

section
-- module Transport.PhysicalAnalytic.Contours (LW56e2)
namespace RH.Transport.PhysicalAnalytic.Contours

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

open OAI OAI.SevenEighths

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours

local notation "Id" => Ideal ActualEisensteinCubic.O

local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

abbrev transportBoundary : ℝ := Geometry.boundary TunedCandidate.p

lemma arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : transportBoundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0< δw) (hdz : 0< δz)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw≤‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz≤‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have htransportBoundary : (4 / 5 : ℝ) < transportBoundary := by
    norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1/2-((ξ:ℂ)+p.1.2*I))
    (show (1/2-((ξ:ℂ)+p.1.2*I) : ℂ).re∈Icc (1/2-Bz) (1/2-33/200) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
      norm_num only [show (1/2:ℂ).re=1/2 by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]]
      constructor <;> linarith [hξ.1,hξ.2])
  have hz := cpow_le_scaleBound hZ (((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)
    (show ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1) : ℂ).re∈Icc (a+33/200-1) (Bs+Bz-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hσ.1,hσ.2,hξ.1,hξ.2])
  have hy := cpow_le_scaleBound hY (((υ:ℂ)+p.2*I)-1)
    (show (((υ:ℂ)+p.2*I)-1 : ℂ).re∈Icc (19/20-1) (cw-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hυ.1,hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖≤ C*height p.1.1^2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := FiniteProducts.combined_slot_bound TunedCandidate.p TunedCandidate.p_lt_one_thousandth η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
    ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2) (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ:ℂ)+p.2*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hυ.1]
  have hw1 : (υ:ℂ)+p.2*I≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hwgap; linarith
  have hz0 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hξ.1]
  have hz1 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hzgap; linarith
  have hlz0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏P∈S,P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏P∈S,P)) (6*((ξ:ℂ)+p.1.2*I))‖≤
      (zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3 := by convert hlz0 using 1; ring
  have hlw : ‖LFunction (fixedPrincipal (∏P∈S,P)) ((υ:ℂ)+p.2*I)‖≤
      (wAmplitude (∏P∈S,P) cw/δw)*height p.2^3 := by convert hlw0 using 1; ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1/2-Bz) (1/2-33/200)).le
  have hsY := (scaleBound_pos Y (19/20-1) (cw-1)).le
  have hsZ := (scaleBound_pos Z (a+33/200-1) (Bs+Bz-1)).le
  have hHB := mul_nonneg (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p] : (0:ℝ)≤3/2) (slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏P∈S,P) hcw).le hdw.le
  calc
    _ = ‖(X:ℂ)^(1/2-((ξ:ℂ)+p.1.2*I))‖ *
        ‖(Z:ℂ)^(((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)‖ *
        ‖(Y:ℂ)^(((υ:ℂ)+p.2*I)-1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖ *
        ‖globalClosedCorrection η S ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          slotMultiplier η J T b ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ := by
      simp only [arithmeticMultiplier,norm_mul]
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*height p.1.1^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*height p.2^3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*jointHeight p.1.1 p.1.2 p.2^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*jointHeight p.1.1 p.1.2 p.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*jointHeight p.1.1 p.1.2 p.2^3) := by
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : transportBoundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have htransportBoundary : (4 / 5 : ℝ) < transportBoundary := by
    norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  apply arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : transportBoundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0≤ C ∧ 0< K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume)≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  have htransportBoundary : (4 / 5 : ℝ) < transportBoundary := by
    norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,arithmetic_profile_eq_source] using hh

theorem source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : transportBoundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  have htransportBoundary : (4 / 5 : ℝ) < transportBoundary := by
    norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  obtain ⟨C,K,hC,hK,hslice⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z a (1/6+e) (19/20) 3 hX hY hZ ha hβ
    (by linarith) (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]) (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]) (by linarith) (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]) 0
  have hi := (hslice .s t).1
  have hs0 : (a:ℂ)+t*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hpair : Integrable (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I))
        ((19/20:ℝ)+q.2*I) ((1/6+e:ℝ)+q.1*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((1/6+e:ℝ)+q.1*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((19/20:ℝ)+q.2*I)) (volume.prod volume) := by
    simpa only [sliceMap,continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : transportBoundary≤ s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0< e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  have htransportBoundary : (4 / 5 : ℝ) < transportBoundary := by
    norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]) (slotBound_nonneg J T b _ _))
    (zBoxAmplitude_nonneg _ _) 0 3
  · exact (FiniteProducts.combined_slot_analytic_z TunedCandidate.p TunedCandidate.p_lt_one_thousandth η S hS.tail J T b hT s 1 hs (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p])).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using FiniteProducts.combined_slot_bound TunedCandidate.p TunedCandidate.p_lt_one_thousandth η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]) (by simpa using hx)
  · intro x hx t _
    exact fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem source_ordered_at_height_t {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : transportBoundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
    HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
    (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  have htransportBoundary : (4 / 5 : ℝ) < transportBoundary := by
    norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (transportBoundary : ℝ)≤(((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (FiniteProducts.source_multiplier_differentiable_w TunedCandidate.p TunedCandidate.p_lt_one_thousandth η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9/10 : ℝ)< w.re
    linarith [hw.1]
  · intro z hz
    have hh := FiniteProducts.source_w_boundary TunedCandidate.p TunedCandidate.p_lt_one_thousandth η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith) hη hcw
    convert boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (FiniteProducts.source_multiplier_differentiable_z TunedCandidate.p TunedCandidate.p_lt_one_thousandth η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p])).mono
    intro z hz
    change (4/25 : ℝ)< z.re
    linarith [hz.1]
  · exact hzb
  · exact source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

end

end RH.Transport.PhysicalAnalytic.Contours

end

theorem solution : type_of% @RH.Transport.PhysicalAnalytic.Contours.source_ordered_at_height_t := @RH.Transport.PhysicalAnalytic.Contours.source_ordered_at_height_t
