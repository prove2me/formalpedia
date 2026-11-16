-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.actual_nonfloor_cube_norm
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T20:54:53.012427+00:00
-- url     : https://prove2.me/submissions/083e7ec2-8363-4646-8846-155a068d22b2

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
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowAmplitudeOnLines_buffered_bound
import Theorems.Thm_RH_Transport_PhysicalHigh_actual_nonfloor_class_from_raw_moments
set_option autoImplicit false

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

lemma jointEnvelope_integrable (J : ℕ) : Integrable (jointEnvelope J) heightMeasure := by
  have hp : MeasurePreserving (fun p : ℝ×ℝ => (p.1+p.2,p.2))
      (volume.prod volume) (volume.prod volume) := by
    have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
        (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
    have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
    simpa only [Function.comp_def,Prod.swap,add_comm] using! hp1
  have ht := hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hi := ((gaussianMoment_integrable J).mul_prod cauchy_integrable).mul_prod cauchy_integrable
  exact ht.integrable_comp_of_integrable hi

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

theorem profile_uniform_moments (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖) heightMeasure ∧
      (∫p : HeightSpace, jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤K := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 zlo zhi hzlo (J+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+2)
  let A := realGaussianBound slo shi zlo zhi*2^J*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|∫p, jointEnvelope J p ∂heightMeasure|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ
  have hbound := profile_moment_majorant W0 W1 J hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  have hc := onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ (hzlo.trans_le hξ.1)
  have hf : Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
      ‖onLines W0 W1 σ ξ υ p‖) heightMeasure := by
    apply ((jointEnvelope_integrable J).const_mul A).mono'
    · exact ((by unfold jointHeight; fun_prop : Continuous (fun p : HeightSpace =>
        jointHeight p.1.1 p.1.2 p.2^J)).mul hc.norm).aestronglyMeasurable
    · apply Eventually.of_forall
      intro p
      have hn : 0≤jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ :=
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
      rw [Real.norm_eq_abs,abs_of_nonneg hn]
      exact hbound p
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫p, A*jointEnvelope J p ∂heightMeasure := integral_mono hf
      ((jointEnvelope_integrable J).const_mul A) hbound
    _ = A*(∫p, jointEnvelope J p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := le_abs_self (∫p, jointEnvelope J p ∂heightMeasure)
      exact mul_le_mul_of_nonneg_left (by linarith) hA.le

end SevenEighths.ProbeMellinBoundary

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RadialIdentity
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory

namespace SevenEighths.ProbePhysical

open ActualEisensteinCubic EisensteinSchwartzPoisson

local notation "O" => ActualEisensteinCubic.O

local notation "Id" => Ideal O

lemma elementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

end SevenEighths.ProbePhysical

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.InitialScales
namespace OAI

noncomputable section

open MeasureTheory

namespace SevenEighths.ProbePhysical

open ProbeMellinBoundary

lemma sourceMellinWeight_eq_scale (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z=sourceScale X Y Z x w z*profile W0 W1 x w z := by
  unfold sourceMellinWeight sourceScale profile
  ring

lemma sourceScale_continuous (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Continuous (fun q : (ℂ × ℂ) × ℂ =>sourceScale X Y Z q.1.1 q.1.2 q.2) := by
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceScale
  exact (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>(1/2:ℂ)-q.2)).const_cpow (Or.inl hx)).mul
    (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.1+q.2-1)).const_cpow (Or.inl hz)))) |>.mul
      ((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.2-1)).const_cpow (Or.inl hy))

lemma sourceScale_norm (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    ‖sourceScale X Y Z x w z‖=X^(1/2-z.re)*Z^(x.re+z.re-1)*Y^(w.re-1) := by
  simp only [sourceScale,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hY,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  norm_num [Complex.sub_re,Complex.add_re]

lemma sourceMellinWeight_initial_continuous (W0 W1 : SchwartzMap ℝ ℂ)
    (a1 b1 : ℝ) (ha1 : 0<a1) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Continuous (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) := by
  have hc := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  simpa only [Function.comp_def,Pi.mul_def,sourceMellinWeight_eq_scale,onLines] using
    hc.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ)

end SevenEighths.ProbePhysical

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSlotEstimate (continued)
namespace OAI

noncomputable section

open scoped Classical BigOperators

open Complex

namespace SevenEighths.PrincipalSlotEstimate

open ProbeEuler ProbeLocal

def principalRawFactor (Q : ℝ) (A η s : ℂ) : ℂ :=
  localFactor (coordV Q (1 / 6)) (coordW Q 1 1) (principalMarked Q A η s)

end SevenEighths.PrincipalSlotEstimate

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalProduct (continued)
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace SevenEighths.ProbeEuler

open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection

local notation "O" => ActualEisensteinCubic.O

def primeDefectBound (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-(363/200:ℝ))

end SevenEighths.ProbeEuler

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TuplePrime
namespace OAI

noncomputable section

open scoped Classical

namespace SevenEighths.ProbePhysical

open CompletedGauss CanonicalQuadraticSieve ProbeRow

local notation "O" => ActualEisensteinCubic.O

local notation "Id" => Ideal O

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

end SevenEighths.ProbePhysical

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.SelectedAgreement
namespace OAI

noncomputable section

open scoped Classical ComplexConjugate

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow

open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

local notation "O" => HeckeFamily.O

theorem ramifiedCorrection_eq_marked (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z=
      1+(1-coordV P.val.absNorm z)*continuedMarkedLocal η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := (supported_prime_data p hp hsp).1
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  change ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)=
    1+(1-coordV P.val.absNorm z)*rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
      ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)
  unfold ramifiedClosed
  rw [hnorm]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Measurable
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler

open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

local notation "O" => HeckeFamily.O

lemma rowClosedMarked_measurable {α : Type*} [MeasurableSpace α]
    (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p}) (η a ρ : ℂ) (j : ℕ)
    (X W V : α→ℂ) (hX : Measurable X) (hW : Measurable W) (hV : Measurable V) :
    Measurable (fun t=>rowClosedMarked p hp hg η a (X t) (W t) (V t) ρ j) := by
  unfold rowClosedMarked rowBaseFinite rowMarkedTerm rowWeightedScalar weightedScalar evenRatio
  simp only [Nat.reduceAdd,Nat.reduceMul,OfNat.ofNat_ne_zero,Nat.one_ne_zero,ite_false]
  fun_prop

lemma continuedMarkedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedMarkedLocal η u P hs (x t) (w t) (z t)) := by
  have hQ : (P.val.absNorm:ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold continuedMarkedLocal
  apply rowClosedMarked_measurable
  · exact measurable_const_cpow _ hQ _ hx.neg
  · exact measurable_const_cpow _ hQ _ hw.neg
  · unfold coordV
    apply measurable_const_cpow _ (by exact_mod_cast hQ)
    fun_prop

lemma ramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>ramifiedCorrection η u P hs (x t) (w t) (z t)) := by
  have hm := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  simp_rw [ramifiedCorrection_eq_marked]
  unfold coordV
  fun_prop (disch := exact hQ)

lemma idealUnramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>idealUnramifiedCorrection η u P (x t) (w t) (z t)) := by
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealUnramifiedCorrection unramifiedClosed ProbeLocal.continuedCorrection markedFactor
    coordV coordR coordW coordD coordK
  fun_prop (disch := exact hQ)

lemma continuedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedCorrection S hS η u (x t) (w t) (z t)) := by
  unfold continuedCorrection ramifiedProduct unramifiedProduct
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro P hP
    exact ramifiedCorrection_measurable η u P.val _ x w z hx hw hz
  · apply Measurable.tprod
    intro P
    unfold unramifiedFactor
    split_ifs
    · exact measurable_const
    · exact idealUnramifiedCorrection_measurable η u P.val x w z hx hw hz

lemma continuedCompensatedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z B q : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z)
    (hB : Measurable B) (hq : Measurable q) :
    Measurable (fun t=>continuedCompensatedLocal η u P hs (x t) (w t) (z t) (B t) (q t)) := by
  have hM := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement coordV coordW coordD
  fun_prop (disch := exact hQ)

lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  apply measurable_of_countable_not_continuousAt
  apply ((Set.finite_singleton (1:ℂ)).insert 0).countable.mono
  intro s hs
  by_contra hn
  have h0 : s≠0 := fun h=>hn (by simp [h])
  have h1 : s≠1 := fun h=>hn (by simp [h])
  exact hs (LFunction_differentiableAt χ h0 (Or.inl h1)).continuousAt

lemma regularizedL_measurable (χ : Character) : Measurable (HeckeReciprocal.regularizedL χ) := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_singleton (0:ℂ)).mono
  intro s hs
  by_contra hn
  exact hs (HeckeReciprocal.regularizedL_differentiableAt χ (by simpa using hn)).continuousAt

lemma reciprocal_measurable (χ : Character) : Measurable (HeckeReciprocal.reciprocal χ) := by
  have hL := LFunction_measurable χ
  have hR := regularizedL_measurable χ
  unfold HeckeReciprocal.reciprocal
  split_ifs <;> fun_prop

lemma continuedL_measurable (χ : Character) : Measurable (HeckeOrigin.continued χ) := by
  have hL := LFunction_measurable χ
  have hR := (HeckeOrigin.poleRemoved_entire χ).continuous.measurable
  unfold HeckeOrigin.continued
  split_ifs <;> fun_prop

lemma physicalCompensatedRow_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>physicalCompensatedRow S hS T hT η u (x t) (w t) (z t)) := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply Measurable.mul
  · exact (((LFunction_measurable _).comp (by fun_prop)).mul
      ((continuedL_measurable _).comp hw)).mul ((reciprocal_measurable _).comp hx)
  · apply Measurable.mul
    · exact continuedCorrection_measurable _ _ η u x w z hx hw hz
    · apply Finset.measurable_prod
      intro P hP
      have hQ : (P.val.val.absNorm:ℂ)≠0 := by
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
      apply continuedCompensatedLocal_measurable _ _ _ _ x w z _ _ hx hw hz
      · exact (measurable_const_cpow _ hQ x hx).const_mul _
      · exact measurable_const_cpow _ hQ _ hw.neg

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ProfileIntegral
namespace OAI

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace SevenEighths.ProbeHighRowFamily

open ProbePhysical ProbeMellinBoundary

lemma two_height_bound (t v w : ℝ) :
    (3+|t|)^2*(3+|w|)^2≤81*jointHeight t v w^4 := by
  have ht : 3+|t|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  have hw : 3+|w|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  calc
    _ ≤ (3*jointHeight t v w)^2*(3*jointHeight t v w)^2 := by gcongr
    _ = _ := by ring

theorem source_profile_integral_bound (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) :
    ∃C : ℝ,0<C ∧ ∀σ∈Icc slo shi,∀r∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀A : ℝ,0≤A → ∀F : HeightSpace→ℝ,
      AEStronglyMeasurable F heightMeasure → (∀p,0≤F p) →
      (∀p,F p≤A*(3+|p.1.1|)^2*(3+|p.2|)^2) →
      Integrable (fun p=>‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p) heightMeasure ∧
      (∫p,‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p ∂heightMeasure)
        ≤C*A*(X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)) := by
  obtain ⟨D,hD,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo 4
  refine ⟨81*D,by positivity,?_⟩
  intro σ hσ r hr υ hυ X Y Z hX hY hZ A hA F hF hF0 hFb
  let E : ℝ := X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let M : HeightSpace→ℝ := fun p=>jointHeight p.1.1 p.1.2 p.2^4*‖onLines W0 W1 σ r υ p‖
  have hMi : Integrable M heightMeasure := (hM σ hσ r hr υ hυ).1
  have hMb : (∫p,M p ∂heightMeasure)≤D := (hM σ hσ r hr υ hυ).2
  let f : HeightSpace→ℝ := fun p=>‖sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p
  have hfm : AEStronglyMeasurable f heightMeasure :=
    (sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
      σ r υ (hzlo.trans_le hr.1)).norm.aestronglyMeasurable.mul hF
  have hf0 (p : HeightSpace) : 0≤f p := mul_nonneg (norm_nonneg _) (hF0 p)
  have hfb (p : HeightSpace) : f p≤(E*A*81)*M p := by
    have h1 := (hFb p).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (two_height_bound p.1.1 p.1.2 p.2) hA)
    have hs : ‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖=E*‖onLines W0 W1 σ r υ p‖ := by
      rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ]
      simp [E,onLines]
    dsimp only [f]
    rw [hs]
    calc
      _ ≤ (E*‖onLines W0 W1 σ r υ p‖)*(A*(81*jointHeight p.1.1 p.1.2 p.2^4)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hE (norm_nonneg _))
      _ = _ := by dsimp [M];ring
  have hfi : Integrable f heightMeasure := (hMi.const_mul (E*A*81)).mono' hfm
    (Filter.Eventually.of_forall fun p=>by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 p)];exact hfb p)
  refine ⟨hfi,?_⟩
  calc
    (∫p,f p ∂heightMeasure) ≤ ∫p,(E*A*81)*M p ∂heightMeasure :=
      integral_mono hfi (hMi.const_mul _) hfb
    _ = (E*A*81)*(∫p,M p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ (E*A*81)*D := mul_le_mul_of_nonneg_left hMb (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set Complex

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

local notation "O" => HeckeFamily.O

lemma weightedRowOnLines_eq {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ υ r t=
      (∏i,W i (((P i).val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold weightedRowOnLines continuedRowOnLines continuedPhysicalRowKernel calibratedTupleValue
  simp only [hnorm,Finset.prod_mul_distrib]
  ring

section

variable {K : ℕ}
  (e σ υ r : ℝ)
  (he : 0<e)
  (he' : e<1/1000)
  (hσ : (7/8:ℝ)≤σ)
  (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
  (hσ3 : σ≤3)
  (hυ : (1/2:ℝ)≤υ)
  (hυ3 : υ≤3)
  (hr : (17/50:ℝ)≤ r)
  (S : Finset (Ideal O))
  (hS : SourceExclusions S)
  (hmax : ∀P∈S,P.IsMaximal)
  (hfirst : FirstTail (1/4) S)
  (η : Character)
  (R : Finset FreeRow)
  (hR : ∀u∈R,u.val≠1)
  (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
  (hT : ∀i P,P∈T i→P.val∉S)
  (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
  (W : Fin K→ℝ→ℂ)
  (Yp : Fin K→ℝ)
  (W0 W1 : SchwartzMap ℝ ℂ)
  (a0 b0 a1 b1 : ℝ)
  (ha0 : 0<a0)
  (ha1 : 0<a1)
  (hW0 : Function.support W0⊆Icc a0 b0)
  (hW1 : Function.support W1⊆Icc a1 b1)
  (X Y Z : ℝ)
  (hX : 0<X)
  (hY : 0<Y)
  (hZ : 0<Z)

end

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.FirstIntegral
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set Complex

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

local notation "O" => HeckeFamily.O

lemma continuedRowOnLines_eq_amplitude {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t=
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
        rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t := by
  unfold continuedRowOnLines continuedPhysicalRowKernel rowAmplitudeOnLines
  ring

lemma rowAmplitudeOnLines_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (σ υ r : ℝ) : Measurable (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r) := by
  have hp (i : Fin K) : 0<elementNorm (CompletedGauss.primaryGenerator (P i).val) :=
    elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  have hN : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hphys := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun t : HeightSpace=>(σ:ℂ)+t.1.1*I) (fun t : HeightSpace=>(υ:ℂ)+t.2*I)
    (fun t : HeightSpace=>(r:ℂ)+t.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rowAmplitudeOnLines
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro i hi
      exact measurable_const_cpow _ (Complex.ofReal_ne_zero.mpr (hp i).ne') _ (by fun_prop)
    · unfold frequencyWeight
      exact measurable_const_cpow _ hN _ (by fun_prop)
  · exact hphys.const_mul _

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set Complex

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem continuedPhysicalRowKernel_buffered_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)
      {t : HeightSpace | |t.1.1|≤H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_buffered_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ r hσ hσ2 hr
  have hb (t : HeightSpace) : ‖A t‖≤C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r (1-a-6*e) (1-a-6*e) (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r (1-a-6*e) (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=>by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set Complex

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem cubeWeightedRow_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H) heightMeasure := by
  have hi := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  have hE : MeasurableSet E := ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  apply (integrable_indicator_iff hE).mpr
  have heq : weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)=
      fun t=>(∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) t := by
    funext t
    exact weightedRowOnLines_eq ..
  rw [heq]
  exact (hi.mono_set (fun t ht=>ht.1.1)).const_mul _

lemma cubeWeightedRow_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H t ∂heightMeasure)=
      (∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H := by
  have hE : MeasurableSet {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H} :=
    ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  unfold cubeWeightedRow
  rw [integral_indicator hE]
  simp_rw [weightedRowOnLines_eq]
  rw [integral_const_mul]
  unfold centralCubeIntegral
  ring

theorem finiteCentralCubeRows_eq_integral {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
      detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      cubeWeightedRow S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z (a u) e (H u) t
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  let f (u : FreeRow) (P : ∀i,T i) := cubeWeightedRow S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z (a u) e (H u)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    rcases hbin u hu with ⟨ha,ha',hB,hH,hzero⟩
    exact cubeWeightedRow_integrable e (a u) (B u) (H u) (idx u) he he' ha ha' hB hH
      S hS hmax hfirst _ _ η u (hR u hu) (ψ u) hzero W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P _=>hi u hu P)
  refine ⟨integrable_finsetSum _ hiu,?_⟩
  change finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu,Finset.mul_sum]
  unfold finiteCentralCubeRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>hi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact (cubeWeightedRow_integral S hS hmax _ _ η u W Yp W0 W1 X Y Z (a u) e (H u)).symm

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open MeasureTheory Set Filter Asymptotics Complex

namespace SevenEighths.PrincipalSignalComparison

open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

open ProbePhysical ActualEisensteinCubic CompletedGauss

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open MeasureTheory Set Filter Asymptotics Complex

namespace SevenEighths.PrincipalSignalComparison

open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

open ProbePhysical ActualEisensteinCubic CompletedGauss

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open MeasureTheory Set Filter Asymptotics Complex

namespace SevenEighths.PrincipalSignalComparison

open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

open ProbePhysical ActualEisensteinCubic CompletedGauss

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open MeasureTheory Set Filter Asymptotics Complex

namespace SevenEighths.PrincipalSignalComparison

open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

open ProbePhysical ActualEisensteinCubic CompletedGauss

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison

end

end OAI

end

section

-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison (continued)

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open MeasureTheory Set Filter Asymptotics Complex

namespace SevenEighths.PrincipalSignalComparison

open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

private instance : IsPrincipalIdealRing HeckeFamily.O := IsCyclotomicExtension.Rat.three_pid K

open ProbePhysical ActualEisensteinCubic CompletedGauss

def annularPrimeWeight (W : ℝ → ℝ) (scale : ℝ) (P : PrimeIdeal) : ℝ :=
  W ((Ideal.absNorm P.val : ℝ)/scale) * (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ))

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
namespace OAI

noncomputable section

open scoped Classical BigOperators

open Filter

namespace SevenEighths.HeckeDetectorClassBudget

open HeckeDetectorFiberPartition HeckeDetectorWitnessRows

theorem labels_card_le (cap mesh : ℝ) (hcap : cap≤1/2) (hm : 0< mesh) :
    (HeckePrimeAmplitudeBins.labels cap mesh).card≤alphabetBound mesh := by
  have hceil : ⌈cap/mesh⌉≤⌈(1/2 : ℝ)/mesh⌉ :=
    Int.ceil_mono (div_le_div_of_nonneg_right hcap hm.le)
  have hsub : Finset.Icc (0 : ℤ) ⌈cap/mesh⌉ ⊆ Finset.Icc (0 : ℤ) ⌈(1/2 : ℝ)/mesh⌉ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hceil⟩
  have h1 := Finset.card_insert_le (0 : ℝ)
    (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))
  have h2 := Finset.card_insert_le cap
    ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ)))
  have h3 := Finset.card_image_le (s:=Finset.Icc (0 : ℤ) ⌈cap/mesh⌉)
    (f:=fun n : ℤ => mesh*(n : ℝ))
  have h4 := Finset.card_le_card hsub
  simp only [Int.card_Icc,sub_zero] at h4 h3
  unfold HeckePrimeAmplitudeBins.labels alphabetBound
  omega

theorem bin_card_le {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (hcap : cap≤1/2) (hm : 0< mesh) :
    Fintype.card (BinLabel slots cap mesh)≤(alphabetBound mesh)^slots.card := by
  simpa only [BinLabel,Fintype.card_fun,Fintype.card_coe] using
    Nat.pow_le_pow_left (labels_card_le cap mesh hcap hm) slots.card

end SevenEighths.HeckeDetectorClassBudget

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeCommonProfile
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

local notation "O" => HeckeFamily.O

theorem cube_sum_eq_common_profile {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) (t : HeightSpace) :
    (∑u∈R,∑P:(∀i,T i),cubeWeightedRow S hS hmax (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z a e H t)=
    {v : HeightSpace | (|v.1.1|≤H ∧ |v.2|≤H) ∧ |v.1.2|≤H}.indicator
      (fun v=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+v.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+v.2*Complex.I)
        ((17/50:ℂ)+v.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e v) t := by
  by_cases ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H
  · simp [cubeWeightedRow,ht,weightedRowOnLines,cubeArithmeticSum,
      Finset.mul_sum,mul_assoc]
  · simp [cubeWeightedRow,ht]

theorem cube_common_profile_integral {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1' : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
      (fun t=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
        ((17/50:ℂ)+t.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  have hh := finiteCentralCubeRows_eq_integral e he he' S hS hmax hfirst η R hR T hT
    (fun _=>a) (fun _=>B) (fun _=>H) (fun _=>i) ψ
    (fun u hu=>⟨ha,ha1,hB,hH,hbin u hu⟩) W Yp W0 W1 a0 b0 a1 b1 ha0 ha1' hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh ⊢
  simpa only [cube_sum_eq_common_profile] using hh

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
namespace OAI

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

local notation "O" => HeckeFamily.O

theorem actual_common_cube_aggregate_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : ℝ,0≤A →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H →
        ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤A) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          A := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := A
  have hm : 0≤ mass := hA
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤ scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤ scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralClassPartition
namespace OAI

noncomputable section

open scoped Classical BigOperators

namespace SevenEighths.ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

lemma sum_amplitudeRows {Slot : Type*} (rows : Finset FreeRow) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (f : FreeRow→ℂ) :
    (∑u∈rows,f u)=∑bin : BinLabel slots cap mesh,
      ∑u∈amplitudeRows rows slots U cap mesh hm widths Q bin,f u := by
  have hmap : ∀u∈rows,amplitudeLabel slots U cap mesh hm widths Q u∈
      (Finset.univ : Finset (BinLabel slots cap mesh)) := by simp
  exact (Finset.sum_fiberwise_of_maps_to hmap f).symm

lemma cubeArithmeticSum_amplitude_partition {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0< mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) :
    cubeArithmeticSum S hS hmax η rows T hT W Yp a e t=
      ∑bin : BinLabel slots cap mesh,cubeArithmeticSum S hS hmax η
        (amplitudeRows rows slots U cap mesh hm widths Q bin) T hT W Yp a e t := by
  unfold cubeArithmeticSum
  exact sum_amplitudeRows rows slots U cap mesh hm widths Q _

theorem cubeArithmeticSum_class_uniform {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0< mesh) (hcap : cap≤1/2) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (A : ℝ) (hA : 0≤A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty →
      ‖cubeArithmeticSum S hS hmax η (amplitudeRows rows slots U cap mesh hm widths Q bin)
        T hT W Yp a e t‖≤A) :
    ‖cubeArithmeticSum S hS hmax η rows T hT W Yp a e t‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [cubeArithmeticSum_amplitude_partition S hS hmax η rows T hT W Yp a e t slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,cubeArithmeticSum,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

section
-- module Transport.TunedCandidate (LW56e2)
namespace RH.Transport.TunedCandidate

open RH.Transport.LocalBounds

noncomputable section

theorem zeta_pos : 0 < zeta := by norm_num [zeta]

theorem sideMargin_eq_value (term : SideCondition) :
    sideMargin term = sideMarginValue term := by
  cases term <;>
    norm_num [sideMargin, sideMarginValue, intermediateExponent, ell,
      Geometry.ell, lx, ly, h, lxAt, lyAt, hAt, b,
      B, boundaryAt, goodTailDecay, p, zeta]

theorem all_side_margins_pos (term : SideCondition) : 0 < sideMargin term := by
  rw [sideMargin_eq_value]
  cases term <;> norm_num [sideMarginValue]

theorem buffered_upper_scale_lt_one : h + zeta < 1 := by
  have hm := all_side_margins_pos SideCondition.bufferedUpperScale
  dsimp [sideMargin] at hm
  linarith

end

end RH.Transport.TunedCandidate

end

section
-- module Transport.PhysicalTail.TailScales (LW56e2)
namespace RH.Transport.PhysicalTail

noncomputable section

open scoped BigOperators

open OAI OAI.SevenEighths ProbeHighRowFamily

def largeBase : ℝ := 1+TunedCandidate.lx/2+TunedCandidate.ly

end

end RH.Transport.PhysicalTail

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

end

end RH.Transport.PhysicalAnalytic.Contours

end

section
-- module Transport.PhysicalAnalytic.ContourTransport (LW56e2)
namespace RH.Transport.PhysicalAnalytic.ContourTransport

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

open OAI OAI.SevenEighths

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours 

local notation "Id" => Ideal ActualEisensteinCubic.O

abbrev transportBoundary : ℝ := Geometry.boundary TunedCandidate.p

end

end RH.Transport.PhysicalAnalytic.ContourTransport

end

section
-- module Transport.PhysicalAnalytic.RemainderBounds (LW56e2)
namespace RH.Transport.PhysicalAnalytic.RemainderBounds

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

open OAI OAI.SevenEighths

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours

local notation "Id" => Ideal ActualEisensteinCubic.O

abbrev transportBoundary : ℝ := Geometry.boundary TunedCandidate.p

abbrev transportShift : ℝ := -2 / 3 - TunedCandidate.b / 6

section Pointwise

variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0< P j) (hthreshold : ∀j∈J,480≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) (T : ι→Finset PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
  (ha : transportBoundary≤ a) (hυ : 19/20≤ υ) (hzlo : 33/200≤ ξ) (hC : 0≤ C)
  (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

end Pointwise

section Uniform

variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (transportBoundary:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)

include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

end Uniform

end

end RH.Transport.PhysicalAnalytic.RemainderBounds

end

section
-- module Transport.PhysicalAnalytic.HeckeShift (LW56e2)
namespace RH.Transport.PhysicalAnalytic.HeckeShift

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex

open scoped Topology

open OAI OAI.SevenEighths

open HeckeFamily HeckeSignal Continuation

abbrev transportBoundary : ℝ := Geometry.boundary TunedCandidate.p

end

end RH.Transport.PhysicalAnalytic.HeckeShift

end

section
-- module Transport.PhysicalAnalytic.SignalComparison (LW56e2)
namespace RH.Transport.PhysicalAnalytic.SignalComparison

noncomputable section

open scoped Classical BigOperators Topology

open MeasureTheory Set Filter Asymptotics Complex

open OAI OAI.SevenEighths

open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

open PrincipalSignalComparison PrincipalMellinResidues ProbePhysical CompletedGauss

variable {κ ι : Type*}

abbrev transportBoundary : ℝ := Geometry.boundary TunedCandidate.p

end

end RH.Transport.PhysicalAnalytic.SignalComparison

end

section
-- module Transport.Endpoint (LW56e2)
namespace RH.Transport.Endpoint

noncomputable section

def perturbation : ℝ := 68479 / 400000000

def boundary : ℝ := 7 / 8 - perturbation / 4

def ell : ℝ := 1 / 6 + perturbation

def ly : ℝ := 23 / 48 - perturbation / 2

def h : ℝ := 13 / 16 + 3 * perturbation / 2

def countDenominator (δ x : ℝ) : ℝ :=
  (5 / 6 - δ) * (3 - 17 * x / 9) + δ * ((2 - 8 * x / 9) * (1 - x))

def adaptiveCount (δ x : ℝ) : ℝ :=
  1 - δ + (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) /
    (2 * countDenominator δ x)

/-- The full high exponent E_B(h), with a=(1+δ)/2 and q=δ*x. -/
def endpointExponent (δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - boundary + h * (17 / 50 - 1 / 6) -
    ((1 + δ) / 2) * ly - ell / 2 + δ * x * ell +
    h * (adaptiveCount δ x + δ / 2 - 17 / 50)

theorem countDenominator_pos {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (_hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) : 0 < countDenominator δ x := by
  have hd : 0 < δ := by linarith
  have ha : 0 < (5 / 6 : ℝ) - δ := by linarith
  have hD : 0 < (3 : ℝ) - 17 * x / 9 := by linarith
  have hP : 0 < ((2 : ℝ) - 8 * x / 9) * (1 - x) :=
    mul_pos (by linarith) (by linarith)
  exact add_pos (mul_pos ha hD) (mul_pos hd hP)

def screenUpper : ℝ := 171197539 / 1000000000000

end

end RH.Transport.Endpoint

end

section
-- module Transport.TunedEndpoint (LW56e2)
namespace RH.Transport.TunedEndpoint

noncomputable section

def perturbation : ℝ := 214651 / 1250000000

def b : ℝ := 192821 / 1562500

def boundary : ℝ := 7 / 8 - perturbation / 4

def ell : ℝ := 1 / 6 + perturbation

def ly : ℝ := (1 - ell + b) / 2

def h : ℝ := (1 + 3 * ell + b) / 2

def saving : ℝ := 1 / 1000000000000

abbrev countDenominator := Endpoint.countDenominator

abbrev adaptiveCount := Endpoint.adaptiveCount

/-- The full high exponent E_B(h), with a=(1+δ)/2 and q=δ*x. -/
def endpointExponent (δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - boundary + h * (17 / 50 - 1 / 6) -
    ((1 + δ) / 2) * ly - ell / 2 + δ * x * ell +
    h * (adaptiveCount δ x + δ / 2 - 17 / 50)

def certificatePolynomial (δ x : ℝ) : ℝ :=
  ((62653326997 : ℝ) / 1200000000000) +
    ((-1065106558949 : ℝ) / 32400000000000) * x +
    ((-1004139726997 : ℝ) / 3000000000000) * δ +
    ((25186672075081 : ℝ) / 81000000000000) * δ * x +
    ((-197904348259 : ℝ) / 10125000000000) * δ * x ^ 2 +
    ((2500643953 : ℝ) / 3750000000) * δ ^ 2 +
    ((-2590008913 : ℝ) / 2250000000) * δ ^ 2 * x +
    ((22163857507 : ℝ) / 33750000000) * δ ^ 2 * x ^ 2 +
    ((-625643953 : ℝ) / 4218750000) * δ ^ 2 * x ^ 3

theorem countDenominator_pos {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (_hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) : 0 < countDenominator δ x := by
  exact Endpoint.countDenominator_pos hdlo hdhi _hxlo hxhi

theorem certificate_identity (δ x : ℝ) (hJ : countDenominator δ x ≠ 0) :
    certificatePolynomial δ x =
      (-endpointExponent δ x - saving) * countDenominator δ x := by
  unfold certificatePolynomial endpointExponent boundary ly h saving
  unfold ell perturbation b
  simp only [adaptiveCount, Endpoint.adaptiveCount]
  field_simp
  unfold countDenominator Endpoint.countDenominator at *
  field_simp at *
  ring

private theorem rectangle_0 {δ x : ℝ}
    (hdlo : ((227 : ℝ) / 400) ≤ δ) (hdhi : δ ≤ ((3 : ℝ) / 4))
    (hxlo : ((1 : ℝ) / 4) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((227 : ℝ) / 400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((3 : ℝ) / 4) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((1 : ℝ) / 4) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (134890312500000 : ℝ) * certificatePolynomial δ x =
      (8298542053865809 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (16090055349606749 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (9950733099257042 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (1965786959991280 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 +
      (26814254216446698 : ℝ) * (δ - ((227 : ℝ) / 400)) * (((3 : ℝ) / 4) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (54976541176857124 : ℝ) * (δ - ((227 : ℝ) / 400)) * (((3 : ℝ) / 4) - δ) * (x - ((1 : ℝ) / 4)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (36615460800429582 : ℝ) * (δ - ((227 : ℝ) / 400)) * (((3 : ℝ) / 4) - δ) * (x - ((1 : ℝ) / 4)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (7941897601627556 : ℝ) * (δ - ((227 : ℝ) / 400)) * (((3 : ℝ) / 4) - δ) * (x - ((1 : ℝ) / 4)) ^ 3 +
      (22122455525496200 : ℝ) * (δ - ((227 : ℝ) / 400)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (47870981727137600 : ℝ) * (δ - ((227 : ℝ) / 400)) ^ 2 * (x - ((1 : ℝ) / 4)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (34107809982905800 : ℝ) * (δ - ((227 : ℝ) / 400)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (8021436046644400 : ℝ) * (δ - ((227 : ℝ) / 400)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (134890312500000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (134890312500000 : ℝ))).mp hnonneg

private theorem rectangle_1 {δ x : ℝ}
    (hdlo : ((381 : ℝ) / 800) ≤ δ) (hdhi : δ ≤ ((227 : ℝ) / 400))
    (hxlo : ((3 : ℝ) / 8) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((381 : ℝ) / 800) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((227 : ℝ) / 400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((3 : ℝ) / 8) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (29912139530294520 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (61051384937937589 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (38963006239960376 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (7551303526733008 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 +
      (91482550980964320 : ℝ) * (δ - ((381 : ℝ) / 800)) * (((227 : ℝ) / 400) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (198600277971938164 : ℝ) * (δ - ((381 : ℝ) / 800)) * (((227 : ℝ) / 400) - δ) * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (138589641080292168 : ℝ) * (δ - ((381 : ℝ) / 800)) * (((227 : ℝ) / 400) - δ) * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (30822593266560992 : ℝ) * (δ - ((381 : ℝ) / 800)) * (((227 : ℝ) / 400) - δ) * (x - ((3 : ℝ) / 8)) ^ 3 +
      (72610234925441760 : ℝ) * (δ - ((381 : ℝ) / 800)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (167555529712378692 : ℝ) * (δ - ((381 : ℝ) / 800)) ^ 2 * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (126784751833847056 : ℝ) * (δ - ((381 : ℝ) / 800)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (31452591359860480 : ℝ) * (δ - ((381 : ℝ) / 800)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_2 {δ x : ℝ}
    (hdlo : ((689 : ℝ) / 1600) ≤ δ) (hdhi : δ ≤ ((381 : ℝ) / 800))
    (hxlo : ((7 : ℝ) / 16) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((689 : ℝ) / 1600) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((381 : ℝ) / 800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((7 : ℝ) / 16) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (257218426046590493 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (530845119291108202 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (x - ((7 : ℝ) / 16)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (330090058619750656 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (55572346406196608 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 3 +
      (730743884219594628 : ℝ) * (δ - ((689 : ℝ) / 1600)) * (((381 : ℝ) / 800) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (1606162032224554856 : ℝ) * (δ - ((689 : ℝ) / 1600)) * (((381 : ℝ) / 800) - δ) * (x - ((7 : ℝ) / 16)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (1109152640327850048 : ℝ) * (δ - ((689 : ℝ) / 1600)) * (((381 : ℝ) / 800) - δ) * (x - ((7 : ℝ) / 16)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (231763646301392896 : ℝ) * (δ - ((689 : ℝ) / 1600)) * (((381 : ℝ) / 800) - δ) * (x - ((7 : ℝ) / 16)) ^ 3 +
      (549911336939701972 : ℝ) * (δ - ((689 : ℝ) / 1600)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (1293050463984458920 : ℝ) * (δ - ((689 : ℝ) / 1600)) ^ 2 * (x - ((7 : ℝ) / 16)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (985870669122550400 : ℝ) * (δ - ((689 : ℝ) / 1600)) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (241641712855456256 : ℝ) * (δ - ((689 : ℝ) / 1600)) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_3 {δ x : ℝ}
    (hdlo : ((261 : ℝ) / 640) ≤ δ) (hdhi : δ ≤ ((689 : ℝ) / 1600))
    (hxlo : ((15 : ℝ) / 32) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((261 : ℝ) / 640) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((689 : ℝ) / 1600) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((15 : ℝ) / 32) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (2600541126954803895 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (5300245334370843220 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (x - ((15 : ℝ) / 32)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (3074915802151589120 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (372015132856376320 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 3 +
      (6729066998216966652 : ℝ) * (δ - ((261 : ℝ) / 640)) * (((689 : ℝ) / 1600) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (14506781610843049552 : ℝ) * (δ - ((261 : ℝ) / 640)) * (((689 : ℝ) / 1600) - δ) * (x - ((15 : ℝ) / 32)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (9411192062384113152 : ℝ) * (δ - ((261 : ℝ) / 640)) * (((689 : ℝ) / 1600) - δ) * (x - ((15 : ℝ) / 32)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (1626726914172588032 : ℝ) * (δ - ((261 : ℝ) / 640)) * (((689 : ℝ) / 1600) - δ) * (x - ((15 : ℝ) / 32)) ^ 3 +
      (4694903801454583836 : ℝ) * (δ - ((261 : ℝ) / 640)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (10861938205993594704 : ℝ) * (δ - ((261 : ℝ) / 640)) ^ 2 * (x - ((15 : ℝ) / 32)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (7948913565413447680 : ℝ) * (δ - ((261 : ℝ) / 640)) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (1778315084998291456 : ℝ) * (δ - ((261 : ℝ) / 640)) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_4 {δ x : ℝ}
    (hdlo : ((2537 : ℝ) / 6400) ≤ δ) (hdhi : δ ≤ ((261 : ℝ) / 640))
    (hxlo : ((31 : ℝ) / 64) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((2537 : ℝ) / 6400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((261 : ℝ) / 640) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((31 : ℝ) / 64) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (30592224468012278507 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (61123544385233196712 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (x - ((31 : ℝ) / 64)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (32513564848756612096 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (1970164305503313920 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 3 +
      (71625073584769915884 : ℝ) * (δ - ((2537 : ℝ) / 6400)) * (((261 : ℝ) / 640) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (148749550181319450272 : ℝ) * (δ - ((2537 : ℝ) / 6400)) * (((261 : ℝ) / 640) - δ) * (x - ((31 : ℝ) / 64)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (86835155195379449856 : ℝ) * (δ - ((2537 : ℝ) / 6400)) * (((261 : ℝ) / 640) - δ) * (x - ((31 : ℝ) / 64)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (9685822127450718208 : ℝ) * (δ - ((2537 : ℝ) / 6400)) * (((261 : ℝ) / 640) - δ) * (x - ((31 : ℝ) / 64)) ^ 3 +
      (45390869585334450220 : ℝ) * (δ - ((2537 : ℝ) / 6400)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (100528978697945203360 : ℝ) * (δ - ((2537 : ℝ) / 6400)) ^ 2 * (x - ((31 : ℝ) / 64)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (67055379211531489280 : ℝ) * (δ - ((2537 : ℝ) / 6400)) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (11904484251404042240 : ℝ) * (δ - ((2537 : ℝ) / 6400)) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_5 {δ x : ℝ}
    (hdlo : ((5001 : ℝ) / 12800) ≤ δ) (hdhi : δ ≤ ((2537 : ℝ) / 6400))
    (hxlo : ((63 : ℝ) / 128) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((5001 : ℝ) / 12800) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((2537 : ℝ) / 6400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((63 : ℝ) / 128) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (409988390547005193555 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (808943424010472117584 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (x - ((63 : ℝ) / 128)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (403629948479791149056 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (4627972948653703168 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 3 +
      (880602773912225746380 : ℝ) * (δ - ((5001 : ℝ) / 12800)) * (((2537 : ℝ) / 6400) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (1763558700164430685504 : ℝ) * (δ - ((5001 : ℝ) / 12800)) * (((2537 : ℝ) / 6400) - δ) * (x - ((63 : ℝ) / 128)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (917213800110941749248 : ℝ) * (δ - ((5001 : ℝ) / 12800)) * (((2537 : ℝ) / 6400) - δ) * (x - ((63 : ℝ) / 128)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (34162619289106644992 : ℝ) * (δ - ((5001 : ℝ) / 12800)) * (((2537 : ℝ) / 6400) - δ) * (x - ((63 : ℝ) / 128)) ^ 3 +
      (504797992030021604940 : ℝ) * (δ - ((5001 : ℝ) / 12800)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (1056489335994050901312 : ℝ) * (δ - ((5001 : ℝ) / 12800)) ^ 2 * (x - ((63 : ℝ) / 128)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (614784924244264861696 : ℝ) * (δ - ((5001 : ℝ) / 12800)) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (63045257776106045440 : ℝ) * (δ - ((5001 : ℝ) / 12800)) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_6 {δ x : ℝ}
    (hdlo : ((19931 : ℝ) / 51200) ≤ δ) (hdhi : δ ≤ ((5001 : ℝ) / 12800))
    (hxlo : ((255 : ℝ) / 512) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((19931 : ℝ) / 51200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((5001 : ℝ) / 12800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((255 : ℝ) / 512) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (99027670009870853320155 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (197572877383225701023552 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((255 : ℝ) / 512)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (99053568017705175023616 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (507615043002585579520 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 3 +
      (202383363555568183090248 : ℝ) * (δ - ((19931 : ℝ) / 51200)) * (((5001 : ℝ) / 12800) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (405880825974283670060544 : ℝ) * (δ - ((19931 : ℝ) / 51200)) * (((5001 : ℝ) / 12800) - δ) * (x - ((255 : ℝ) / 512)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (206600939293685966176256 : ℝ) * (δ - ((19931 : ℝ) / 51200)) * (((5001 : ℝ) / 12800) - δ) * (x - ((255 : ℝ) / 512)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (3101980210542178992128 : ℝ) * (δ - ((19931 : ℝ) / 51200)) * (((5001 : ℝ) / 12800) - δ) * (x - ((255 : ℝ) / 512)) ^ 3 +
      (105511095496163069973552 : ℝ) * (δ - ((19931 : ℝ) / 51200)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (214763416608183615837184 : ℝ) * (δ - ((19931 : ℝ) / 51200)) ^ 2 * (x - ((255 : ℝ) / 512)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (113992116484524666257408 : ℝ) * (δ - ((19931 : ℝ) / 51200)) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (4739044299421392044032 : ℝ) * (δ - ((19931 : ℝ) / 51200)) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_7 {δ x : ℝ}
    (hdlo : ((79651 : ℝ) / 204800) ≤ δ) (hdhi : δ ≤ ((19931 : ℝ) / 51200))
    (hxlo : ((1023 : ℝ) / 2048) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((79651 : ℝ) / 204800) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((19931 : ℝ) / 51200) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((1023 : ℝ) / 2048) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (25011096297733763447022315 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (50081871863030726977400064 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((1023 : ℝ) / 2048)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (25193636709675207041744896 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (122849236593608740569088 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 3 +
      (50424609775973646803433240 : ℝ) * (δ - ((79651 : ℝ) / 204800)) * (((19931 : ℝ) / 51200) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (101228143825347637091477504 : ℝ) * (δ - ((79651 : ℝ) / 204800)) * (((19931 : ℝ) / 51200) - δ) * (x - ((1023 : ℝ) / 2048)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (51308945462958008018403328 : ℝ) * (δ - ((79651 : ℝ) / 204800)) * (((19931 : ℝ) / 51200) - δ) * (x - ((1023 : ℝ) / 2048)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (505387576187821261586432 : ℝ) * (δ - ((79651 : ℝ) / 204800)) * (((19931 : ℝ) / 51200) - δ) * (x - ((1023 : ℝ) / 2048)) ^ 3 +
      (25550944327679429476006320 : ℝ) * (δ - ((79651 : ℝ) / 204800)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (51558393065633699955986432 : ℝ) * (δ - ((79651 : ℝ) / 204800)) ^ 2 * (x - ((1023 : ℝ) / 2048)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (26527258471610481981259776 : ℝ) * (δ - ((79651 : ℝ) / 204800)) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (519797804034647633428480 : ℝ) * (δ - ((79651 : ℝ) / 204800)) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_8 {δ x : ℝ}
    (hdlo : ((159229 : ℝ) / 409600) ≤ δ) (hdhi : δ ≤ ((79651 : ℝ) / 204800))
    (hxlo : ((2047 : ℝ) / 4096) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((159229 : ℝ) / 409600) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((79651 : ℝ) / 204800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((2047 : ℝ) / 4096) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (397440220710856675382606763 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (795249895821869923246070272 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (x - ((2047 : ℝ) / 4096)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (398683948337017235372507136 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (874225638509300110327808 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 3 +
      (797979276003465448131035348 : ℝ) * (δ - ((159229 : ℝ) / 409600)) * (((79651 : ℝ) / 204800) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (1598655841892578747130157056 : ℝ) * (δ - ((159229 : ℝ) / 409600)) * (((79651 : ℝ) / 204800) - δ) * (x - ((2047 : ℝ) / 4096)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (804383986601717822220402688 : ℝ) * (δ - ((159229 : ℝ) / 409600)) * (((79651 : ℝ) / 204800) - δ) * (x - ((2047 : ℝ) / 4096)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (3707325493981298909249536 : ℝ) * (δ - ((159229 : ℝ) / 409600)) * (((79651 : ℝ) / 204800) - δ) * (x - ((2047 : ℝ) / 4096)) ^ 3 +
      (401637816428133224826945452 : ℝ) * (δ - ((159229 : ℝ) / 409600)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (806701543937295738260776960 : ℝ) * (δ - ((159229 : ℝ) / 409600)) ^ 2 * (x - ((2047 : ℝ) / 4096)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (408994950711296532215234560 : ℝ) * (δ - ((159229 : ℝ) / 409600)) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (3931175570995479698210816 : ℝ) * (δ - ((159229 : ℝ) / 409600)) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_9 {δ x : ℝ}
    (hdlo : ((63677 : ℝ) / 163840) ≤ δ) (hdhi : δ ≤ ((159229 : ℝ) / 409600))
    (hxlo : ((4095 : ℝ) / 8192) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((63677 : ℝ) / 163840) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((159229 : ℝ) / 409600) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((4095 : ℝ) / 8192) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (6337320811246769232832241715 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (12676023644083782051576714240 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (x - ((4095 : ℝ) / 8192)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (6344120861784816143187312640 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (5417838685082271707299840 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 3 +
      (12697526626115550976556454492 : ℝ) * (δ - ((63677 : ℝ) / 163840)) * (((159229 : ℝ) / 409600) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (25411588099562541910534787072 : ℝ) * (δ - ((63677 : ℝ) / 163840)) * (((159229 : ℝ) / 409600) - δ) * (x - ((4095 : ℝ) / 8192)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (12738670307452872762182336512 : ℝ) * (δ - ((63677 : ℝ) / 163840)) * (((159229 : ℝ) / 409600) - δ) * (x - ((4095 : ℝ) / 8192)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (24608453393192028043476992 : ℝ) * (δ - ((63677 : ℝ) / 163840)) * (((159229 : ℝ) / 409600) - δ) * (x - ((4095 : ℝ) / 8192)) ^ 3 +
      (6368993162033012536446047916 : ℝ) * (δ - ((63677 : ℝ) / 163840)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (12761923755291458354576543744 : ℝ) * (δ - ((63677 : ℝ) / 163840)) ^ 2 * (x - ((4095 : ℝ) / 8192)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (6420906004040722171255848960 : ℝ) * (δ - ((63677 : ℝ) / 163840)) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (27975220432297603530489856 : ℝ) * (δ - ((63677 : ℝ) / 163840)) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_10 {δ x : ℝ}
    (hdlo : ((636697 : ℝ) / 1638400) ≤ δ) (hdhi : δ ≤ ((63677 : ℝ) / 163840))
    (hxlo : ((8191 : ℝ) / 16384) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((636697 : ℝ) / 1638400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((63677 : ℝ) / 163840) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((8191 : ℝ) / 16384) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (101228566084429064927589881187 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (202448138308208310656498378752 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (x - ((8191 : ℝ) / 16384)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (101242856252003340270767702016 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (23283267347695718126059520 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 3 +
      (202609810896557081037008711084 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) * (((63677 : ℝ) / 163840) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (405281436910416413597638172672 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) * (((63677 : ℝ) / 163840) - δ) * (x - ((8191 : ℝ) / 16384)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (202798004795263431228340043776 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) * (((63677 : ℝ) / 163840) - δ) * (x - ((8191 : ℝ) / 16384)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (126377259476825635205152768 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) * (((63677 : ℝ) / 163840) - δ) * (x - ((8191 : ℝ) / 16384)) ^ 3 +
      (101451532623201798797214273740 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (203044151069669289224585912320 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) ^ 2 * (x - ((8191 : ℝ) / 16384)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (101765990045441007332947394560 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (173370837922632694633594880 : ℝ) * (δ - ((636697 : ℝ) / 1638400)) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_11 {δ x : ℝ}
    (hdlo : ((1273321 : ℝ) / 3276800) ≤ δ) (hdhi : δ ≤ ((636697 : ℝ) / 1638400))
    (hxlo : ((16383 : ℝ) / 32768) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((1273321 : ℝ) / 3276800) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((636697 : ℝ) / 1638400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((16383 : ℝ) / 32768) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (1618473750198989177711643127875 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (3236719628729041296532575965184 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (x - ((16383 : ℝ) / 32768)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (1618276189298180111365178392576 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (30307724971338017221378048 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 3 +
      (3237682867220433435879400097100 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) * (((636697 : ℝ) / 1638400) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (6475062501624698868618152198144 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) * (((636697 : ℝ) / 1638400) - δ) * (x - ((16383 : ℝ) / 32768)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (3237592798004677251335358251008 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) * (((636697 : ℝ) / 1638400) - δ) * (x - ((16383 : ℝ) / 32768)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (213157513749578776819269632 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) * (((636697 : ℝ) / 1638400) - δ) * (x - ((16383 : ℝ) / 32768)) ^ 3 +
      (1619771375647953646291928085900 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (3240029604914064626819295690752 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) ^ 2 * (x - ((16383 : ℝ) / 32768)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (1621003296864742838802334089216 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (745064555126262980033904640 : ℝ) * (δ - ((1273321 : ℝ) / 3276800)) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_12 {δ x : ℝ}
    (hdlo : ((5093211 : ℝ) / 13107200) ≤ δ) (hdhi : δ ≤ ((1273321 : ℝ) / 3276800))
    (hxlo : ((65535 : ℝ) / 131072) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((5093211 : ℝ) / 13107200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((1273321 : ℝ) / 3276800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((65535 : ℝ) / 131072) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (414262618786220927424324575330715 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (828536680975118512087150775713792 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((65535 : ℝ) / 131072)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (414302028324669051871892011483136 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (27966087082356449694208491520 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 3 +
      (828529622717726952119533345633608 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) * (((1273321 : ℝ) / 3276800) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (1657049219014391678532509012721664 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((65535 : ℝ) / 131072)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (828542615846451076791998481432576 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((65535 : ℝ) / 131072)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (23019452406733157220994777088 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((65535 : ℝ) / 131072)) ^ 3 +
      (414302986378303363136975260222512 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (828620484677910277836071905787904 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) ^ 2 * (x - ((65535 : ℝ) / 131072)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (414348533458668071301163723522048 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (31035110370650129634691121152 : ℝ) * (δ - ((5093211 : ℝ) / 13107200)) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_13 {δ x : ℝ}
    (hdlo : ((2546569 : ℝ) / 6553600) ≤ δ) (hdhi : δ ≤ ((5093211 : ℝ) / 13107200))
    (hxlo : ((65535 : ℝ) / 131072) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((2546569 : ℝ) / 6553600) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((5093211 : ℝ) / 13107200) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((65535 : ℝ) / 131072) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (414294216087733168595206870278156 : ℝ) * (((5093211 : ℝ) / 13107200) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (828668770549600969119656983199744 : ℝ) * (((5093211 : ℝ) / 13107200) - δ) ^ 2 * (x - ((65535 : ℝ) / 131072)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (414471415064442125204734806589440 : ℝ) * (((5093211 : ℝ) / 13107200) - δ) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (96860553886609613969535533056 : ℝ) * (((5093211 : ℝ) / 13107200) - δ) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 3 +
      (828520852427156757577764955689252 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((5093211 : ℝ) / 13107200) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (1657097504886082369816094090133504 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((5093211 : ℝ) / 13107200) - δ) * (x - ((65535 : ℝ) / 131072)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (828665497452225130695569564499968 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((5093211 : ℝ) / 13107200) - δ) * (x - ((65535 : ℝ) / 131072)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (88844895922692641555839188992 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((5093211 : ℝ) / 13107200) - δ) * (x - ((65535 : ℝ) / 131072)) ^ 3 +
      (414262618786220927424324575330715 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (828536680975118512087150775713792 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (x - ((65535 : ℝ) / 131072)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (414302028324669051871892011483136 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (27966087082356449694208491520 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (x - ((65535 : ℝ) / 131072)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_14 {δ x : ℝ}
    (hdlo : ((2546569 : ℝ) / 6553600) ≤ δ) (hdhi : δ ≤ ((1273321 : ℝ) / 3276800))
    (hxlo : ((32767 : ℝ) / 65536) ≤ x) (hxhi : x ≤ ((65535 : ℝ) / 131072)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((2546569 : ℝ) / 6553600) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((1273321 : ℝ) / 3276800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((32767 : ℝ) / 65536) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((65535 : ℝ) / 131072) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (207131154019614778269631776768024 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (((65535 : ℝ) / 131072) - x) ^ 3 +
      (517831731479709067967147329282084 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((32767 : ℝ) / 65536)) * (((65535 : ℝ) / 131072) - x) ^ 2 +
      (414274131494199510612896059617298 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 2 * (((65535 : ℝ) / 131072) - x) +
      (103573554021933292148801717569539 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 3 +
      (414247166901496518514399733859424 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((1273321 : ℝ) / 3276800) - δ) * (((65535 : ℝ) / 131072) - x) ^ 3 +
      (1035599390557470235247891677554320 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((32767 : ℝ) / 65536)) * (((65535 : ℝ) / 131072) - x) ^ 2 +
      (828465541850030066599455702766408 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((32767 : ℝ) / 65536)) ^ 2 * (((65535 : ℝ) / 131072) - x) +
      (207113318169711794491279042705548 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((32767 : ℝ) / 65536)) ^ 3 +
      (207151996030437821556051803637856 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (((65535 : ℝ) / 131072) - x) ^ 3 +
      (517875607821666829400144805760144 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (x - ((32767 : ℝ) / 65536)) * (((65535 : ℝ) / 131072) - x) ^ 2 +
      (414299358397977475246444913886792 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 2 * (((65535 : ℝ) / 131072) - x) +
      (103575746594575840784243815055628 : ℝ) * (δ - ((2546569 : ℝ) / 6553600)) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_15 {δ x : ℝ}
    (hdlo : ((39789 : ℝ) / 102400) ≤ δ) (hdhi : δ ≤ ((2546569 : ℝ) / 6553600))
    (hxlo : ((32767 : ℝ) / 65536) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((39789 : ℝ) / 102400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((2546569 : ℝ) / 6553600) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((32767 : ℝ) / 65536) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (25897784788237987200722430373888 : ℝ) * (((2546569 : ℝ) / 6553600) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (51807583791676696091070400823296 : ℝ) * (((2546569 : ℝ) / 6553600) - δ) ^ 2 * (x - ((32767 : ℝ) / 65536)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (25923878389290338465250780643328 : ℝ) * (((2546569 : ℝ) / 6553600) - δ) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (14079373680398639848988082176 : ℝ) * (((2546569 : ℝ) / 6553600) - δ) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 3 +
      (51784681147120324320515921651584 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((2546569 : ℝ) / 6553600) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (103577840398980536193626644938752 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((2546569 : ℝ) / 6553600) - δ) * (x - ((32767 : ℝ) / 65536)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (51805767824061942577263213019136 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((2546569 : ℝ) / 6553600) - δ) * (x - ((32767 : ℝ) / 65536)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (12608547858571012522047963136 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((2546569 : ℝ) / 6553600) - δ) * (x - ((32767 : ℝ) / 65536)) ^ 3 +
      (25891394252451847283703972096003 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (51783750112571725140674916032512 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((32767 : ℝ) / 65536)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (25895382764600763173986281455616 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (3026892308956550436547985408 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((32767 : ℝ) / 65536)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_16 {δ x : ℝ}
    (hdlo : ((39789 : ℝ) / 102400) ≤ δ) (hdhi : δ ≤ ((1273321 : ℝ) / 3276800))
    (hxlo : ((16383 : ℝ) / 32768) ≤ x) (hxhi : x ≤ ((32767 : ℝ) / 65536)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((39789 : ℝ) / 102400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((1273321 : ℝ) / 3276800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((16383 : ℝ) / 32768) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((32767 : ℝ) / 65536) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (12946405136024347883037603225600 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (((32767 : ℝ) / 65536) - x) ^ 3 +
      (32366740170359850127409585459200 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((16383 : ℝ) / 32768)) * (((32767 : ℝ) / 65536) - x) ^ 2 +
      (25894781234437806778316045355008 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 2 * (((32767 : ℝ) / 65536) - x) +
      (6474446197059496800180607593472 : ℝ) * (((1273321 : ℝ) / 3276800) - δ) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 3 +
      (25889697068604186199737379315200 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((1273321 : ℝ) / 3276800) - δ) * (((32767 : ℝ) / 65536) - x) ^ 3 +
      (64721809656072144569654675623168 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((16383 : ℝ) / 32768)) * (((32767 : ℝ) / 65536) - x) ^ 2 +
      (51775560772995091308102351775360 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((16383 : ℝ) / 32768)) ^ 2 * (((32767 : ℝ) / 65536) - x) +
      (12943448179441168559896745638848 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((1273321 : ℝ) / 3276800) - δ) * (x - ((16383 : ℝ) / 32768)) ^ 3 +
      (12947790001591913421693145023000 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (((32767 : ℝ) / 65536) - x) ^ 3 +
      (32368563517304035318670021395236 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((16383 : ℝ) / 32768)) * (((32767 : ℝ) / 65536) - x) ^ 2 +
      (25894273394706460475130519413138 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 2 * (((32767 : ℝ) / 65536) - x) +
      (6473499875951181923626618863683 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((16383 : ℝ) / 32768)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_17 {δ x : ℝ}
    (hdlo : ((39789 : ℝ) / 102400) ≤ δ) (hdhi : δ ≤ ((636697 : ℝ) / 1638400))
    (hxlo : ((8191 : ℝ) / 16384) ≤ x) (hxhi : x ≤ ((16383 : ℝ) / 32768)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((39789 : ℝ) / 102400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((636697 : ℝ) / 1638400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((8191 : ℝ) / 16384) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((16383 : ℝ) / 32768) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (809169401342431171468451010560 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (((16383 : ℝ) / 32768) - x) ^ 3 +
      (2022849423940325575823888843776 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (x - ((8191 : ℝ) / 16384)) * (((16383 : ℝ) / 32768) - x) ^ 2 +
      (1618255183859357209141226816000 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 2 * (((16383 : ℝ) / 32768) - x) +
      (404575160500760871344925100800 : ℝ) * (((636697 : ℝ) / 1638400) - δ) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 3 +
      (1618435627529273429386806509312 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((636697 : ℝ) / 1638400) - δ) * (((16383 : ℝ) / 32768) - x) ^ 3 +
      (4045697906583577460193631133312 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((636697 : ℝ) / 1638400) - δ) * (x - ((8191 : ℝ) / 16384)) * (((16383 : ℝ) / 32768) - x) ^ 2 +
      (3236218026362122247862987779904 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((636697 : ℝ) / 1638400) - δ) * (x - ((8191 : ℝ) / 16384)) ^ 2 * (((16383 : ℝ) / 32768) - x) +
      (808955745786239894793736005600 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((636697 : ℝ) / 1638400) - δ) * (x - ((8191 : ℝ) / 16384)) ^ 3 +
      (809828528675432519420719049496 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (((16383 : ℝ) / 32768) - x) ^ 3 +
      (2024535346245982021757072089252 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((8191 : ℝ) / 16384)) * (((16383 : ℝ) / 32768) - x) ^ 2 +
      (1619649662243414312733068206162 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 2 * (((16383 : ℝ) / 32768) - x) +
      (404942843911988411572982021475 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((8191 : ℝ) / 16384)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_18 {δ x : ℝ}
    (hdlo : ((39789 : ℝ) / 102400) ≤ δ) (hdhi : δ ≤ ((63677 : ℝ) / 163840))
    (hxlo : ((4095 : ℝ) / 8192) ≤ x) (hxhi : x ≤ ((8191 : ℝ) / 16384)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((39789 : ℝ) / 102400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((63677 : ℝ) / 163840) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((4095 : ℝ) / 8192) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((8191 : ℝ) / 16384) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (50585785238311900117296846336 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (((8191 : ℝ) / 16384) - x) ^ 3 +
      (126450046387473861135200575744 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (x - ((4095 : ℝ) / 8192)) * (((8191 : ℝ) / 16384) - x) ^ 2 +
      (101150805131288418486508793984 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 2 * (((8191 : ℝ) / 16384) - x) +
      (25286543791950974108389094080 : ℝ) * (((63677 : ℝ) / 163840) - δ) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 3 +
      (101214052950972207638180098944 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((63677 : ℝ) / 163840) - δ) * (((8191 : ℝ) / 16384) - x) ^ 3 +
      (252991105333548656640358427968 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((63677 : ℝ) / 163840) - δ) * (x - ((4095 : ℝ) / 8192)) * (((8191 : ℝ) / 16384) - x) ^ 2 +
      (202356191899692284532857181856 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((63677 : ℝ) / 163840) - δ) * (x - ((4095 : ℝ) / 8192)) ^ 2 * (((8191 : ℝ) / 16384) - x) +
      (50579139136677641119897218672 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((63677 : ℝ) / 163840) - δ) * (x - ((4095 : ℝ) / 8192)) ^ 3 +
      (50698566489974153862657933720 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (((8191 : ℝ) / 16384) - x) ^ 3 +
      (126751944311296359000293757540 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((4095 : ℝ) / 8192)) * (((8191 : ℝ) / 16384) - x) ^ 2 +
      (101416261167385375889674932530 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 2 * (((8191 : ℝ) / 16384) - x) +
      (25362883155800449699303568435 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((4095 : ℝ) / 8192)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_19 {δ x : ℝ}
    (hdlo : ((39789 : ℝ) / 102400) ≤ δ) (hdhi : δ ≤ ((159229 : ℝ) / 409600))
    (hxlo : ((2047 : ℝ) / 4096) ≤ x) (hxhi : x ≤ ((4095 : ℝ) / 8192)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((39789 : ℝ) / 102400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((159229 : ℝ) / 409600) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((2047 : ℝ) / 4096) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((4095 : ℝ) / 8192) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (3163521178117032240762414464 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (((4095 : ℝ) / 8192) - x) ^ 3 +
      (7906839540934020109082597440 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (x - ((2047 : ℝ) / 4096)) * (((4095 : ℝ) / 8192) - x) ^ 2 +
      (6324124199058105587039702048 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 2 * (((4095 : ℝ) / 8192) - x) +
      (1580805788697246878665526448 : ℝ) * (((159229 : ℝ) / 409600) - δ) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 3 +
      (6334252854719690027195133632 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((159229 : ℝ) / 409600) - δ) * (((4095 : ℝ) / 8192) - x) ^ 3 +
      (15830754247659138824209196576 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((159229 : ℝ) / 409600) - δ) * (x - ((2047 : ℝ) / 4096)) * (((4095 : ℝ) / 8192) - x) ^ 2 +
      (12660768220112073542352098064 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((159229 : ℝ) / 409600) - δ) * (x - ((2047 : ℝ) / 4096)) ^ 2 * (((4095 : ℝ) / 8192) - x) +
      (3164266732041269220055203288 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((159229 : ℝ) / 409600) - δ) * (x - ((2047 : ℝ) / 4096)) ^ 3 +
      (3179521765686853403060854104 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (((4095 : ℝ) / 8192) - x) ^ 3 +
      (7950282231817759797575562244 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((2047 : ℝ) / 4096)) * (((4095 : ℝ) / 8192) - x) ^ 2 +
      (6363008804226654216024935938 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 2 * (((4095 : ℝ) / 8192) - x) +
      (1592248290508253134111511979 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((2047 : ℝ) / 4096)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_20 {δ x : ℝ}
    (hdlo : ((39789 : ℝ) / 102400) ≤ δ) (hdhi : δ ≤ ((79651 : ℝ) / 204800))
    (hxlo : ((1023 : ℝ) / 2048) ≤ x) (hxhi : x ≤ ((2047 : ℝ) / 4096)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((39789 : ℝ) / 102400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((79651 : ℝ) / 204800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((1023 : ℝ) / 2048) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((2047 : ℝ) / 4096) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (197968879733337517257832800 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (((2047 : ℝ) / 4096) - x) ^ 3 +
      (494671691068251610617275920 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (x - ((1023 : ℝ) / 2048)) * (((2047 : ℝ) / 4096) - x) ^ 2 +
      (395562860037039060896766728 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 2 * (((2047 : ℝ) / 4096) - x) +
      (98860036816157257523825452 : ℝ) * (((79651 : ℝ) / 204800) - δ) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 3 +
      (396958203319691255877248160 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((79651 : ℝ) / 204800) - δ) * (((2047 : ℝ) / 4096) - x) ^ 3 +
      (991834679486637967088363248 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((79651 : ℝ) / 204800) - δ) * (x - ((1023 : ℝ) / 2048)) * (((2047 : ℝ) / 4096) - x) ^ 2 +
      (793047229748355165477579640 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((79651 : ℝ) / 204800) - δ) * (x - ((1023 : ℝ) / 2048)) ^ 2 * (((2047 : ℝ) / 4096) - x) +
      (198170729787666111652044948 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((79651 : ℝ) / 204800) - δ) * (x - ((1023 : ℝ) / 2048)) ^ 3 +
      (200088770381870107576178520 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (((2047 : ℝ) / 4096) - x) ^ 3 +
      (500460643024928069273868036 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((1023 : ℝ) / 2048)) * (((2047 : ℝ) / 4096) - x) ^ 2 +
      (400781338657875902675223938 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 2 * (((2047 : ℝ) / 4096) - x) +
      (100409454107033306206736363 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((1023 : ℝ) / 2048)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_21 {δ x : ℝ}
    (hdlo : ((39789 : ℝ) / 102400) ≤ δ) (hdhi : δ ≤ ((19931 : ℝ) / 51200))
    (hxlo : ((511 : ℝ) / 1024) ≤ x) (hxhi : x ≤ ((1023 : ℝ) / 2048)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((39789 : ℝ) / 102400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((19931 : ℝ) / 51200) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((511 : ℝ) / 1024) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1023 : ℝ) / 2048) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (12404479358962332669409880 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (((1023 : ℝ) / 2048) - x) ^ 3 +
      (30979715629039058816913796 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((511 : ℝ) / 1024)) * (((1023 : ℝ) / 2048) - x) ^ 2 +
      (24761766733235451065185730 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 2 * (((1023 : ℝ) / 2048) - x) +
      (6186527491666797414307275 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 3 +
      (24944052379019934261790112 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((19931 : ℝ) / 51200) - δ) * (((1023 : ℝ) / 2048) - x) ^ 3 +
      (62293334666011192712151152 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((19931 : ℝ) / 51200) - δ) * (x - ((511 : ℝ) / 1024)) * (((1023 : ℝ) / 2048) - x) ^ 2 +
      (49786120965025683414535224 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((19931 : ℝ) / 51200) - δ) * (x - ((511 : ℝ) / 1024)) ^ 2 * (((1023 : ℝ) / 2048) - x) +
      (12436832724147108663713460 : ℝ) * (δ - ((39789 : ℝ) / 102400)) * (((19931 : ℝ) / 51200) - δ) * (x - ((511 : ℝ) / 1024)) ^ 3 +
      (12677175374521738078298976 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (((1023 : ℝ) / 2048) - x) ^ 3 +
      (31726254535307208967347472 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((511 : ℝ) / 1024)) * (((1023 : ℝ) / 2048) - x) ^ 2 +
      (25436818225110719225012872 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 2 * (((1023 : ℝ) / 2048) - x) +
      (6387736081919857369001580 : ℝ) * (δ - ((39789 : ℝ) / 102400)) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_22 {δ x : ℝ}
    (hdlo : ((9929 : ℝ) / 25600) ≤ δ) (hdhi : δ ≤ ((39789 : ℝ) / 102400))
    (hxlo : ((511 : ℝ) / 1024) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((9929 : ℝ) / 25600) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((39789 : ℝ) / 102400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((511 : ℝ) / 1024) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (1550873506541400029044784 : ℝ) * (((39789 : ℝ) / 102400) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (3111991410236064615540736 : ℝ) * (((39789 : ℝ) / 102400) - δ) ^ 2 * (x - ((511 : ℝ) / 1024)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (1579218273904249010126848 : ℝ) * (((39789 : ℝ) / 102400) - δ) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (18097409611116044091392 : ℝ) * (((39789 : ℝ) / 102400) - δ) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 3 +
      (3084233132103674551981176 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((39789 : ℝ) / 102400) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (6153682566225236982932480 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((39789 : ℝ) / 102400) - δ) * (x - ((511 : ℝ) / 1024)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (3070408455196562801295360 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((39789 : ℝ) / 102400) - δ) * (x - ((511 : ℝ) / 1024)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (953088994606657306624 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((39789 : ℝ) / 102400) - δ) * (x - ((511 : ℝ) / 1024)) ^ 3 +
      (1550559919870291583676235 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (3093249147648889953199744 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((511 : ℝ) / 1024)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (1542705311709070875164672 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (13112438545002266624 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((511 : ℝ) / 1024)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_23 {δ x : ℝ}
    (hdlo : ((9929 : ℝ) / 25600) ≤ δ) (hdhi : δ ≤ ((19931 : ℝ) / 51200))
    (hxlo : ((255 : ℝ) / 512) ≤ x) (hxhi : x ≤ ((511 : ℝ) / 1024)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((9929 : ℝ) / 25600) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((19931 : ℝ) / 51200) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((255 : ℝ) / 512) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((511 : ℝ) / 1024) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (774840387396080936589408 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (((511 : ℝ) / 1024) - x) ^ 3 +
      (1935433677864197724125328 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((255 : ℝ) / 512)) * (((511 : ℝ) / 1024) - x) ^ 2 +
      (1548312407253083889681992 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 2 * (((511 : ℝ) / 1024) - x) +
      (387718376635350007261196 : ℝ) * (((19931 : ℝ) / 51200) - δ) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 3 +
      (1549818531871321841522976 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((19931 : ℝ) / 51200) - δ) * (((511 : ℝ) / 1024) - x) ^ 3 +
      (3862370532041459298419120 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((19931 : ℝ) / 51200) - δ) * (x - ((255 : ℝ) / 512)) * (((511 : ℝ) / 1024) - x) ^ 2 +
      (3079233298692237385113304 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((19931 : ℝ) / 51200) - δ) * (x - ((255 : ℝ) / 512)) ^ 2 * (((511 : ℝ) / 1024) - x) +
      (766679812781137261468196 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((19931 : ℝ) / 51200) - δ) * (x - ((255 : ℝ) / 512)) ^ 3 +
      (792221360078966826561240 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (((511 : ℝ) / 1024) - x) ^ 3 +
      (1978623549651353043936068 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((255 : ℝ) / 512)) * (((511 : ℝ) / 1024) - x) ^ 2 +
      (1582564665627538274062370 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 2 * (((511 : ℝ) / 1024) - x) +
      (396161730453804314946843 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((255 : ℝ) / 512)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_24 {δ x : ℝ}
    (hdlo : ((9929 : ℝ) / 25600) ≤ δ) (hdhi : δ ≤ ((5001 : ℝ) / 12800))
    (hxlo : ((127 : ℝ) / 256) ≤ x) (hxhi : x ≤ ((255 : ℝ) / 512)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((9929 : ℝ) / 25600) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((5001 : ℝ) / 12800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((127 : ℝ) / 256) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((255 : ℝ) / 512) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (48777691627901027242264 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (((255 : ℝ) / 512) - x) ^ 3 +
      (121522998573004629910564 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((127 : ℝ) / 256)) * (((255 : ℝ) / 512) - x) ^ 2 +
      (96959254088635405657938 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 2 * (((255 : ℝ) / 512) - x) +
      (24213762106127529268419 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 3 +
      (98681608359021250464864 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((5001 : ℝ) / 12800) - δ) * (((255 : ℝ) / 512) - x) ^ 3 +
      (245303201028811220212880 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((5001 : ℝ) / 12800) - δ) * (x - ((127 : ℝ) / 256)) * (((255 : ℝ) / 512) - x) ^ 2 +
      (195058099495165312238408 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((5001 : ℝ) / 12800) - δ) * (x - ((127 : ℝ) / 256)) ^ 2 * (((255 : ℝ) / 512) - x) +
      (48436134029702556558348 : ℝ) * (δ - ((9929 : ℝ) / 25600)) * (((5001 : ℝ) / 12800) - δ) * (x - ((127 : ℝ) / 256)) ^ 3 +
      (52070071551549509227616 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (((255 : ℝ) / 512) - x) ^ 3 +
      (130267899001436760647824 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((127 : ℝ) / 256)) * (((255 : ℝ) / 512) - x) ^ 2 +
      (104575789092198701001032 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 2 * (((255 : ℝ) / 512) - x) +
      (26377773874040767493388 : ℝ) * (δ - ((9929 : ℝ) / 25600)) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_25 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((9929 : ℝ) / 25600))
    (hxlo : ((127 : ℝ) / 256) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((9929 : ℝ) / 25600) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((127 : ℝ) / 256) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (6227202668138889658368 : ℝ) * (((9929 : ℝ) / 25600) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (12756764804541540990976 : ℝ) * (((9929 : ℝ) / 25600) - δ) ^ 2 * (x - ((127 : ℝ) / 256)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (6953165614705098620928 : ℝ) * (((9929 : ℝ) / 25600) - δ) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (423421151760242180096 : ℝ) * (((9929 : ℝ) / 25600) - δ) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 3 +
      (12053644769072857313024 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((9929 : ℝ) / 25600) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (24036264008583252918272 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((9929 : ℝ) / 25600) - δ) * (x - ((127 : ℝ) / 256)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (12155996105303077421056 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((9929 : ℝ) / 25600) - δ) * (x - ((127 : ℝ) / 256)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (173009511848372862976 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((9929 : ℝ) / 25600) - δ) * (x - ((127 : ℝ) / 256)) ^ 3 +
      (6097211453487628405283 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (12089115282788272261792 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((127 : ℝ) / 256)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (6009762118278273089536 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (17673251573355511808 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((127 : ℝ) / 256)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_26 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((5001 : ℝ) / 12800))
    (hxlo : ((63 : ℝ) / 128) ≤ x) (hxhi : x ≤ ((127 : ℝ) / 256)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((5001 : ℝ) / 12800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((63 : ℝ) / 128) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((127 : ℝ) / 256) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (3068368051148727091200 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (((127 : ℝ) / 256) - x) ^ 3 +
      (7663134603551402639360 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((63 : ℝ) / 128)) * (((127 : ℝ) / 256) - x) ^ 2 +
      (6151612801072949239808 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 2 * (((127 : ℝ) / 256) - x) +
      (1556800667034722414592 : ℝ) * (((5001 : ℝ) / 12800) - δ) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 3 +
      (6074806306206360222720 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((5001 : ℝ) / 12800) - δ) * (((127 : ℝ) / 256) - x) ^ 3 +
      (15001069442819371473408 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((5001 : ℝ) / 12800) - δ) * (x - ((63 : ℝ) / 128)) * (((127 : ℝ) / 256) - x) ^ 2 +
      (11839576700781047000320 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((5001 : ℝ) / 12800) - δ) * (x - ((63 : ℝ) / 128)) ^ 2 * (((127 : ℝ) / 256) - x) +
      (2913221050466983827328 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((5001 : ℝ) / 12800) - δ) * (x - ((63 : ℝ) / 128)) ^ 3 +
      (3279907124376041548440 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((127 : ℝ) / 256) - x) ^ 3 +
      (8155634382605950792996 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((63 : ℝ) / 128)) * (((127 : ℝ) / 256) - x) ^ 2 +
      (6502963936283501929778 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 2 * (((127 : ℝ) / 256) - x) +
      (1627189735985922163363 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((63 : ℝ) / 128)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_27 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((2537 : ℝ) / 6400))
    (hxlo : ((31 : ℝ) / 64) ≤ x) (hxhi : x ≤ ((63 : ℝ) / 128)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((2537 : ℝ) / 6400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((31 : ℝ) / 64) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((63 : ℝ) / 128) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (196076962302749859840 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (((63 : ℝ) / 128) - x) ^ 3 +
      (484211666959081148416 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (x - ((31 : ℝ) / 64)) * (((63 : ℝ) / 128) - x) ^ 2 +
      (384032601663616829440 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 2 * (((63 : ℝ) / 128) - x) +
      (95886501598397721600 : ℝ) * (((2537 : ℝ) / 6400) - δ) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 3 +
      (405950594298233585152 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((2537 : ℝ) / 6400) - δ) * (((63 : ℝ) / 128) - x) ^ 3 +
      (991904400885803724032 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((2537 : ℝ) / 6400) - δ) * (x - ((31 : ℝ) / 64)) * (((63 : ℝ) / 128) - x) ^ 2 +
      (773879663561422532224 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((2537 : ℝ) / 6400) - δ) * (x - ((31 : ℝ) / 64)) ^ 2 * (((63 : ℝ) / 128) - x) +
      (187902390941102070720 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((2537 : ℝ) / 6400) - δ) * (x - ((31 : ℝ) / 64)) ^ 3 +
      (244737795744098228056 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((63 : ℝ) / 128) - x) ^ 3 +
      (611600871157080128932 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((31 : ℝ) / 64)) * (((63 : ℝ) / 128) - x) ^ 2 +
      (493074654046519682082 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 2 * (((63 : ℝ) / 128) - x) +
      (126199498007505401235 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((31 : ℝ) / 64)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_28 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((261 : ℝ) / 640))
    (hxlo : ((15 : ℝ) / 32) ≤ x) (hxhi : x ≤ ((31 : ℝ) / 64)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((261 : ℝ) / 640) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((15 : ℝ) / 32) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((31 : ℝ) / 64) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (13111474502718928896 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (((31 : ℝ) / 64) - x) ^ 3 +
      (31864637041241867264 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (x - ((15 : ℝ) / 32)) * (((31 : ℝ) / 64) - x) ^ 2 +
      (24883416462705826304 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 2 * (((31 : ℝ) / 64) - x) +
      (6127405071960933120 : ℝ) * (((261 : ℝ) / 640) - δ) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 3 +
      (29384780076817991424 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((261 : ℝ) / 640) - δ) * (((31 : ℝ) / 64) - x) ^ 3 +
      (70853969021788280448 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((261 : ℝ) / 640) - δ) * (x - ((15 : ℝ) / 32)) * (((31 : ℝ) / 64) - x) ^ 2 +
      (54592326256619273536 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((261 : ℝ) / 640) - δ) * (x - ((15 : ℝ) / 32)) ^ 2 * (((31 : ℝ) / 64) - x) +
      (13117101999717732832 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((261 : ℝ) / 640) - δ) * (x - ((15 : ℝ) / 32)) ^ 3 +
      (20804329015638431160 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((31 : ℝ) / 64) - x) ^ 3 +
      (52407474860941019620 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((15 : ℝ) / 32)) * (((31 : ℝ) / 64) - x) ^ 2 +
      (42954059703515374490 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 2 * (((31 : ℝ) / 64) - x) +
      (11347717396333612555 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((15 : ℝ) / 32)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_29 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((689 : ℝ) / 1600))
    (hxlo : ((7 : ℝ) / 16) ≤ x) (hxhi : x ≤ ((15 : ℝ) / 32)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((689 : ℝ) / 1600) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((7 : ℝ) / 16) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((15 : ℝ) / 32) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (938378181494997504 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (((15 : ℝ) / 32) - x) ^ 3 +
      (2223994779041624320 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (x - ((7 : ℝ) / 16)) * (((15 : ℝ) / 32) - x) ^ 2 +
      (1696062388812082048 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 2 * (((15 : ℝ) / 32) - x) +
      (409733578209966528 : ℝ) * (((689 : ℝ) / 1600) - δ) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 3 +
      (2385038559734138752 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((689 : ℝ) / 1600) - δ) * (((15 : ℝ) / 32) - x) ^ 3 +
      (5646431619360719936 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((689 : ℝ) / 1600) - δ) * (x - ((7 : ℝ) / 16)) * (((15 : ℝ) / 32) - x) ^ 2 +
      (4280067887862421024 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((689 : ℝ) / 1600) - δ) * (x - ((7 : ℝ) / 16)) ^ 2 * (((15 : ℝ) / 32) - x) +
      (1017081598381191408 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((689 : ℝ) / 1600) - δ) * (x - ((7 : ℝ) / 16)) ^ 3 +
      (2057747408372723944 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((15 : ℝ) / 32) - x) ^ 3 +
      (5210001589723518724 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((7 : ℝ) / 16)) * (((15 : ℝ) / 32) - x) ^ 2 +
      (4326871150683477078 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 2 * (((15 : ℝ) / 32) - x) +
      (1173725950363645959 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((7 : ℝ) / 16)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_30 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((381 : ℝ) / 800))
    (hxlo : ((3 : ℝ) / 8) ≤ x) (hxhi : x ≤ ((7 : ℝ) / 16)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((381 : ℝ) / 800) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((3 : ℝ) / 8) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((7 : ℝ) / 16) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (74349528677529600 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (((7 : ℝ) / 16) - x) ^ 3 +
      (169766347097305280 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) * (((7 : ℝ) / 16) - x) ^ 2 +
      (124919189855366528 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((7 : ℝ) / 16) - x) +
      (29324318171718672 : ℝ) * (((381 : ℝ) / 800) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 +
      (225328057121710080 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((381 : ℝ) / 800) - δ) * (((7 : ℝ) / 16) - x) ^ 3 +
      (520413132801813888 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((381 : ℝ) / 800) - δ) * (x - ((3 : ℝ) / 8)) * (((7 : ℝ) / 16) - x) ^ 2 +
      (385941857719630000 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((381 : ℝ) / 800) - δ) * (x - ((3 : ℝ) / 8)) ^ 2 * (((7 : ℝ) / 16) - x) +
      (90416273639946328 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((381 : ℝ) / 800) - δ) * (x - ((3 : ℝ) / 8)) ^ 3 +
      (239297116242356160 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((7 : ℝ) / 16) - x) ^ 3 +
      (603151214115284596 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((3 : ℝ) / 8)) * (((7 : ℝ) / 16) - x) ^ 2 +
      (501604389413438228 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((7 : ℝ) / 16) - x) +
      (137477834234925493 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_31 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((227 : ℝ) / 400))
    (hxlo : ((1 : ℝ) / 4) ≤ x) (hxhi : x ≤ ((3 : ℝ) / 8)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((227 : ℝ) / 400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((1 : ℝ) / 4) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((3 : ℝ) / 8) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (6752461232264160 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (((3 : ℝ) / 8) - x) ^ 3 +
      (14684933392096936 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (10300408246973620 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (2323422771172800 : ℝ) * (((227 : ℝ) / 400) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 +
      (25519655996066152 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((227 : ℝ) / 400) - δ) * (((3 : ℝ) / 8) - x) ^ 3 +
      (57046844437238972 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((227 : ℝ) / 400) - δ) * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (41094574036787944 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((227 : ℝ) / 400) - δ) * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (9436158027761280 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((227 : ℝ) / 400) - δ) * (x - ((1 : ℝ) / 4)) ^ 3 +
      (33194168215463236 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((3 : ℝ) / 8) - x) ^ 3 +
      (81971363022408352 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (67026469960067967 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (18152558731360440 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_32 {δ x : ℝ}
    (hdlo : ((77 : ℝ) / 200) ≤ δ) (hdhi : δ ≤ ((3 : ℝ) / 4))
    (hxlo : (0 : ℝ) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 4)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((77 : ℝ) / 200) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((3 : ℝ) / 4) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - (0 : ℝ) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 4) - x := sub_nonneg.mpr hxhi
  have hid : (134890312500000 : ℝ) * certificatePolynomial δ x =
      (1437823062980532 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (((1 : ℝ) / 4) - x) ^ 3 +
      (2956180347116473 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (1962642769136473 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (422028827016510 : ℝ) * (((3 : ℝ) / 4) - δ) ^ 2 * (x - (0 : ℝ)) ^ 3 +
      (7103495904395148 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((3 : ℝ) / 4) - δ) * (((1 : ℝ) / 4) - x) ^ 3 +
      (15193498655025831 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((3 : ℝ) / 4) - δ) * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (10522616347991732 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((3 : ℝ) / 4) - δ) * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (2345899345475249 : ℝ) * (δ - ((77 : ℝ) / 200)) * (((3 : ℝ) / 4) - δ) * (x - (0 : ℝ)) ^ 3 +
      (11422475303646600 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (((1 : ℝ) / 4) - x) ^ 3 +
      (27023337345077450 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (21215937856459900 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (5530613881374050 : ℝ) * (δ - ((77 : ℝ) / 200)) ^ 2 * (x - (0 : ℝ)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (134890312500000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (134890312500000 : ℝ))).mp hnonneg

private theorem rectangle_33 {δ x : ℝ}
    (hdlo : ((47 : ℝ) / 160) ≤ δ) (hdhi : δ ≤ ((77 : ℝ) / 200))
    (hxlo : ((3 : ℝ) / 8) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((47 : ℝ) / 160) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((77 : ℝ) / 200) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((3 : ℝ) / 8) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (10754889588631800 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (28082915459324085 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (26268217013278600 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (8836537580673040 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 +
      (9008757198551040 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (12636792301198688 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (4567594652867560 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (667854894311072 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (x - ((3 : ℝ) / 8)) ^ 3 +
      (9293691084691200 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (14560513520252720 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (5457494633104224 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (12618933670528 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_34 {δ x : ℝ}
    (hdlo : ((81 : ℝ) / 400) ≤ δ) (hdhi : δ ≤ ((47 : ℝ) / 160))
    (hxlo : ((3 : ℝ) / 8) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((81 : ℝ) / 400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((47 : ℝ) / 160) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((3 : ℝ) / 8) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (34295735042116320 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (101618590755151684 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (101395173380483504 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (34023059467740544 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 +
      (34010801155976160 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (99694869536097652 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (100505273400246840 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (34678295428381088 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (x - ((3 : ℝ) / 8)) ^ 3 +
      (10754889588631800 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (28082915459324085 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - ((3 : ℝ) / 8)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (26268217013278600 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (8836537580673040 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - ((3 : ℝ) / 8)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_35 {δ x : ℝ}
    (hdlo : ((47 : ℝ) / 160) ≤ δ) (hdhi : δ ≤ ((77 : ℝ) / 200))
    (hxlo : ((1 : ℝ) / 4) ≤ x) (hxhi : x ≤ ((3 : ℝ) / 8)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((47 : ℝ) / 160) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((77 : ℝ) / 200) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((1 : ℝ) / 4) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((3 : ℝ) / 8) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (17407351317642220 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (((3 : ℝ) / 8) - x) ^ 3 +
      (42995230239563860 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (36446422072466715 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (10754889588631800 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 +
      (29990222795037616 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (((3 : ℝ) / 8) - x) ^ 3 +
      (62125511830685288 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (41415750890107552 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (9008757198551040 : ℝ) * (δ - ((47 : ℝ) / 160)) * (((77 : ℝ) / 200) - δ) * (x - ((1 : ℝ) / 4)) ^ 3 +
      (27009844929056640 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (((3 : ℝ) / 8) - x) ^ 3 +
      (58739733568387744 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (41201632987894480 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (9293691084691200 : ℝ) * (δ - ((47 : ℝ) / 160)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_36 {δ x : ℝ}
    (hdlo : ((81 : ℝ) / 400) ≤ δ) (hdhi : δ ≤ ((47 : ℝ) / 160))
    (hxlo : ((1 : ℝ) / 4) ≤ x) (hxhi : x ≤ ((3 : ℝ) / 8)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((81 : ℝ) / 400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((47 : ℝ) / 160) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((1 : ℝ) / 4) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((3 : ℝ) / 8) - x := sub_nonneg.mpr hxhi
  have hid : (67445156250000 : ℝ) * certificatePolynomial δ x =
      (36658804609550288 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (((3 : ℝ) / 8) - x) ^ 3 +
      (106469630865272608 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (104155819497546236 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (34295735042116320 : ℝ) * (((47 : ℝ) / 160) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 +
      (39639182475531264 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (((3 : ℝ) / 8) - x) ^ 3 +
      (109855409127570152 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (104369937399759308 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (34010801155976160 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((47 : ℝ) / 160) - δ) * (x - ((1 : ℝ) / 4)) ^ 3 +
      (17407351317642220 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (((3 : ℝ) / 8) - x) ^ 3 +
      (42995230239563860 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - ((1 : ℝ) / 4)) * (((3 : ℝ) / 8) - x) ^ 2 +
      (36446422072466715 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((3 : ℝ) / 8) - x) +
      (10754889588631800 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (67445156250000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (67445156250000 : ℝ))).mp hnonneg

private theorem rectangle_37 {δ x : ℝ}
    (hdlo : ((1 : ℝ) / 50) ≤ δ) (hdhi : δ ≤ ((81 : ℝ) / 400))
    (hxlo : ((1 : ℝ) / 4) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 2)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((1 : ℝ) / 50) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((81 : ℝ) / 400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - ((1 : ℝ) / 4) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 2) - x := sub_nonneg.mpr hxhi
  have hid : (134890312500000 : ℝ) * certificatePolynomial δ x =
      (10107721993958368 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (28561227015660896 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (26796489829109888 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (8342744560129408 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 +
      (8792153919139950 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (((1 : ℝ) / 2) - x) ^ 3 +
      (26011909109642068 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (x - ((1 : ℝ) / 4)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (25648480569735714 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (x - ((1 : ℝ) / 4)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (8423860371855068 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (x - ((1 : ℝ) / 4)) ^ 3 +
      (2291175288096893 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 3 +
      (6435177993868397 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (x - ((1 : ℝ) / 4)) * (((1 : ℝ) / 2) - x) ^ 2 +
      (6295073022359086 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 2 * (((1 : ℝ) / 2) - x) +
      (2126441216733784 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (x - ((1 : ℝ) / 4)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (134890312500000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (134890312500000 : ℝ))).mp hnonneg

private theorem rectangle_38 {δ x : ℝ}
    (hdlo : ((81 : ℝ) / 400) ≤ δ) (hdhi : δ ≤ ((77 : ℝ) / 200))
    (hxlo : (0 : ℝ) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 4)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((81 : ℝ) / 400) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((77 : ℝ) / 200) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - (0 : ℝ) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 4) - x := sub_nonneg.mpr hxhi
  have hid : (134890312500000 : ℝ) * certificatePolynomial δ x =
      (3052395157285944 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (((1 : ℝ) / 4) - x) ^ 3 +
      (8048464504048214 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (7311873734712961 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (2291175288096893 : ℝ) * (((77 : ℝ) / 200) - δ) ^ 2 * (x - (0 : ℝ)) ^ 3 +
      (3046884946976088 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((77 : ℝ) / 200) - δ) * (((1 : ℝ) / 4) - x) ^ 3 +
      (5087166855346014 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((77 : ℝ) / 200) - δ) * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (2506480533654212 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((77 : ℝ) / 200) - δ) * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (372547233247622 : ℝ) * (δ - ((81 : ℝ) / 400)) * (((77 : ℝ) / 200) - δ) * (x - (0 : ℝ)) ^ 3 +
      (5751292251922128 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (((1 : ℝ) / 4) - x) ^ 3 +
      (11824721388465892 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (7850571076545892 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (1688115308066040 : ℝ) * (δ - ((81 : ℝ) / 400)) ^ 2 * (x - (0 : ℝ)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (134890312500000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (134890312500000 : ℝ))).mp hnonneg

private theorem rectangle_39 {δ x : ℝ}
    (hdlo : ((1 : ℝ) / 50) ≤ δ) (hdhi : δ ≤ ((81 : ℝ) / 400))
    (hxlo : (0 : ℝ) ≤ x) (hxhi : x ≤ ((1 : ℝ) / 4)) :
    0 ≤ certificatePolynomial δ x := by
  have hda : 0 ≤ δ - ((1 : ℝ) / 50) := sub_nonneg.mpr hdlo
  have hdb : 0 ≤ ((81 : ℝ) / 400) - δ := sub_nonneg.mpr hdhi
  have hxc : 0 ≤ x - (0 : ℝ) := sub_nonneg.mpr hxlo
  have hxd : 0 ≤ ((1 : ℝ) / 4) - x := sub_nonneg.mpr hxhi
  have hid : (134890312500000 : ℝ) * certificatePolynomial δ x =
      (11867102987113728 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (((1 : ℝ) / 4) - x) ^ 3 +
      (33844245693966720 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (32085104948089312 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (10107721993958368 : ℝ) * (((81 : ℝ) / 400) - δ) ^ 2 * (x - (0 : ℝ)) ^ 3 +
      (9162695682167688 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (((1 : ℝ) / 4) - x) ^ 3 +
      (27106691160846842 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (26741014405197632 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (8792153919139950 : ℝ) * (δ - ((1 : ℝ) / 50)) * (((81 : ℝ) / 400) - δ) * (x - (0 : ℝ)) ^ 3 +
      (3052395157285944 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (((1 : ℝ) / 4) - x) ^ 3 +
      (8048464504048214 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (x - (0 : ℝ)) * (((1 : ℝ) / 4) - x) ^ 2 +
      (7311873734712961 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 4) - x) +
      (2291175288096893 : ℝ) * (δ - ((1 : ℝ) / 50)) ^ 2 * (x - (0 : ℝ)) ^ 3 := by
    unfold certificatePolynomial
    ring
  have hnonneg : 0 ≤ (134890312500000 : ℝ) * certificatePolynomial δ x := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (134890312500000 : ℝ))).mp hnonneg

/-- Finite exact rectangle coverage, with no sampling assumption. -/
theorem certificate_nonnegative {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    0 ≤ certificatePolynomial δ x := by
  by_cases hsplit1 : δ ≤ ((77 : ℝ) / 200)
  · by_cases hsplit2 : x ≤ ((1 : ℝ) / 4)
    · by_cases hsplit3 : δ ≤ ((81 : ℝ) / 400)
      · exact rectangle_39 hdlo hsplit3 hxlo hsplit2
      · have hlower3 : ((81 : ℝ) / 400) ≤ δ := le_of_lt (lt_of_not_ge hsplit3)
        exact rectangle_38 hlower3 hsplit1 hxlo hsplit2
    · have hlower2 : ((1 : ℝ) / 4) ≤ x := le_of_lt (lt_of_not_ge hsplit2)
      by_cases hsplit4 : δ ≤ ((81 : ℝ) / 400)
      · exact rectangle_37 hdlo hsplit4 hlower2 hxhi
      · have hlower4 : ((81 : ℝ) / 400) ≤ δ := le_of_lt (lt_of_not_ge hsplit4)
        by_cases hsplit5 : x ≤ ((3 : ℝ) / 8)
        · by_cases hsplit6 : δ ≤ ((47 : ℝ) / 160)
          · exact rectangle_36 hlower4 hsplit6 hlower2 hsplit5
          · have hlower6 : ((47 : ℝ) / 160) ≤ δ := le_of_lt (lt_of_not_ge hsplit6)
            exact rectangle_35 hlower6 hsplit1 hlower2 hsplit5
        · have hlower5 : ((3 : ℝ) / 8) ≤ x := le_of_lt (lt_of_not_ge hsplit5)
          by_cases hsplit7 : δ ≤ ((47 : ℝ) / 160)
          · exact rectangle_34 hlower4 hsplit7 hlower5 hxhi
          · have hlower7 : ((47 : ℝ) / 160) ≤ δ := le_of_lt (lt_of_not_ge hsplit7)
            exact rectangle_33 hlower7 hsplit1 hlower5 hxhi
  · have hlower1 : ((77 : ℝ) / 200) ≤ δ := le_of_lt (lt_of_not_ge hsplit1)
    by_cases hsplit8 : x ≤ ((1 : ℝ) / 4)
    · exact rectangle_32 hlower1 hdhi hxlo hsplit8
    · have hlower8 : ((1 : ℝ) / 4) ≤ x := le_of_lt (lt_of_not_ge hsplit8)
      by_cases hsplit9 : δ ≤ ((227 : ℝ) / 400)
      · by_cases hsplit10 : x ≤ ((3 : ℝ) / 8)
        · exact rectangle_31 hlower1 hsplit9 hlower8 hsplit10
        · have hlower10 : ((3 : ℝ) / 8) ≤ x := le_of_lt (lt_of_not_ge hsplit10)
          by_cases hsplit11 : δ ≤ ((381 : ℝ) / 800)
          · by_cases hsplit12 : x ≤ ((7 : ℝ) / 16)
            · exact rectangle_30 hlower1 hsplit11 hlower10 hsplit12
            · have hlower12 : ((7 : ℝ) / 16) ≤ x := le_of_lt (lt_of_not_ge hsplit12)
              by_cases hsplit13 : δ ≤ ((689 : ℝ) / 1600)
              · by_cases hsplit14 : x ≤ ((15 : ℝ) / 32)
                · exact rectangle_29 hlower1 hsplit13 hlower12 hsplit14
                · have hlower14 : ((15 : ℝ) / 32) ≤ x := le_of_lt (lt_of_not_ge hsplit14)
                  by_cases hsplit15 : δ ≤ ((261 : ℝ) / 640)
                  · by_cases hsplit16 : x ≤ ((31 : ℝ) / 64)
                    · exact rectangle_28 hlower1 hsplit15 hlower14 hsplit16
                    · have hlower16 : ((31 : ℝ) / 64) ≤ x := le_of_lt (lt_of_not_ge hsplit16)
                      by_cases hsplit17 : δ ≤ ((2537 : ℝ) / 6400)
                      · by_cases hsplit18 : x ≤ ((63 : ℝ) / 128)
                        · exact rectangle_27 hlower1 hsplit17 hlower16 hsplit18
                        · have hlower18 : ((63 : ℝ) / 128) ≤ x := le_of_lt (lt_of_not_ge hsplit18)
                          by_cases hsplit19 : δ ≤ ((5001 : ℝ) / 12800)
                          · by_cases hsplit20 : x ≤ ((127 : ℝ) / 256)
                            · exact rectangle_26 hlower1 hsplit19 hlower18 hsplit20
                            · have hlower20 : ((127 : ℝ) / 256) ≤ x := le_of_lt (lt_of_not_ge hsplit20)
                              by_cases hsplit21 : δ ≤ ((9929 : ℝ) / 25600)
                              · exact rectangle_25 hlower1 hsplit21 hlower20 hxhi
                              · have hlower21 : ((9929 : ℝ) / 25600) ≤ δ := le_of_lt (lt_of_not_ge hsplit21)
                                by_cases hsplit22 : x ≤ ((255 : ℝ) / 512)
                                · exact rectangle_24 hlower21 hsplit19 hlower20 hsplit22
                                · have hlower22 : ((255 : ℝ) / 512) ≤ x := le_of_lt (lt_of_not_ge hsplit22)
                                  by_cases hsplit23 : δ ≤ ((19931 : ℝ) / 51200)
                                  · by_cases hsplit24 : x ≤ ((511 : ℝ) / 1024)
                                    · exact rectangle_23 hlower21 hsplit23 hlower22 hsplit24
                                    · have hlower24 : ((511 : ℝ) / 1024) ≤ x := le_of_lt (lt_of_not_ge hsplit24)
                                      by_cases hsplit25 : δ ≤ ((39789 : ℝ) / 102400)
                                      · exact rectangle_22 hlower21 hsplit25 hlower24 hxhi
                                      · have hlower25 : ((39789 : ℝ) / 102400) ≤ δ := le_of_lt (lt_of_not_ge hsplit25)
                                        by_cases hsplit26 : x ≤ ((1023 : ℝ) / 2048)
                                        · exact rectangle_21 hlower25 hsplit23 hlower24 hsplit26
                                        · have hlower26 : ((1023 : ℝ) / 2048) ≤ x := le_of_lt (lt_of_not_ge hsplit26)
                                          by_cases hsplit27 : δ ≤ ((79651 : ℝ) / 204800)
                                          · by_cases hsplit28 : x ≤ ((2047 : ℝ) / 4096)
                                            · exact rectangle_20 hlower25 hsplit27 hlower26 hsplit28
                                            · have hlower28 : ((2047 : ℝ) / 4096) ≤ x := le_of_lt (lt_of_not_ge hsplit28)
                                              by_cases hsplit29 : δ ≤ ((159229 : ℝ) / 409600)
                                              · by_cases hsplit30 : x ≤ ((4095 : ℝ) / 8192)
                                                · exact rectangle_19 hlower25 hsplit29 hlower28 hsplit30
                                                · have hlower30 : ((4095 : ℝ) / 8192) ≤ x := le_of_lt (lt_of_not_ge hsplit30)
                                                  by_cases hsplit31 : δ ≤ ((63677 : ℝ) / 163840)
                                                  · by_cases hsplit32 : x ≤ ((8191 : ℝ) / 16384)
                                                    · exact rectangle_18 hlower25 hsplit31 hlower30 hsplit32
                                                    · have hlower32 : ((8191 : ℝ) / 16384) ≤ x := le_of_lt (lt_of_not_ge hsplit32)
                                                      by_cases hsplit33 : δ ≤ ((636697 : ℝ) / 1638400)
                                                      · by_cases hsplit34 : x ≤ ((16383 : ℝ) / 32768)
                                                        · exact rectangle_17 hlower25 hsplit33 hlower32 hsplit34
                                                        · have hlower34 : ((16383 : ℝ) / 32768) ≤ x := le_of_lt (lt_of_not_ge hsplit34)
                                                          by_cases hsplit35 : δ ≤ ((1273321 : ℝ) / 3276800)
                                                          · by_cases hsplit36 : x ≤ ((32767 : ℝ) / 65536)
                                                            · exact rectangle_16 hlower25 hsplit35 hlower34 hsplit36
                                                            · have hlower36 : ((32767 : ℝ) / 65536) ≤ x := le_of_lt (lt_of_not_ge hsplit36)
                                                              by_cases hsplit37 : δ ≤ ((2546569 : ℝ) / 6553600)
                                                              · exact rectangle_15 hlower25 hsplit37 hlower36 hxhi
                                                              · have hlower37 : ((2546569 : ℝ) / 6553600) ≤ δ := le_of_lt (lt_of_not_ge hsplit37)
                                                                by_cases hsplit38 : x ≤ ((65535 : ℝ) / 131072)
                                                                · exact rectangle_14 hlower37 hsplit35 hlower36 hsplit38
                                                                · have hlower38 : ((65535 : ℝ) / 131072) ≤ x := le_of_lt (lt_of_not_ge hsplit38)
                                                                  by_cases hsplit39 : δ ≤ ((5093211 : ℝ) / 13107200)
                                                                  · exact rectangle_13 hlower37 hsplit39 hlower38 hxhi
                                                                  · have hlower39 : ((5093211 : ℝ) / 13107200) ≤ δ := le_of_lt (lt_of_not_ge hsplit39)
                                                                    exact rectangle_12 hlower39 hsplit35 hlower38 hxhi
                                                          · have hlower35 : ((1273321 : ℝ) / 3276800) ≤ δ := le_of_lt (lt_of_not_ge hsplit35)
                                                            exact rectangle_11 hlower35 hsplit33 hlower34 hxhi
                                                      · have hlower33 : ((636697 : ℝ) / 1638400) ≤ δ := le_of_lt (lt_of_not_ge hsplit33)
                                                        exact rectangle_10 hlower33 hsplit31 hlower32 hxhi
                                                  · have hlower31 : ((63677 : ℝ) / 163840) ≤ δ := le_of_lt (lt_of_not_ge hsplit31)
                                                    exact rectangle_9 hlower31 hsplit29 hlower30 hxhi
                                              · have hlower29 : ((159229 : ℝ) / 409600) ≤ δ := le_of_lt (lt_of_not_ge hsplit29)
                                                exact rectangle_8 hlower29 hsplit27 hlower28 hxhi
                                          · have hlower27 : ((79651 : ℝ) / 204800) ≤ δ := le_of_lt (lt_of_not_ge hsplit27)
                                            exact rectangle_7 hlower27 hsplit23 hlower26 hxhi
                                  · have hlower23 : ((19931 : ℝ) / 51200) ≤ δ := le_of_lt (lt_of_not_ge hsplit23)
                                    exact rectangle_6 hlower23 hsplit19 hlower22 hxhi
                          · have hlower19 : ((5001 : ℝ) / 12800) ≤ δ := le_of_lt (lt_of_not_ge hsplit19)
                            exact rectangle_5 hlower19 hsplit17 hlower18 hxhi
                      · have hlower17 : ((2537 : ℝ) / 6400) ≤ δ := le_of_lt (lt_of_not_ge hsplit17)
                        exact rectangle_4 hlower17 hsplit15 hlower16 hxhi
                  · have hlower15 : ((261 : ℝ) / 640) ≤ δ := le_of_lt (lt_of_not_ge hsplit15)
                    exact rectangle_3 hlower15 hsplit13 hlower14 hxhi
              · have hlower13 : ((689 : ℝ) / 1600) ≤ δ := le_of_lt (lt_of_not_ge hsplit13)
                exact rectangle_2 hlower13 hsplit11 hlower12 hxhi
          · have hlower11 : ((381 : ℝ) / 800) ≤ δ := le_of_lt (lt_of_not_ge hsplit11)
            exact rectangle_1 hlower11 hsplit9 hlower10 hxhi
      · have hlower9 : ((227 : ℝ) / 400) ≤ δ := le_of_lt (lt_of_not_ge hsplit9)
        exact rectangle_0 hlower9 hdhi hlower8 hxhi

/-- Verified adaptive endpoint inequality for the full rational count. -/
theorem adaptive_endpoint_bound {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    endpointExponent δ x ≤ -(1 / 1000000000000 : ℝ) := by
  have hJ := countDenominator_pos hdlo hdhi hxlo hxhi
  have hp := certificate_nonnegative hdlo hdhi hxlo hxhi
  rw [certificate_identity δ x (ne_of_gt hJ)] at hp
  have he : 0 ≤ -endpointExponent δ x - saving :=
    (mul_nonneg_iff_of_pos_right hJ).mp hp
  unfold saving at he
  linarith

end

end RH.Transport.TunedEndpoint

end

section
-- module Transport.PhysicalHigh.RowCount (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section

open scoped Classical BigOperators ContDiff

open Set Filter

open OAI OAI.SevenEighths

open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch

open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst

open HeckeDetectorAdaptiveCutoff

/-- The source's complementary amplitude coordinate gives precisely the
full rational count used by the tuned endpoint certificate. -/
theorem balanced_count_eq (δ x : ℝ) :
    OAI.SevenEighths.Endpoint.balancedRowCount δ (1 / 2 - x) =
      RH.Transport.Endpoint.adaptiveCount δ x := by
  have hJ : OAI.SevenEighths.Endpoint.balanceDenominator δ (1 / 2 - x) =
      RH.Transport.Endpoint.countDenominator δ x := by
    unfold OAI.SevenEighths.Endpoint.balanceDenominator
      OAI.SevenEighths.Endpoint.denominator OAI.SevenEighths.Endpoint.primeWeight
      RH.Transport.Endpoint.countDenominator
    ring
  have hP : OAI.SevenEighths.Endpoint.primeWeight (1 / 2 - x) =
      (2 - 8 * x / 9) * (1 - x) := by
    unfold OAI.SevenEighths.Endpoint.primeWeight
    ring
  unfold OAI.SevenEighths.Endpoint.balancedRowCount
    OAI.SevenEighths.Endpoint.balancedCutoff
  rw [hJ, hP]
  unfold RH.Transport.Endpoint.adaptiveCount
  ring

end

end RH.Transport.PhysicalHigh

end

section
-- module Transport.Candidate (LW56e2)
namespace RH.Transport.Candidate

open RH.Transport.Geometry

open RH.Transport.LocalBounds

noncomputable section

def p : ℝ := 68479 / 400000000

def B : ℝ := boundary p

def zeta : ℝ := 1 / 320000000000

inductive SideCondition where
  | lowSubset
  | minimumWidth
  | minimumLx
  | minimumLy
  | gram
  | floor
  | intermediate
  | small
  | selectedSupply
  | strongSupply
  | bufferedUpperScale
  | principalW
  | principalZ
  | goodTail
  | principalMixed
  | smallFirstRegion

def sideMargin (term : SideCondition) : ℝ :=
  match term with
  | .lowSubset => 1 / 5 - ell p
  | .minimumWidth => 1 - 3 * ell p
  | .minimumLx => lx p - ell p
  | .minimumLy => ly p - ell p
  | .gram => ly p - ell p - 11 * b / 6
  | .floor => 7 / 1200 - (32 / 25) * p
  | .intermediate => 241 / 9600 - (329 / 400) * p
  | .small => 63 / 800 - (51 / 100) * p
  | .selectedSupply => ell p / (h p + zeta) - 7 / 37
  | .strongSupply => 5 * ell p - h p - zeta
  | .bufferedUpperScale => 1 - h p - zeta
  | .principalW => ly p / 20
  | .principalZ => h p / 600
  | .goodTail => goodTailDecay p - 4 / 5
  | .principalMixed => 4 * B - 301 / 100
  | .smallFirstRegion => B - 1 / 2

end

end RH.Transport.Candidate

end

section
-- module Transport.Certificate (LW56e2)
namespace RH.Transport.Certificate

noncomputable section

theorem adaptive_count_bounds {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    1 - δ ≤ Endpoint.adaptiveCount δ x ∧ Endpoint.adaptiveCount δ x ≤ 1 := by
  have hJ := Endpoint.countDenominator_pos hdlo hdhi hxlo hxhi
  have hd : 0 ≤ δ := by linarith
  have ha : 0 ≤ (5 / 6 : ℝ) - δ := by linarith
  have hP : 0 ≤ ((2 : ℝ) - 8 * x / 9) * (1 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hP2 : ((2 : ℝ) - 8 * x / 9) * (1 - x) ≤ 2 := by
    calc
      _ ≤ 2 * (1 - x) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 2 := by linarith
  have hD : (2 : ℝ) ≤ 3 - 17 * x / 9 := by linarith
  have hPD : ((2 : ℝ) - 8 * x / 9) * (1 - x) ≤ 3 - 17 * x / 9 :=
    hP2.trans hD
  have hPJ : (5 / 6 - δ) * ((2 - 8 * x / 9) * (1 - x)) ≤
      Endpoint.countDenominator δ x := by
    have hm := mul_le_mul_of_nonneg_left hPD ha
    have hn := mul_nonneg hd hP
    unfold Endpoint.countDenominator
    linarith
  have hnum : 0 ≤ (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) :=
    mul_nonneg (mul_nonneg ha hd) hP
  have hquot0 := div_nonneg hnum (show 0 ≤ 2 * Endpoint.countDenominator δ x by positivity)
  have hquot : (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) /
      (2 * Endpoint.countDenominator δ x) ≤ δ := by
    apply (div_le_iff₀ (show 0 < 2 * Endpoint.countDenominator δ x by positivity)).2
    have hm := mul_le_mul_of_nonneg_left hPJ hd
    have hn := mul_nonneg hd hJ.le
    nlinarith
  unfold Endpoint.adaptiveCount
  constructor <;> linarith

def rowSlope (δ x : ℝ) : ℝ := Endpoint.adaptiveCount δ x + δ / 2 - 17 / 50

theorem row_slope_bounds {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    0 ≤ rowSlope δ x ∧ rowSlope δ x ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := adaptive_count_bounds hdlo hdhi hxlo hxhi
  unfold rowSlope
  constructor <;> linarith

end

end RH.Transport.Certificate

end

section
-- module Transport.TunedCertificate (LW56e2)
namespace RH.Transport.TunedCertificate

noncomputable section

theorem candidate_matches_endpoint :
    TunedCandidate.p = TunedEndpoint.perturbation ∧
    TunedCandidate.b = TunedEndpoint.b ∧
    TunedCandidate.B = TunedEndpoint.boundary ∧
    TunedCandidate.ell = TunedEndpoint.ell ∧
    TunedCandidate.ly = TunedEndpoint.ly ∧
    TunedCandidate.h = TunedEndpoint.h ∧
    TunedCandidate.cushion = TunedEndpoint.saving := by
  norm_num [TunedCandidate.p, TunedCandidate.b, TunedCandidate.B,
    TunedCandidate.boundaryAt, TunedCandidate.ell, Geometry.ell,
    TunedCandidate.ly, TunedCandidate.lyAt, TunedCandidate.h, TunedCandidate.hAt,
    TunedCandidate.cushion, TunedEndpoint.perturbation, TunedEndpoint.b,
    TunedEndpoint.boundary, TunedEndpoint.ell, TunedEndpoint.ly, TunedEndpoint.h,
    TunedEndpoint.saving]

def highExponent (d δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - TunedCandidate.B + TunedCandidate.h * (17 / 50 - 1 / 6) -
    ((1 + δ) / 2) * TunedCandidate.ly - TunedCandidate.ell / 2 +
    δ * x * TunedCandidate.ell + d * Certificate.rowSlope δ x

theorem high_exponent_endpoint (d δ x : ℝ) :
    highExponent d δ x = TunedEndpoint.endpointExponent δ x +
      (d - TunedCandidate.h) * Certificate.rowSlope δ x := by
  obtain ⟨_, _, hB, hell, hly, hh, _⟩ := candidate_matches_endpoint
  unfold highExponent TunedEndpoint.endpointExponent Certificate.rowSlope
  rw [hB, hell, hly, hh]
  simp only [TunedEndpoint.adaptiveCount]
  ring

/-- Bound on the entire buffered row interval for the tuned exponent. -/
theorem buffered_high_bound {d δ x : ℝ}
    (hd : d ≤ TunedCandidate.h + TunedCandidate.zeta)
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    highExponent d δ x ≤ -(3 / 4000000000000 : ℝ) := by
  have he := TunedEndpoint.adaptive_endpoint_bound hdlo hdhi hxlo hxhi
  obtain ⟨hs0, hs2⟩ := Certificate.row_slope_bounds hdlo hdhi hxlo hxhi
  have hm := mul_le_mul_of_nonneg_right
    (show d - TunedCandidate.h ≤ TunedCandidate.zeta by linarith) hs0
  have hz := mul_le_mul_of_nonneg_left hs2 TunedCandidate.zeta_pos.le
  rw [high_exponent_endpoint]
  norm_num [TunedCandidate.zeta] at hm hz
  linarith

end

end RH.Transport.TunedCertificate

end

section
-- module Transport.PhysicalHigh.TunedExponent (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section

open OAI OAI.SevenEighths

open ProbeHighRowFamily

def profileExponent (a e : ℝ) : ℝ :=
  TunedCandidate.lx * (4 / 25) + a + 16 * e - 33 / 50 -
    TunedCandidate.ly * (a + 6 * e)

def arithmeticExponent (N : ℕ) (a v d R q e eps loss mesh overhead : ℝ) : ℝ :=
  overhead + d * R + v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) +
    loss - (4 / 25) * TunedCandidate.ell + q * TunedCandidate.ell +
    mesh * TunedCandidate.ell

theorem tuned_physical_scale_identity (Z a e : ℝ) (hZ : 0 < Z) :
    (Z ^ TunedCandidate.lx) ^ (4 / 25 : ℝ) * Z ^ (a + 16 * e - 33 / 50) *
      (Z ^ TunedCandidate.ly) ^ (-a - 6 * e) = Z ^ profileExponent a e := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold profileExponent
  ring

theorem adaptiveRowExponent_zero {a q ε εm slot ν : ℝ} (ha : a ≤ 7 / 8) :
    adaptiveRowExponent (2 * a - 1) q 0 ε εm slot ν =
      RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) +
        (159 * ε + εm + slot + 7 * ν) := by
  have hd : 2 * a - 1 ≤ (5 / 6 : ℝ) := by linarith
  simp only [adaptiveRowExponent, if_pos hd, balanced_count_eq, zero_div, add_zero]
  ring

theorem tuned_accounting (N : ℕ) (a q v d countLoss e eps loss mesh overhead : ℝ)
    (ha : (1 / 2 : ℝ) < a) :
    profileExponent a e + arithmeticExponent N a v d
      (RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) + countLoss)
      q e eps loss mesh overhead =
    TunedCandidate.signal TunedCandidate.B +
      TunedCertificate.highExponent v (2 * a - 1) (q / (2 * a - 1)) +
      (d - v) * RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) +
      d * countLoss + e * (16 - 6 * TunedCandidate.ly) + 12 * v * e +
      v * eps * (N + 8) + loss + mesh * TunedCandidate.ell + overhead := by
  have hd : 2 * a - 1 ≠ 0 := by linarith
  have hq : (2 * a - 1) * (q / (2 * a - 1)) = q := mul_div_cancel₀ q hd
  unfold profileExponent arithmeticExponent TunedCertificate.highExponent
    Certificate.rowSlope
  rw [hq]
  unfold TunedCandidate.signal TunedCandidate.signalAt
    TunedCandidate.h TunedCandidate.hAt TunedCandidate.ly TunedCandidate.lyAt
    TunedCandidate.lx TunedCandidate.lxAt
  ring

theorem tuned_mixed_saving (N : ℕ) (a q v d countLoss μ e eps loss mesh overhead saving : ℝ)
    (ha : (51 / 100 : ℝ) < a) (ha' : a ≤ 7 / 8)
    (hq : 0 ≤ q) (hq' : q ≤ (2 * a - 1) / 2)
    (hv : v ≤ TunedCandidate.h + TunedCandidate.zeta) (hd : d ≤ 1)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) (hcount : 0 ≤ countLoss)
    (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : countLoss + μ + 26 * e + eps * (N + 8) + loss +
      mesh * TunedCandidate.ell + overhead + saving ≤ (3 / 4000000000000 : ℝ)) :
    profileExponent a e + arithmeticExponent N a v d
      (RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) + countLoss)
      q e eps loss mesh overhead ≤ TunedCandidate.signal TunedCandidate.B - saving := by
  have hδ : 0 < 2 * a - 1 := by linarith
  have hlo : (1 / 50 : ℝ) ≤ 2 * a - 1 := by linarith
  have hhi : 2 * a - 1 ≤ (3 / 4 : ℝ) := by linarith
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hq hδ.le
  have hx' : q / (2 * a - 1) ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hδ).mpr (by linarith)
  have hend := TunedCertificate.buffered_high_bound hv hlo hhi hx hx'
  obtain ⟨hRlo, hRhi⟩ := Certificate.adaptive_count_bounds hlo hhi hx hx'
  have hR0 : 0 ≤ RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) := by
    linarith
  have hdiff1 := mul_le_mul_of_nonneg_right hdv hR0
  have hdiff2 := mul_le_mul_of_nonneg_left hRhi hμ
  have hdiff : (d - v) * RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) ≤ μ := by
    linarith
  have hcount' := mul_le_mul_of_nonneg_right hd hcount
  have hv1 : v ≤ 1 := hv.trans TunedCandidate.buffered_upper_scale_lt_one.le
  have hly : (1 / 3 : ℝ) ≤ TunedCandidate.ly := by
    norm_num [TunedCandidate.ly, TunedCandidate.lyAt, TunedCandidate.ell,
      Geometry.ell, TunedCandidate.p, TunedCandidate.b]
  have hprofile := mul_le_mul_of_nonneg_left
    (show 16 - 6 * TunedCandidate.ly ≤ (14 : ℝ) by linarith) he
  have hve := mul_le_mul_of_nonneg_right hv1 he
  have hveps := mul_le_mul_of_nonneg_right hv1
    (show 0 ≤ eps * (N + 8) by positivity)
  rw [tuned_accounting N a q v d countLoss e eps loss mesh overhead (by linarith)]
  nlinarith only [hend, hdiff, hcount', hprofile, hve, hveps, hbudget]

end

end RH.Transport.PhysicalHigh

end

section
-- module Transport.PhysicalHigh.NonfloorClass (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section

open scoped Classical BigOperators Topology ContDiff

open Filter Set

open OAI OAI.SevenEighths

open ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
lemma nonfloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end

end RH.Transport.PhysicalHigh

end

section
-- module Transport.PhysicalHigh.NonfloorArithmetic (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section

open scoped Classical BigOperators Topology ContDiff

open Filter Set

open OAI OAI.SevenEighths

open ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0< τ) (hε : 0< ε) (hκ : 0< κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=TunedCandidate.ell)
    (hsupply : (7/37:ℝ)*dmax≤ TunedCandidate.ell) (hdmax1 : dmax≤1) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤ φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0< εm) (hν : 0< ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (μ saving : ℝ) (hμ : 0≤ μ)
    (hfinal : (159*ε+εm+R+7*ν)+μ+
      (26*e+(N+8)*eps+loss+mesh*TunedCandidate.ell)+
      (logCost+heightCost+momentCost)+saving≤3/4000000000000)
    (counts : ProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ TunedCandidate.h+TunedCandidate.zeta → d-v≤ μ →
      51/100< a → a≤7/8 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) 0
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(TunedCandidate.signal TunedCandidate.B-saving-profileExponent a e) := by
  obtain ⟨C,hC,hclass⟩ :=
    actual_nonfloor_class_from_raw_moments M H hH TunedCandidate.ell
      (by norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]) N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hsupply hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm 0 ν logCost heightCost momentCost hεm (by norm_num) (by norm_num) hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0≤ cardCost := by dsimp [cardCost];positivity
  refine ⟨(cardCost+1)*C,by positivity,?_⟩
  intro η
  filter_upwards [hclass η,eventually_gt_atTop (1:ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(TunedCandidate.signal TunedCandidate.B-saving-profileExponent a e)
  have hb : 0≤ bound := by dsimp [bound];positivity
  have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
    (nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
    (by linarith) (fun j=>ell j/d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha (by linarith) hC0 rows hrows hnorm i hi hnext hcurrent t ht hmom bin hne
      dsimp only at hp
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
      rw [adaptiveRowExponent_zero ha'] at hp
      have hs := tuned_mixed_saving N a q v d (159*ε+εm+R+7*ν) μ e eps loss mesh
        (logCost+heightCost+momentCost) saving ha ha' hp.1 hp.2.1 hv'
        (hd'.trans hdmax1) hμ hdv (by positivity) he.le heps.le (by nlinarith [hfinal])
      unfold profileExponent arithmeticExponent at hs
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      unfold profileExponent
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost*bound := hpart
    _ ≤ (cardCost+1)*bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound];ring

end

end RH.Transport.PhysicalHigh

end

section
-- module Transport.PhysicalHigh.NonfloorIntegral (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section

open scoped Classical BigOperators Topology ContDiff

open Filter Set

open OAI OAI.SevenEighths

open ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_cube_norm_t (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0< τ) (hε : 0< ε) (hκ : 0< κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=TunedCandidate.ell)
    (hsupply : (7/37:ℝ)*dmax≤ TunedCandidate.ell) (hdmax1 : dmax≤1) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤ φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0< εm) (hν : 0< ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (μ saving : ℝ) (hμ : 0≤ μ)
    (hfinal : (159*ε+εm+R+7*ν)+μ+
      (26*e+(N+8)*eps+loss+mesh*TunedCandidate.ell)+
      (logCost+heightCost+momentCost)+saving≤3/4000000000000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (counts : ProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ TunedCandidate.h+TunedCandidate.zeta → d-v≤ μ →
      51/100< a → a≤7/8 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) 0
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y
        W0 W1 (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(TunedCandidate.signal TunedCandidate.B-saving) := by
  obtain ⟨C,hC,harith⟩ :=
    actual_nonfloor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hsupply hdmax1 hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm ν logCost heightCost momentCost hεm hν hlog hMomentHeight
      μ saving hμ hfinal counts
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro η
  filter_upwards [harith η,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z harith hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro hmom
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let A : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(TunedCandidate.signal TunedCandidate.B-saving-(profileExponent a e))
  have hA : 0≤ A := by dsimp [A];positivity
  have hp := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha.le (by linarith) hT
    (by gcongr;omega) S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1)
    T (nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hnext W Y
    (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z (by positivity) (by positivity) hZp A hA
    (fun t ht=>harith d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
      t ht (hmom t ht))
  apply hp.trans_eq
  rw [tuned_physical_scale_identity Z a e hZp]
  dsimp only [A]
  calc
    _ = (D*C)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
        (Z^(profileExponent a e)*Z^(TunedCandidate.signal TunedCandidate.B-saving-(profileExponent a e))) := by ring
    _ = _ := by rw [←Real.rpow_add hZp];congr 2;ring

end

end RH.Transport.PhysicalHigh

end

theorem solution : type_of% @RH.Transport.PhysicalHigh.actual_nonfloor_cube_norm_t := @RH.Transport.PhysicalHigh.actual_nonfloor_cube_norm_t
