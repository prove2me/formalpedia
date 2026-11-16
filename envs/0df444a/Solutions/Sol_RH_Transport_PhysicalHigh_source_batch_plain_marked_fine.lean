-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.source_batch_plain_marked_fine
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T14:55:10.8092+00:00
-- url     : https://prove2.me/submissions/ae1b57e2-2dee-45e5-a0f5-055323abca87

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028
import Definitions.Def_Transport_PhysicalHigh_PositiveFineSourceInput
import Theorems.Thm_OAI_SevenEighths_CenteredMomentDetectorPlainExceptional_retained_positive_energy_le_source
import Theorems.Thm_OAI_SevenEighths_CenteredMomentDetectorPlainExceptional_source_batch_plain_retained
set_option autoImplicit false

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier
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

namespace ActualEisensteinCubic

theorem quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa only [map_ofNat, Nat.cast_ofNat] using hz)

end ActualEisensteinCubic

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
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CubeLabels
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

namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open QuadraticSquarefreeKernel

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

end QuadraticMainBoundary

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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end JointLogSeparation

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Operations
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

theorem row_ideal_dvd (S : Finset (Ideal O)) {u : O} (hu : u ∈ rows S) :
    (Ideal.span {u} : Ideal O) ∣ (∏ P ∈ S, P)^5 := by
  have hI : (Ideal.span {u} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hu.1
  have hle : normalizedFactors (Ideal.span {u}) ≤ 5 • S.val := by
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {u})
    · have hp := hu.2 P hP
      have hc : S.val.count P = 1 := Multiset.count_eq_one_of_mem S.nodup hp.1
      rw [Multiset.count_nsmul, hc]
      omega
    · simp only [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  have hd := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self hI, Multiset.prod_nsmul] at hd
  change (Ideal.span {u} : Ideal O) ∣ (S.prod id)^5
  simpa only [Finset.prod_val] using hd

theorem row_norm_bound (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    {u : O} (hu : u ∈ rows S) : (Ideal.span {u}).absNorm ≤ bound S := by
  have hd := map_dvd Ideal.absNorm (row_ideal_dvd S hu)
  apply Nat.le_of_dvd _ hd
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Ideal.absNorm_eq_zero_iff]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero))

end SevenEighths.HeckeExceptionalRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem split_at_prime (I P : Ideal O) (hI : I ≠ 0) [P.IsMaximal] :
    ∃ J : Ideal O, I = P ^ valuation I P * J ∧ J ≠ 0 ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ valuation I Q
  have hsplit : I = P ^ valuation I P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
      _ = ∏ Q ∈ S, Q ^ valuation I Q := Finset.prod_multiset_count _
      _ = P ^ valuation I P * J := by
        by_cases hP : P ∈ S
        · exact (Finset.mul_prod_erase S (fun Q => Q ^ valuation I Q) hP).symm
        · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
            (fun h => hP (Multiset.mem_toFinset.mpr h))
          simp only [J, Finset.erase_eq_of_notMem hP, hz, pow_zero, one_mul]
  refine ⟨J, hsplit, ?_, ?_⟩
  · intro hz
    apply hI
    rw [hsplit, hz, mul_zero]
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hp := prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

theorem exists_unit_probe (Q K P : Ideal O) (hK : K ≠ 0) [P.IsMaximal]
    (hQP : IsCoprime Q P) (u : (O ⧸ P)ˣ) :
    ∃ n : O, n - 1 ∈ Q ∧ IsCoprime (Ideal.span {n}) K ∧
      Ideal.Quotient.mk P n = (u : O ⧸ P) := by
  obtain ⟨J, hsplit, hJ, hJP⟩ := split_at_prime K P hK
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) P (hQP.mul_left hJP)
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk P n) = (1, (u : O ⧸ P)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnJ : Ideal.Quotient.mk J n = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn)
  have hcJ : IsCoprime (Ideal.span {n}) J :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnJ ▸ isUnit_one)
  have hcP : IsCoprime (Ideal.span {n}) P :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnP ▸ u.isUnit)
  refine ⟨n, Ideal.mul_le_left hn, ?_, hnP⟩
  rw [hsplit]
  exact hcP.pow_right.mul_right hcJ

theorem valuation_mod_six_of_unit_agreement (Q K I J P : Ideal O)
    (hK : K ≠ 0) (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (heq : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      idealRowHom n I = idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  obtain ⟨I₀, hsplitI, hI₀, hcI⟩ := split_at_prime I P hI.1
  obtain ⟨J₀, hsplitJ, hJ₀, hcJ⟩ := split_at_prime J P hJ.1
  have hsI : CanonicalQuadraticSieve.Supported I₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitI ▸ hI)).2
  have hsJ : CanonicalQuadraticSieve.Supported J₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitJ ▸ hJ)).2
  have hpows : actualSextic P hg ^ valuation I P = actualSextic P hg ^ valuation J P := by
    apply MulChar.ext
    intro u
    obtain ⟨n, hn, hcK, hnP⟩ := exists_unit_probe (Q * I₀ * J₀) K P hK
      ((hQP.mul_left hcI).mul_left hcJ) u
    have hval := heq n (Ideal.mul_le_left (Ideal.mul_le_left hn)) hcK
    have hIn : n - 1 ∈ I₀ := Ideal.mul_le_right (Ideal.mul_le_left hn)
    have hJn : n - 1 ∈ J₀ := Ideal.mul_le_right hn
    rw [hsplitI, hsplitJ, map_mul, map_mul, map_pow, map_pow,
      idealRowHom_congr_mod I₀ n 1 hIn, idealRowHom_congr_mod J₀ n 1 hJn,
      idealRowHom_one_supported I₀ hsI, idealRowHom_one_supported J₀ hsJ,
      mul_one, mul_one, idealRowHom_prime n P hg, hnP] at hval
    simpa only [MulChar.pow_apply_coe] using hval
  have hm := (pow_eq_pow_iff_modEq.mp hpows)
  rw [actualSextic_order_six P hg hchar] at hm
  exact hm

theorem elementCoeff_eq_one_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hψ : Q ≤ ψ.modulus)
    (n : O) (hn : n - 1 ∈ Q) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = 1 := by
  have hn0 : n ≠ 0 := by
    intro hz
    have h1 : (1 : O) ∈ Q := by simpa [hz] using Q.neg_mem hn
    exact hQ ((Ideal.eq_top_iff_one Q).mpr h1)
  rw [elementCoeff_eq_of_inducedBy χ ψ h n hn0 hc]
  change ψ.residue (Ideal.Quotient.mk ψ.modulus n) = 1
  rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (hψ hn), map_one]

theorem actual_row_on_fixed_units (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1)
    (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (n : O) (hn : n - 1 ∈ Ideal.span {(72 : O)})
    (hc : IsCoprime (Ideal.span {n}) (Ideal.span {m})) :
    elementCoeff χ n = elementCoeff η n * idealRowHom n (Ideal.span {r}) := by
  have hd72 : λ₀ ^ 2 ∣ (72 : O) := ActualEisensteinCubic.lambda_sq_dvd_three.trans
    (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩)
  have hp : λ₀ ^ 2 ∣ n - 1 := hd72.trans (Ideal.mem_span_singleton.mp hn)
  rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hp]
  change ((elementCoeff η n * coprimalityMask m n) * numeratorBadTwist u a b r hr n) *
    idealRowHom n (Ideal.span {r}) = _
  have hm : coprimalityMask m n = 1 := by
    change (if IsCoprime m n then (1 : ℂ) else 0) = 1
    simp only [((Ideal.isCoprime_span_singleton_iff _ _).mp hc).symm, ite_true]
  rw [hm, numeratorBadTwist_periodic u a b r hr n 1 hn, map_one, mul_one, mul_one]

theorem valuation_span_eq_zero_of_not_mem (x : O) (P : Ideal O) (hx : x ∉ P) :
    valuation (Ideal.span {x}) P = 0 := by
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ P.zero_mem)
  apply Multiset.count_eq_zero.mpr
  intro hP
  have hle := ((Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr hx0)).mp hP).2
  exact hx (hle (Ideal.subset_span (by simp)))

theorem valuation_supported_numerator (x : O) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : r ≠ 0) (hx : x = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P : Ideal O) (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P) :
    valuation (Ideal.span {x}) P = valuation (Ideal.span {r}) P := by
  have hu : Ideal.span {(u : O)} = (1 : Ideal O) := by
    simpa only [Ideal.one_eq_top] using (Ideal.span_singleton_eq_top.mpr u.isUnit)
  have hl0 : Ideal.span {λ₀} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have h20 : Ideal.span {(2 : O)} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hr0 : Ideal.span {r} ≠ (0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hr
  rw [hx]
  simp only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu, one_mul]
  rw [valuation_mul _ _ _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ h20)) hr0,
    valuation_mul _ _ _ (pow_ne_zero _ hl0) (pow_ne_zero _ h20), valuation_pow, valuation_pow,
    valuation_span_eq_zero_of_not_mem λ₀ P hg, valuation_span_eq_zero_of_not_mem (2 : O) P h2]
  omega

theorem local_row_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q K I P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ : Q ≤ ψ.modulus) (hI : CanonicalQuadraticSieve.Supported I)
    [P.IsMaximal] (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hrow : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ n = elementCoeff η n * idealRowHom n I) :
    valuation I P % 6 = 0 := by
  have hzero : valuation (1 : Ideal O) P % 6 = 0 := by
    simp only [valuation, normalizedFactors_one, Multiset.count_zero, Nat.zero_mod]
  rw [← hzero]
  apply valuation_mod_six_of_unit_agreement (Q * η.modulus) (K * χ.modulus) I 1 P
    (mul_ne_zero hK χ.modulus_ne_bot) hI
    (by constructor; exact one_ne_zero; simp only [normalizedFactors_one, Multiset.notMem_zero, false_implies, implies_true]) hg hchar
    (hQP.mul_left hηP)
  intro n hn hc
  obtain ⟨hcK, hcχ⟩ := IsCoprime.mul_right_iff.mp hc
  have hnQ := Ideal.mul_le_left hn
  have hη : elementCoeff η n = 1 := by
    change η.residue (Ideal.Quotient.mk η.modulus n) = 1
    rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn), map_one]
  have he := elementCoeff_eq_one_of_inducedBy χ ψ h Q hQ hψ n hnQ hcχ
  rw [hrow n hnQ hcK, hη, one_mul] at he
  simpa only [map_one] using he

theorem actual_row_numerator_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m f z : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P) :
    valuation (Ideal.span {f ^ 4 * z}) P % 6 = 0 := by
  obtain ⟨u, a, b, r, hr, hpr, hx⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z) (mul_ne_zero (pow_ne_zero _ hf) hz)
  rw [valuation_supported_numerator _ u a b r (Ideal.span_singleton_eq_bot.not.mp hr.1) hx P hg h2]
  apply local_row_valuation_zero η χ ψ h Q (Ideal.span {m}) (Ideal.span {r}) P hQ
    (Ideal.span_singleton_eq_bot.not.mpr hm) hψ hr hg
    (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP hηP
  intro n hn hc
  exact actual_row_on_fixed_units η χ m f z hmLam hm2 u a b r hr hpr hx hχ n (hQ72 hn) hc

theorem outside_fixed_support (Q : Ideal O) (hQ : Q ≠ 0)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (P : Ideal O) (hP : Prime P)
    (hPS : P ∉ (normalizedFactors Q).toFinset) :
    λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := (inferInstance : P.IsMaximal).eq_of_le hJ.ne_top hPJ
    apply hPS
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hQ).mpr
    exact ⟨Ideal.isPrime_of_prime hP, hPJ' ▸ hQJ⟩
  have h72 : (72 : O) ∉ P := by
    intro hh
    have hle : Q ≤ P := hQ72.trans ((Ideal.span_singleton_le_iff_mem _).mpr hh)
    have he := Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [sup_eq_right.mpr hle] at he
    exact hP.ne_one (by simpa only [Ideal.one_eq_top] using he)
  have hl : λ₀ ∣ (72 : O) :=
    (dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans
      (ActualEisensteinCubic.lambda_sq_dvd_three.trans (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩))
  have h2 : (2 : O) ∣ 72 := ⟨36, by norm_num⟩
  refine ⟨?_, ?_, hcop⟩
  · intro hh
    obtain ⟨v, hv⟩ := hl
    exact h72 (hv ▸ P.mul_mem_right v hh)
  · intro hh
    obtain ⟨v, hv⟩ := h2
    exact h72 (hv ▸ P.mul_mem_right v hh)

end SevenEighths.CenteredExceptionalProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Mask
namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem annular_ideal_sum_summable (χ : Ideal O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

end SevenEighths.CenteredMomentMask
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicProfiles
namespace OAI

noncomputable section

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open CubicReflectionKernel
theorem section_deriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : (ℝ × ℝ) × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (_root_.OAI.SevenEighths.HeckeDyadic.shift σ freq)=_root_.OAI.SevenEighths.HeckeDyadic.shift σ (-freq) := by
  simp only [HeckeDyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.RayQuotient
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

attribute [local instance] OAI.SevenEighths.HeckeRayQuotient.instFiniteQuotientOIdeal_solutions
attribute [local instance] OAI.SevenEighths.HeckeRayQuotient.instIsPrincipalIdealRingO_solutions
theorem idealCoeff_character (χ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (character M H hH χ) I = RayQuotient.idealCharacter M H hH χ I := rfl

end SevenEighths.HeckeRayQuotient

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeRow
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r9b5e29_1 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance instIsPrincipalIdealRingO_solutions_r9b5e29_1 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
omit [NeZero M] in
theorem identityClass_coprime {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    IsCoprime I M := by
  obtain ⟨hI,a,ha,u,hu,huH⟩ := hI
  rw [←ha]
  exact (IdealCharacter.isUnit_mk_iff_isCoprime M a).mp (hu ▸ u.isUnit)

omit [NeZero M] in
theorem identityClass_coprime_larger {I J : Ideal O}
    (hI : I∈RayQuotient.identityClass M H) (hMJ : M≤J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hI)]
  exact sup_le_sup_left hMJ I

omit [NeZero M] in
theorem identityClass_prime_good (m : O) (hmLam : λ₀∣m) (hMm : M≤Ideal.span {m})
    (P : Ideal O) [P.IsMaximal] (hP : P∈RayQuotient.identityClass M H) : λ₀∉P := by
  have hm : m∉P := (SixthPowerAverage.prime_coprime_span_iff P m).mp
    (identityClass_coprime_larger M H hP hMm)
  intro hLam
  obtain ⟨a,rfl⟩ := hmLam
  exact hm (P.mul_mem_right a hLam)

end SevenEighths.HeckePrimeRow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

theorem idealCoeff_inverse (ν : Character) (J : Ideal O) :
    idealCoeff ν.inverse J=(idealCoeff ν J)⁻¹ := by
  by_cases hJ : J=0
  · subst J
    simp only [map_zero,inv_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν.inverse hg,
    idealCoeff_span ν hg,HeckeFamily.elementCoeff_inverse]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Extraction
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealRectangle_extract (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealRectangle W₁ W₂
        (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
        (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp only [idealRectangle, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  congr 2 <;> congr 1 <;> ring

end SevenEighths.CenteredMomentExtraction
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,mul_assoc]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeHeight
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open CenteredMomentLattice CenteredMomentTwist
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem rowTwistedSum_eq (η χ : Character) (m A₀ z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]

end SevenEighths.CenteredMomentHeckeHeight

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

theorem rowTwistedSum_eq_weight (η : Character) (m A z : O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
    (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem live_slot_product (η : Character) (m A z : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (t : ℝ) :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_norm_sq (T : ℝ) (hT : 0 < T) (x : ℂ) :
    ‖(Real.sqrt T:ℂ)⁻¹*x‖^2=‖x‖^2/T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt hT.le]
  ring

end SevenEighths.CenteredMomentDivisorRawEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_split (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

end SevenEighths.CenteredMomentSourceRow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [if_pos hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

end SevenEighths.CenteredMomentSecondHeightFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SlotNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤X) (hP:∀i,0≤P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (fun i _=>hP i),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤X₁*X₂) (hP:∀i,0≤P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  calc
    _=((Real.sqrt (X₁*X₂):ℂ)⁻¹*(∏i,(Real.sqrt (P i):ℂ)⁻¹))*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏i,rowSlot η m A z (S i) (β i) t) := by ring
    _=_ := by rw [he]

end SevenEighths.CenteredMomentSlotNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,idealCoeff χ I*W ((I.absNorm:ℝ)/X) at he
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,HeckeDyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

theorem plain_polynomial_eq_row (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (X σ t : ℝ) (hX : 0<X) :
    polynomial χ false W X σ t = (Real.sqrt X:ℂ)⁻¹*
      rowTwistedSum η m A z (twistProfile W σ t) 0 X := by
  rw [←polynomial_twistProfile,plain_zero_height _ _ X hX,rowTwistedSum_eq η χ m A z hrow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveSlotRow_eq_product
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t) S β P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,normalizedSlot η m A z (S i) (β i) 0 (P i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open HeckeDetectorRelativePrime
local notation "O" => HeckeFamily.O

theorem physical_slot_conj (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η : Character) (m u : O) (hmLam : ConcretePrimeRowBridge.goodLambda∣m)
    (hMm : M≤Ideal.span {m}) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) (hD : 0<D)
    (hη : ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus) :
    normalizedSlot η m 1 u (primePool M H b D) (physicalSlotCoefficient η W D z) 0 D=
      conj (HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z) := by
  unfold normalizedSlot rowSlot HeckePrimeRow.canonicalPrimeAmplitude
  rw [←sqrt_inverse_cpow D hD,map_mul]
  simp only [map_inv₀,Complex.conj_ofReal,Complex.ofReal_zero,one_mul,mul_zero,Complex.cpow_zero,mul_one,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hP' : P∈primePool M H b D := hP
  obtain ⟨_,hp,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H m hmLam hMm P hclass
  have hcop := HeckePrimeRow.identityClass_coprime_larger M H hclass hMm
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,if_pos hcop,one_mul]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp only [physicalSlotCoefficient,hw,zero_mul,map_zero,mul_zero,zero_mul]
  · have hn := idealCoeff_ne_zero_of_coprime η P hp.ne_zero (hη P hP' hw)
    simp only [physicalSlotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,map_mul,starRingEnd_self_apply]
    field_simp

lemma physicalSlotCoefficient_annular (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ)
    (P : Ideal O) (hP : P≠0) (hD : 0<D) :
    physicalSlotCoefficient η W D z P=idealCoeff η.inverse P*
      HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) P := by
  have hn : 0<(P.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  unfold physicalSlotCoefficient HeckePrimeAnnular.annularWeight
  rw [map_mul,HeckeInverseAmplification.conj_positive_cpow _ (div_pos hn hD)]
  have he : conj (z-1)= -HeckeDyadic.shift (1-z.re) (-z.im) := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  rw [he]

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRows
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ψ : Character) (m u : O) (reverse : Bool)
    (hrow : ∀n,elementCoeff ψ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (1*u) n)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then conj (idealCoeff ψ I) else idealCoeff ψ I)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hMm : M≤Ideal.span {m})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η m 1 u
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  rw [positiveSlotRow_eq_product η ψ m 1 u hrow _ _ _ _ P _ _ _ _ hX₁ hX₂ hP]
  simp only [norm_mul,norm_prod]
  rw [norm_of_oriented_coefficients χ ψ reverse hc false W₁ X₁ σ t hX₁,
    norm_of_oriented_coefficients χ ψ reverse hc false W₂ X₂ σ t hX₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_slot_conj M H η m u hmLam hMm (V i) (b i) (P i) (external i) (hP i) (hη i),RCLike.norm_conj]

theorem momentData_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then
      conj (idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
      else idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
    (hMm : M≤Ideal.span {ProbeHighRowFamily.rowMaskElement})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η ProbeHighRowFamily.rowMaskElement 1 u.val
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  apply source_plain_pair_norm M H η χ
    ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u))
    ProbeHighRowFamily.rowMaskElement u.val reverse _ hc (dvd_mul_left _ _) hMm
    W₁ W₂ V b P external X₁ X₂ σ t hX₁ hX₂ hP hη
  intro n
  simpa only [ProbeHighRowFamily.momentData,ProbeHighRowFamily.momentElement,one_mul] using
    (ProbeHighRowFamily.momentData η).character_spec (ProbeHighRowFamily.momentElement u) n

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem Witness.left_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.r=Real.logb U ((2 : ℝ)^w.left.val) := by
  rw [←w.left_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem Witness.right_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.m=Real.logb U ((2 : ℝ)^w.right.val) := by
  rw [←w.right_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

theorem fiber_lengths {Row Label : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (χ : Row→Label→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (J K : Fin (dyadicLength U))
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    tstar-r-ε≤ m ∧ r≤tstar+ε ∧ m≤1/2+75*ε ∧ tstar-1/2-76*ε≤ r ∧ 0≤ m := by
  obtain ⟨u,hu⟩ := hne
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by
    rw [(w u).toWitness.left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by
    rw [(w u).toWitness.right_exponent hU,hK u hu]
  exact hr ▸ hm ▸ ⟨(w u).product_length_lower,(w u).inverse_length_upper,
    (w u).plain_length_upper,(w u).inverse_length_lower,(w u).plain_length_lower⟩

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryFiber
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_plain_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have hc := F.row_coeff u hu
  rw [hdata] at hc
  have he := momentData_plain_pair_norm M H η (F.family u F.label) u F.reverse hc hMm
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular)
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    (U^F.m) (U^F.m) σ t (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
    (fun s=>Real.rpow_pos_of_pos hU _) (fun s=>hη s.val s.property)
  have hprod := Finset.prod_coe_sort selected (fun s=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val
    (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s))
  rw [hprod] at he
  simpa only [detectorPositiveRow,Fiber.physicalProduct,HeckeDetectorPhysicalSelection.physical,
    Finset.prod_coe_sort] using he

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySupport
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma annular_prime_coprime (η : Character) (a D : ℝ) (ha : 0<a) (hD : 0<D)
    (hlarge : (η.modulus.absNorm:ℝ)/a<D)
    (W : ℝ→ℂ) (hs : Function.support W⊆Set.Ici a)
    (P : Ideal O) (hp : Prime P) (hW : W ((P.absNorm:ℝ)/D)≠0) :
    IsCoprime P η.modulus := by
  apply ProbeRaySlots.prime_coprime_of_norm_gt η ⟨P,hp⟩
  have hlo : a*D≤(P.absNorm:ℝ) := (le_div_iff₀ hD).mp (hs hW)
  have hh : (η.modulus.absNorm:ℝ)<a*D := by
    have hh := (div_lt_iff₀ ha).mp hlarge
    nlinarith
  exact hh.trans_le hlo

theorem eventually_primePool_coprime (η : Character) (a : ℝ) (ha : 0<a) :
    ∀ᶠD : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a)] with D hD hlarge
  intro M H W b hs P hP hW
  exact annular_prime_coprime η a D ha hD hlarge W hs P (Finset.mem_filter.mp hP).2.1 hW

theorem eventually_primePool_power_coprime (η : Character) (a ell : ℝ) (ha : 0<a) (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b (Z^ell),W ((P.absNorm:ℝ)/(Z^ell))≠0→IsCoprime P η.modulus :=
  (tendsto_rpow_atTop hell).eventually (eventually_primePool_coprime η a ha)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma source_product_le_rowMask (S : Finset (Ideal O))
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) :
    (∏P∈S,P)≤Ideal.span {rowMaskElement} := by
  apply Ideal.dvd_iff_le.mp
  have hne : (Ideal.span {ConcretePrimeRowBridge.goodLambda}:Ideal O)≠Ideal.span {(2:O)} := by
    intro he
    have hh : CanonicalQuadraticSieve.badPrime false=CanonicalQuadraticSieve.badPrime true := he
    have hh := CanonicalQuadraticSieve.badPrime_injective hh
    cases hh
  have hd := Finset.prod_dvd_prod_of_subset CanonicalQuadraticSieve.fixedBadPrimes S (fun P : Ideal O=>P) hbad
  have he : (∏P∈CanonicalQuadraticSieve.fixedBadPrimes,P)=Ideal.span {rowMaskElement} := by
    change (∏P∈({Ideal.span {ConcretePrimeRowBridge.goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O)),P)=_
    rw [Finset.prod_pair hne]
    unfold rowMaskElement
    rw [←Ideal.span_singleton_mul_span_singleton]
    exact mul_comm _ _
  rwa [he] at hd

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentDetectorDictionary.instFiniteQuotientOIdeal_solutions
lemma sourceMomentData_base (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (j : Sum Bool (RayQuotient.Characters M H)) :
    sourceMomentData M H hH S hS η j=momentData (sourceMomentBase M H hH S hS η j) := by
  rcases j with b|θ
  · cases b <;> rfl
  · rfl

theorem eventually_source_slots_coprime {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (ell : Fin N→ℝ) (hell : ∀i,0<ell i) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀d : ℝ,d≠0→∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b ((Z^d)^(ell i/d)),
        W ((P.absNorm:ℝ)/((Z^d)^(ell i/d)))≠0→
          IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
  have he : ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b (Z^(ell i)),W ((P.absNorm:ℝ)/(Z^(ell i)))≠0→
        IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [eventually_primePool_power_coprime (sourceMomentBase M H hH S hS η j)
      a (ell i) ha (hell i)] with Z hz
    exact hz M H
  filter_upwards [he,eventually_ge_atTop (0:ℝ)] with Z hz hZ
  intro j i d hd W b hs
  have heq : (Z^d)^(ell i/d)=Z^(ell i) := by
    rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]
  rw [heq]
  exact hz j i W b hs

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UncenteredTerminal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentUncenteredTerminal
open HeckeFamily CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma comparisonScale_pos (b : ℝ) : 0<comparisonScale b := by
  have hb : 0< max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  unfold comparisonScale
  positivity

theorem comparison_first_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (B I : Ideal O) (hB : B≠0) :
    W ((Ideal.absNorm (B*I):ℝ)/comparisonScale b)=0 := by
  by_contra h
  have ht := hs h
  by_cases hI : I=0
  · simp only [hI,mul_zero,map_zero,Nat.cast_zero,zero_div,Set.mem_Icc] at ht
    linarith [ht.1]
  have hn : 1≤(Ideal.absNorm (B*I):ℝ) :=
    QuadraticMainBoundary.norm_one_le (mul_ne_zero hB hI)
  have hmax : 1≤ max 1 b := le_max_left _ _
  have hb : b≤ max 1 b := le_max_right _ _
  have harg : (Ideal.absNorm (B*I):ℝ)/comparisonScale b=
      (Ideal.absNorm (B*I):ℝ)*(2*max 1 b) := by
    simp [comparisonScale,div_eq_mul_inv]
  rw [harg] at ht
  have hupper := ht.2
  nlinarith

theorem profileCoefficient_eq_uncentered {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ : ℝ) (ha₁ : 0<a₁)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (X₁ X₂ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hB₁ : B₁≠0) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) Y₂ B₁ B₂ s=
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ s := by
  funext v
  simp only [profileCoefficient,idealRectangle,
    comparison_first_zero W₁ a₁ b₁ ha₁ hs₁ B₁ (v (Sum.inr 0)) hB₁,
    zero_mul,sub_zero,uncenteredProfileCoefficient]

end SevenEighths.CenteredMomentUncenteredTerminal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangle
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangle
open ActualEisensteinCubic HeckeFamily CenteredMomentHeckeExpansion CenteredMomentRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentExtraction CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentRemainingBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem pack_product (v : ι→Ideal O) (I J : Ideal O) :
    finiteTupleProduct (pack v I J)=(∏ i,v i)*I*J := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,pack_slot,Fin.prod_univ_two,
    pack_left,pack_right,mul_assoc]

theorem sum_tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (f : Tuple ι→ℂ) :
    (∑ v∈tuplePool slots S₁ S₂,f v)=
      ∑ v : (∀ i,slots i),∑ I : S₁,∑ J : S₂,f (pack (fun i=>v i) I J) := by
  rw [← Finset.sum_coe_sort (tuplePool slots S₁ S₂) f]
  have he := (tuplePoolEquiv slots S₁ S₂).symm.sum_comp (fun v : tuplePool slots S₁ S₂=>f v)
  change (∑ x : ((∀ i,slots i)×S₁×S₂),f (pack (fun i=>x.1 i) x.2.1 x.2.2))=
    (∑ v : tuplePool slots S₁ S₂,f v) at he
  simpa only [Fintype.sum_prod_type] using he.symm

theorem finite_column_regroup (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (w : Ideal O→ℂ) :
    (∑ I∈finiteColumns S,finiteColumnCoefficient S β I*w I)=
      ∑ v∈S,β v*w (finiteTupleProduct v) := by
  simp only [finiteColumnCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I∈finiteColumns S,∑ v∈S.filter (fun v=>finiteTupleProduct v=I),
        β v*w (finiteTupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

theorem rectangle_zero_left (S₁ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (I J : Ideal O) (hI : I∉S₁) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₁ ((Ideal.absNorm (B₁*I):ℝ)/X₁)=0 := by
    by_contra hn;exact hI (h I (Or.inl hn))
  have hy : W₁ ((Ideal.absNorm (B₁*I):ℝ)/Y₁)=0 := by
    by_contra hn;exact hI (h I (Or.inr hn))
  simp only [idealRectangle,hx,hy,zero_mul,sub_self]

theorem rectangle_zero_right (S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₂ W₂ B₂ X₂ Y₂) (I J : Ideal O) (hJ : J∉S₂) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₂ ((Ideal.absNorm (B₂*J):ℝ)/X₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inl hn))
  have hy : W₂ ((Ideal.absNorm (B₂*J):ℝ)/Y₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inr hn))
  simp only [idealRectangle,hx,hy,mul_zero,sub_self]

theorem finite_plain_rectangle (S₁ S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (f : Ideal O→Ideal O→ℂ) :
    (∑ I : S₁,∑ J : S₂,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))=
      ∑' I : Ideal O,∑' J : Ideal O,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) := by
  symm
  rw [tsum_eq_sum (s := S₁)]
  · rw [← Finset.sum_coe_sort S₁ (fun I=>∑' J : Ideal O,
      f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))]
    apply Finset.sum_congr rfl
    intro I hI
    rw [tsum_eq_sum (s := S₂)]
    · exact (Finset.sum_coe_sort S₂ _).symm
    · intro J hJ
      rw [rectangle_zero_right S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₂ I J hJ,mul_zero]
  · intro I hI
    simp only [rectangle_zero_left S₁ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ I _ hI,mul_zero,tsum_zero]

theorem source_polynomial_eq_full_masked_rectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [finite_column_regroup,sum_tuplePool]
  unfold fullMaskedRectangle
  apply Finset.sum_congr rfl
  intro v hv
  rw [← finite_plain_rectangle S₁ S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ h₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [profileCoefficient,pack_product,pack_slot,pack_left,pack_right]
  ring

theorem fullMaskedRectangle_modulus_one [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot 1 L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ =
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  simp only [fullMaskedRectangle,CenteredMomentDivisorRowEnergy.maskedRectangle,
    isCoprime_one_right,ite_true,one_mul,idealRectangle_extract]
  apply Finset.sum_congr (by ext; simp)
  intro v hv
  rfl

theorem source_polynomial_eq_maskedRectangle [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient 1 ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ 1 L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_modulus_one η m A z t slots ν _ L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)

end SevenEighths.CenteredMomentSourceRectangle

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRectangleMask
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSourceRectangle
open CenteredMomentDivisorRowEnergy CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_ideal_mask (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (R I : Ideal O) :
    (if IsCoprime I R then (1:ℂ) else 0)*rowWeight η m A z t I=
      rowWeight η (m*idealGenerator R) A z t I := by
  by_cases hI : Supported I
  · have hm : (m*idealGenerator R)^6*(A*z)=(idealGenerator R)^6*(m^6*(A*z)) := by ring
    change (if IsCoprime I R then (1:ℂ) else 0)*
      ((idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))=
      (idealCoeff η I*idealRowHom ((m*idealGenerator R)^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)
    rw [hm,idealRowHom_argument_mul ((idealGenerator R)^6) (m^6*(A*z)) I,
      idealRowHom_sixth_mask (idealGenerator R) I hI,span_idealGenerator]
    ring
  · rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hI,
      rowWeight_zero_of_not_supported η (m*idealGenerator R) A z t
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) I hI,mul_zero]

theorem fullMaskedRectangle_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  unfold fullMaskedRectangle maskedRectangle
  apply Finset.sum_congr (by ext;simp)
  intro v hv
  congr 1
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [idealRectangle_extract]
  rw [mul_right_comm (if IsCoprime _ R then (1:ℂ) else 0) _,rowWeight_ideal_mask η m A z t hmLam hm2]
  ring

theorem source_polynomial_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈CenteredMomentSourceMass.finiteColumns (tuplePool slots S₁ S₂),
      CenteredMomentSourceMass.finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (CenteredMomentSourceProfileMass.profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ R L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_eq_maskedRectangle η m A z t hmLam hm2 slots ν _ R L W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂)

end SevenEighths.CenteredMomentSourceRectangleMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RestrictedDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem source_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*CanonicalRowCompletion.idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*CanonicalRowCompletion.idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentRestrictedDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangleEnergy
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
local notation "O" => ActualEisensteinCubic.O

theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])

end SevenEighths.CenteredMomentSourceRectangleEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainSource
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentAddedZeroUniform
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentUncenteredTerminal CenteredMomentHeckeExpansion
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentDivisorRowEnergy
open CenteredMomentRetainedEnergy CenteredMomentRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma comparison_row_zero (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) :
    rowTwistedSum η m A z W t (comparisonScale b)=0 := by
  rw [rowTwistedSum_eq_weight]
  calc
    _ = ∑' _I : Ideal O, (0:ℂ) := by
      apply tsum_congr
      intro I
      have h := comparison_first_zero W a b ha hs 1 I one_ne_zero
      simpa only [one_mul,mul_zero] using congrArg (fun v : ℂ=>rowWeight η m A z t I*v) h
    _ = 0 := tsum_zero

theorem complete_source_polynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    (∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
      finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
        (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
          rowWeight η m A z t I)=
      (rowTwistedSum η (m*idealGenerator R) A z W₁ t X₁*
        rowTwistedSum η (m*idealGenerator R) A z W₂ t X₂)*
        ∏ i,rowSlot η (m*idealGenerator R) A z (slots i)
          (fun I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t := by
  let : DecidableEq (ι⊕Fin 2) := Classical.decEq _
  have hs₁' : Function.support W₁⊆Set.Iic b₁ := fun x hx=>(hs₁ hx).2
  have hs₂' : Function.support W₂⊆Set.Iic b₂ := fun x hx=>(hs₂ hx).2
  have hy₁ := comparisonScale_pos b₁
  have hy₂ := div_pos (mul_pos hX₁ hX₂) hy₁
  have hc₁ := plainSupportPool_coverage W₁ b₁ X₁ (comparisonScale b₁)
    (support_zero W₁ a₁ b₁ ha₁ hs₁) hs₁' hX₁ hy₁
  have hc₂ := plainSupportPool_coverage W₂ b₂ X₂ (X₁*X₂/comparisonScale b₁)
    (support_zero W₂ a₂ b₂ ha₂ hs₂) hs₂' hX₂ hy₂
  have he := source_polynomial_eq_maskedRectangle η m A z t hmLam hm2 slots _ _ R 1
    ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) 1 1 hc₁ hc₂
  rw [profileCoefficient_eq_uncentered R ν Wslot P W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (X₁*X₂/comparisonScale b₁) 1 1 1 one_ne_zero] at he
  simp only [map_one,Nat.cast_one,div_one] at he
  unfold completePool
  rw [he]
  have hr := actual_slot_rectangle_sum η (m*idealGenerator R) A z slots
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t W₁ W₂ b₁ b₂
    X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) hs₁' hs₂' hX₁ hX₂ hy₁ hy₂
  simp only [maskedRectangle,one_dvd,ite_true,one_mul]
  rw [hr,comparison_row_zero η (m*idealGenerator R) A z t W₁ a₁ b₁ ha₁ hs₁,
    zero_mul,sub_zero]

theorem positiveSlotRow_eq_complete_source (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (m*idealGenerator R) A z W₁ W₂ slots
      (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹*
      ∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
        finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
          (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
            rowWeight η m A z t I := by
  rw [complete_source_polynomial η m A z t hmLam hm2 slots R ν Wslot P W₁ W₂
    a₁ b₁ a₂ b₂ X₁ X₂ ha₁ ha₂ hs₁ hs₂ hX₁ hX₂]
  rfl

theorem positive_energy_eq_complete_source (η : Character) (t : ℝ) (keep : O→Prop)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (hP : ∀ i,0<P i)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑' z : O,if keep z then
      ‖positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X₁ X₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)=
      sourceRestrictedEnergy keep (finiteColumns (completePool slots b₁ b₂ X₁ X₂))
        (finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
          (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1))
        (heightCoeff η t) Φ K / (X₁*X₂*∏ i,P i) := by
  have htotal : 0<X₁*X₂*∏ i,P i := mul_pos (mul_pos hX₁ hX₂)
    (Finset.prod_pos (fun i _=>hP i))
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [← tsum_div_const]
  apply tsum_congr
  intro z
  rw [height_source_row]
  by_cases hk : keep z
  · rw [if_pos hk,if_pos hk,
      positiveSlotRow_eq_complete_source η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) slots R ν Wslot P W₁ W₂
        a₁ b₁ a₂ b₂ X₁ X₂ ha₁ ha₂ hs₁ hs₂ hX₁ hX₂,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    ring
  · simp only [if_neg hk,zero_div]

end SevenEighths.CenteredMomentDetectorPlainSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeDetectorDyadicProfiles

theorem compact_family_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀p∈J,SchwartzMap.seminorm ℝ k n (G p)≤C := by
  have hc := (section_iteratedDeriv_smooth F hF n).continuous.norm
  obtain ⟨M,hM⟩ := (hJ.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨1+L^k*(|M|+1),by positivity,?_⟩
  intro p hp
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro x
  have he : (G p : ℝ→ℂ)=F p := funext (hG p)
  rw [he]
  by_cases hx : x∈Icc (-L) L
  · have hnorm : ‖iteratedDeriv n (F p) x‖≤|M|+1 := by
      have hb := hM (Set.mem_image_of_mem _ (show (p,x)∈J×ˢIcc (-L) L from ⟨hp,hx⟩))
      exact hb.trans (by linarith [le_abs_self M])
    have hxp : ‖x‖^k≤L^k := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using hx
    exact (mul_le_mul hxp hnorm (norm_nonneg _) (pow_nonneg hL k)).trans (by linarith)
  · have hout : iteratedDeriv n (F p) x=0 := by
      by_contra hn
      have hx' := (subset_tsupport (iteratedDeriv n (F p))) hn
      have hh := (CubicReflectionKernel.tsupport_iteratedDeriv_subset (F p) n) hx'
      exact hx ((closure_minimal (hs p) isClosed_Icc) hh)
    rw [hout,norm_zero,mul_zero]
    positivity

theorem compact_family_finite_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀p∈J,S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G p)≤C := by
  choose C hC hb using fun z : ℕ×ℕ=>compact_family_seminorm F hF L hL hs J hJ G hG z.1 z.2
  have hsum : 0≤∑z∈S,C z := Finset.sum_nonneg (fun z _=>(hC z).le)
  refine ⟨1+∑z∈S,C z,by linarith,?_⟩
  intro p hp
  apply Seminorm.finset_sup_apply_le (by linarith)
  intro z hz
  apply (hb z p hp).trans
  have hh := Finset.single_le_sum (fun z (_ : z∈S)=>(hC z).le) hz
  linarith

theorem compact_family_frequencyTwist
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀p∈J,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (JointLogSeparation.frequencyTwist (G p) t)≤C*(1+‖t‖)^n := by
  let S' := S.biUnion (fun z=> (Finset.range (z.2+1)).image (fun i=>(z.1,i)))
  obtain ⟨B,hB,hbound⟩ := compact_family_finite_seminorm F hF L hL hs J hJ G hG S'
  let c : ℕ×ℕ→ℝ := fun z=>(2:ℝ)^z.2*(1+2*Real.pi)^z.2*((z.2+1)*B)
  have hc (z : ℕ×ℕ) : 0≤ c z := by dsimp [c];positivity
  have hsum : 0≤∑z∈S,c z := Finset.sum_nonneg (fun z _=>hc z)
  refine ⟨S.sup Prod.snd,1+∑z∈S,c z,by linarith,?_⟩
  intro p hp t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hd : JointLogSeparation.derivativeSeminormSum (G p) z.1 z.2≤(z.2+1)*B := by
    unfold JointLogSeparation.derivativeSeminormSum
    calc
      _≤∑i∈Finset.range (z.2+1),B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : (z.1,i)∈S' := Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
        exact (Seminorm.le_finset_sup_apply hi').trans (hbound p hp)
      _=_ := by simp
  have hzC : c z≤1+∑z∈S,c z := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S)=>hc z) hz
    linarith
  have he := JointLogSeparation.frequencyTwist_seminorm_polynomial (G p) t z.1 z.2
  have hb : SchwartzMap.seminorm ℝ z.1 z.2 (JointLogSeparation.frequencyTwist (G p) t)≤ c z*(1+‖t‖)^z.2 := by
    apply he.trans
    dsimp only [c]
    gcongr
  exact hb.trans (mul_le_mul hzC
    (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)) (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformLog
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic

lemma realInterpolatedLog_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (realInterpolatedLog W)) := by
  unfold realInterpolatedLog Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>Real.exp (-p.1.1*p.2))).smul
    (hW.comp (by fun_prop))

lemma realInterpolatedLog_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (realInterpolatedLog W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hw : W (Real.exp x)≠0 := by intro hw;exact hx (by simp [realInterpolatedLog,hw])
  have hlo : Real.log a≤x := by simpa only [Real.log_exp] using Real.log_le_log ha (hs hw).1
  have hhi : x≤Real.log b := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) (hs hw).2
  constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),abs_nonneg (Real.log a),abs_nonneg (Real.log b)]

lemma realInterpolatedLogSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) (x : ℝ) :
    realInterpolatedLogSchwartz W a b ha hs hW p x=realInterpolatedLog W p x := by
  rw [realInterpolatedLogSchwartz,CubicReflectionKernel.logSchwartz_apply]
  unfold twistProfile realInterpolatedLog
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ←Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero]
  change W (Real.exp x)*Complex.exp ((x:ℂ)*-(p.1:ℂ))=
    ((Real.exp (-p.1*x):ℝ):ℂ)*W (Real.exp x)
  rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  have he : (x:ℂ)*-(p.1:ℂ)=-(p.1:ℂ)*(x:ℂ) := by ring
  rw [he,mul_comm]

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic JointLogSeparation

 theorem interpolatedProfile_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤C*(1+‖t‖)^n := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CompletedHeight.fixedLogReturnCLM a b ha) S
  obtain ⟨n,B,hB,hbound⟩ := compact_family_frequencyTwist
    (realInterpolatedLog W) (realInterpolatedLog_smooth W hW)
    (|Real.log a|+|Real.log b|) (by positivity) (realInterpolatedLog_support W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ)) (isCompact_Icc.prod isCompact_singleton)
    (realInterpolatedLogSchwartz W a b ha hs hW) (realInterpolatedLogSchwartz_apply W a b ha hs hW) T
  refine ⟨n,A*B,mul_pos hA hB,?_⟩
  intro σ hσ t
  have hp : (σ,0)∈Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ) := ⟨hσ,rfl⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))≤B*(1+‖t‖)^n :=
    (hbound (σ,0) hp (t/(2*Real.pi))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) n) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.lengths (F : Fiber M H Label Slot U a ε tstar T allowance i) (hU : 1<U) :
    tstar-F.r-ε≤F.m ∧ F.r≤tstar+ε ∧ F.m≤1/2+75*ε ∧ tstar-1/2-76*ε≤F.r ∧ 0≤F.m :=
  fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hU F.witness
    F.left F.right F.fixed_left F.fixed_right

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.instFiniteQuotientOIdeal_solutions
lemma relativeCharacter_ideal (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (relativeCharacter M H hH η₀ θ) I=
      idealCoeff (HeckeRayQuotient.character M H hH θ) I*idealCoeff η₀.inverse I :=
  idealCoeff_product _ _ _

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

lemma radialMajorant_nonneg (x:ℝ):0≤(radialMajorant x).re:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.1 x

lemma radialMajorant_one (x:ℝ)(hx:x∈Set.Icc (0:ℝ) 1):radialMajorant x=1:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.2.2 x hx

end SevenEighths.CenteredMomentDetectorPlainFiberSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount
open HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:O)} := inf_le_right

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

theorem detectorSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Fin 3=>interpolatedProfile_uniform
    (orientedProfile q.1 ((logProfile^[q.2.val]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support q.1 q.2.val) (oriented_detector_log_smooth q.1 q.2.val) S
  let J := (Finset.univ : Finset (Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Fin 3,C q,by linarith,?_⟩
  intro reverse n hn σ hσ t
  let q : Bool×Fin 3 := (reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q σ hσ (orientedFrequency reverse t)
  have hnorm : ‖orientedFrequency reverse t‖=‖t‖ := by cases reverse <;> simp [orientedFrequency]
  rw [hnorm] at he
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

variable {Δ:ℝ}{D:Parameters.HighData Δ}

lemma source_keep_iff (F:ProbeFinalAssembly.SourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal F) η) u.val↔¬sourceExceptional F η u:=by
  exact and_iff_right u.property.1

theorem source_label_modulus_eventually (F:ProbeFinalAssembly.SourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

end SevenEighths.CenteredMomentDetectorEnergyInitialState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

theorem fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQη : Q≤η.modulus)
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {Δ : ℝ} {D : Parameters.HighData Δ}

lemma source_exceptional_norm (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤ sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤ rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)<Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary
local notation "O"=>HeckeFamily.O
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem physical_annular_all (S:ProbeFinalAssembly.SourceData D)(η₀:Character)
    (P:ℝ)(hP:0<P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=>conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentDetectorPlainCapacity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainStateDictionary
open HeckeFamily HeckeDetectorRawFiber HeckePrimeAnnular
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

lemma plainProfile_eq_detectorSchwartz
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(j:ℕ)(σ t:ℝ):
    plainProfile F j σ t=(detectorSchwartz F.reverse j σ t:ℝ→ℂ):=by
  funext x
  exact (detectorSchwartz_apply F.reverse j σ t x).symm

theorem retainedSourceEnergy_eq_energy
    (keep:O→Prop)(F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ))(hU:0<U):
    retainedSourceEnergy keep F η selected j k σ t Φ=
      energy η (fixedBadMask*idealGenerator 1) 1 0
        (plainProfile F j σ t) (plainProfile F k σ t)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m) keep Φ U:=by
  exact (positive_energy_eq_complete_source η 0 keep
    (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (fun _=>Real.rpow_pos_of_pos hU _)
    (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _) Φ U).symm

end SevenEighths.CenteredMomentDetectorPlainStateDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainMarkedState
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_slot_coefficient (S:ProbeFinalAssembly.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(η:Character)(s:Slot)
    (hreal:(F.external s).re=17/50)(hU:0<U)(I:Ideal O):
    idealCoeff η.inverse I*slotWindow F s ((I.absNorm:ℝ)/(U^(F.widths s)))=
      idealCoeff η.inverse I*annularWeight (fun x=>conj (S.W x))
        (U^(F.widths s)) (33/50) (-(F.external s).im) I := by
  have he:=physical_annular_all S η (U^(F.widths s)) (Real.rpow_pos_of_pos hU _)
    (F.external s) I
  rw [hreal] at he
  norm_num at he
  simpa only [physicalSlotCoefficient,slotWindow,hprofile] using he

theorem retained_eq_initial_energy (S:ProbeFinalAssembly.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(hupper:∀s,F.upper s=2)
    (η:Character)(Q:Ideal O)(selected:Finset Slot)
    (hreal:∀s∈selected,(F.external s).re=17/50)
    (Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)(hU:1≤U)(hδ:0≤δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^δ)(j k:ℕ)(σ t:ℝ):
    let state:=initialState η Q Φ bΦ U δ hU hδ hs hp hη
    retainedSourceEnergy state.radial.keep F η selected j k σ t Φ=
      energy state.character state.mask 1 0
        ((detectorProfiles F.reverse j k σ t).profile 0)
        ((detectorProfiles F.reverse j k σ t).profile 1)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H 2 (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*
          annularWeight (fun x=>conj (S.W x)) (U^(F.widths s.val)) (33/50)
            (-(F.external s.val).im) I)
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m)
        state.radial.keep state.radial.profile state.radial.scale := by
  dsimp only
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  have hc:(fun (s:selected) I=>idealCoeff η.inverse I*
      slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))=
      (fun (s:selected) I=>idealCoeff η.inverse I*
        annularWeight (fun x=>conj (S.W x)) (U^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I):=by
    funext s I
    exact source_slot_coefficient S F hprofile η s.val (hreal s.val s.property)
      (zero_lt_one.trans_le hU) I
  rw [hc]
  simp only [hupper,plainProfile_eq_detectorSchwartz,initialState,NaturalState.mask,
    detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
  norm_num

theorem plain_length_eq [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1<U):
    length U (U^F.m)=F.m := by
  have hm:0≤F.m:=(F.lengths hU).2.2.2.2
  rw [length,max_eq_right (Real.one_le_rpow hU.le hm),
    Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem marked_capacity [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1<U)
    (selected:Finset Slot)(κ δ:ℝ)(hδ:0≤δ)
    (hcap:2*F.m+6*κ*(∑s∈selected,F.widths s)≤1):
    length U (U^F.m)+length U (U^F.m)+6*κ*(∑s:selected,F.widths s.val)≤1+δ := by
  rw [plain_length_eq F hU,Finset.sum_coe_sort]
  linarith

theorem source_batch_marked_initial (S:ProbeFinalAssembly.SourceData D):
    ∃bΦ:ℝ,0<bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*(3/4+2*Δ)*(∑s∈selected,F.widths s)≤1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*(3/4+2*Δ)*(∑s:selected,F.widths s.val)≤ state.width ∧
        (∀s:selected,0<F.widths s.val ∧ F.widths s.val≤F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
          energy state.character state.mask 1 0
            ((detectorProfiles F.reverse j k σ t).profile 0)
            ((detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=>CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=>idealCoeff η₀.inverse I*
              annularWeight (fun x=>conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually S η δ hδ,source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0<d:=by linarith
  have hU:1<Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ)≤(Z^d)^δ:=hz.2 label d hd
  let state:=initialState η₀ (internalQ (sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=retained_eq_initial_energy S F hprof hupper η₀ (internalQ (sourceFixedIdeal S) η₀) selected
      (fun s _=>hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end SevenEighths.CenteredMomentDetectorPlainMarkedState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMomentParameters
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Δ:ℝ}

lemma source_base_gt_one (_D:Parameters.HighData Δ)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ)≤d):1<Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap (D:Parameters.HighData Δ):
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem actual_fiber_lengths (D:Parameters.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1<U):
    0≤F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact plain_length_eq F hU

lemma width_bands (D:Parameters.HighData Δ)(m:ℝ)(hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤ max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  have hδ:0<delta D:=(fixed_parameters D).1
  have hd:delta D≤1/4:=(fixed_parameters D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.CenteredMomentDetectorPlainMomentParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional

theorem paired_control (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t:ℝ,
      (detectorProfiles reverse j k σ t).control S ^2≤C*(1+‖t‖)^J:=by
  obtain ⟨J,C,hC,h⟩:=detectorSchwartz_uniform S
  refine ⟨4*J,C ^4,by positivity,?_⟩
  intro reverse j k hjk σ hσ t
  have hj:=h reverse j (by omega) σ hσ t
  have hk:=h reverse k (by omega) σ hσ t
  have hp:(detectorProfiles reverse j k σ t).control S≤(C*(1+‖t‖)^J)^2:=by
    simpa only [detectorProfiles,Profiles.control,sourceControl,Fin.zero_eta,ite_true,
      show ¬((1:Fin 2)=0) by decide,ite_false,pow_two] using
      mul_le_mul hj hk (sourceControl_nonneg S (detectorSchwartz reverse k σ t)) (by positivity)
  have hs:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
  calc
    _≤((C*(1+‖t‖)^J)^2)^2:=hs
    _=C ^4*(1+‖t‖)^(4*J):=by
      rw [←pow_mul,mul_pow,←pow_mul]
      congr 2 ; omega

theorem source_height_factor (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀degree:ℕ,∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height → |t|≤height →
      (detectorProfiles reverse j k σ t).control S ^2*(1+|(0:ℝ)|+height)^degree
        ≤C*(1+height)^(J+degree):=by
  obtain ⟨J,C,hC,h⟩:=paired_control S
  refine ⟨J,C,hC,?_⟩
  intro degree reverse j k hjk σ hσ height t hh ht
  have hb:(detectorProfiles reverse j k σ t).control S ^2≤C*(1+height)^J:=by
    apply (h reverse j k hjk σ hσ t).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Real.norm_eq_abs] using add_le_add le_rfl ht
  simpa only [abs_zero,add_zero,pow_add,mul_assoc] using
    mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith:0≤1+height) degree)

end SevenEighths.CenteredMomentDetectorPlainProfileControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainRelativeClass
open HeckeFamily CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
attribute [local instance] OAI.SevenEighths.CenteredMomentDetectorPlainRelativeClass.instFiniteQuotientOIdeal
local instance instIsPrincipalIdealRingO_solutions:IsPrincipalIdealRing O:=IsCyclotomicExtension.Rat.three_pid K
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

lemma ray_identity (θ:RayQuotient.Characters M H)(I:Ideal O)
    (hI:I∈RayQuotient.identityClass M H):
    idealCoeff (HeckeRayQuotient.character M H hH θ) I=1:=by
  rcases hI with ⟨hI,a,ha,u,hu,huH⟩
  rw [HeckeRayQuotient.idealCoeff_character]
  change IdealCharacter.ofResidue M θ (RayQuotient.character_unitInvariant M H hH θ) I=1
  rw [IdealCharacter.ofResidue_of_generator M θ _ hI ha,←hu]
  exact (RayOrthogonality.mem_characters_iff H θ).mp θ.property u huH

lemma relative_pool (η₀:Character)(θ:RayQuotient.Characters M H)(b P:ℝ)
    (I:Ideal O)(hI:I∈primePool M H b P):
    idealCoeff (relativeCharacter M H hH η₀ θ) I=idealCoeff η₀.inverse I:=by
  rw [relativeCharacter_ideal,ray_identity M H hH θ I (Finset.mem_filter.mp hI).2.2,one_mul]

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem positive_row (η η₀:Character)(θ:ι→RayQuotient.Characters M H)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→Ideal O→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*β i I) P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P t X₁ X₂:=by
  unfold positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [relative_pool M H hH η₀ (θ i) (b i) (P i) I hI]

omit [DecidableEq ι] in
theorem energy_eq (η η₀:Character)(θ:ι→RayQuotient.Characters M H)(m A:O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→Ideal O→ℂ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*β i I) P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row M H hH η η₀ θ m A z W₁ W₂ b P β t X₁ X₂]

end SevenEighths.CenteredMomentDetectorPlainRelativeClass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ParametersHighDataFine
namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.Parameters

theorem fine_slot_widths {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0< mesh D.t)(hfine:∀j,D.ell j≤ mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ)≤d)(j:Fin D.N):
    0<D.ell j/d ∧ D.ell j/d≤ mesh D.t:=by
  have hd0:0<d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith

end SevenEighths.Parameters

end

end OAI
end

section
-- module Transport.PhysicalHigh.PlainRetained (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

open OAI OAI.SevenEighths
open CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_fibers_eventually_retained_t (S:ProbeFinalAssembly.SourceData D)(N:ℕ)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional S η₀))=∅:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem source_batch_plain_retained_t (S:ProbeFinalAssembly.SourceData D)(N:ℕ)(ell:Fin N→ℝ)
    (hell:∀j,0< ell j)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [source_fibers_eventually_retained_t S N η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      ell hell 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0< Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus≤ Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end
end RH.Transport.PhysicalHigh

end

section
-- module Transport.PhysicalHigh.PlainInitialState (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

open OAI OAI.SevenEighths
open CenteredMomentDetectorPlainMarkedState
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_batch_marked_initial_t (S:ProbeFinalAssembly.SourceData D)(N:ℕ)(ell:Fin N→ℝ)
    (hell:∀j,0< ell j)(κ:ℝ):
    ∃bΦ:ℝ,0< bΦ ∧ ∀η:Character,∀δ:ℝ,0< δ→
      ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*κ*(∑s∈selected,F.widths s)≤1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*κ*(∑s:selected,F.widths s.val)≤ state.width ∧
        (∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
          energy state.character state.mask 1 0
            ((detectorProfiles F.reverse j k σ t).profile 0)
            ((detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=>CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=>idealCoeff η₀.inverse I*
              annularWeight (fun x=>conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually S η δ hδ,source_batch_plain_retained_t S N ell hell η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0< d:=by linarith
  have hU:1< Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ)≤(Z^d)^δ:=hz.2 label d hd
  let state:=initialState η₀ (internalQ (sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=retained_eq_initial_energy S F hprof hupper η₀ (internalQ (sourceFixedIdeal S) η₀) selected
      (fun s _=>hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end
end RH.Transport.PhysicalHigh

end

section
-- module Transport.PhysicalHigh.PlainMarked (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainMomentParameters CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=>HeckeFamily.O

theorem source_batch_plain_marked_fine_t {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(N:ℕ)(ell:Fin N→ℝ)(hell:∀j,0< ell j)
    (ε εm:ℝ)(hε:ε≤1/1000)(hεm:0< εm)(hεm1:εm≤1)
    (mesh:ℝ)(hmesh:0< mesh)(hfine:∀j,ell j≤ mesh/200)
    (henergy:PositiveFineSourceInput S N εm mesh):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin N)
      (Z^d) a ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height→(∀s,|(B.external s).im|≤ height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin N),selected⊆F.slots→
      2*F.m+6*(3/4)*(∑s∈selected,F.widths s)≤1→
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+εm):=by
  obtain ⟨bΦ,hbΦ,hsource⟩:=source_batch_marked_initial_t S N ell hell (3/4)
  obtain ⟨degree,seminorms,henergy⟩:=henergy bΦ hbΦ
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩:=
    CenteredMomentDetectorPlainProfileControl.source_height_factor seminorms
  refine ⟨J+degree,?_⟩
  intro η
  let data:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η
  choose C hC hbound using fun label=>henergy (data label)
  choose U₀ hU₀ using fun label=>Filter.eventually_atTop.mp (hbound label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0< Csum:=by
    have h:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤ Csum:=by
    have h:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le)
      (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→U₀ label≤ Z^d:=by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  let Cfinal:=Csum*(1+diagonalControl radialMajorant)*Cprofile
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  refine ⟨Cfinal,by dsimp [Cfinal];positivity,?_⟩
  filter_upwards [hsource η (εm/4) (by positivity),hscale] with Z hs hscale
  refine ⟨hs.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap j k hjk σ hσ t ht
  have hU:1< Z^d:=Real.one_lt_rpow hs.1 (by linarith)
  obtain ⟨state,hchar,hQ,hpuncture,hΦ,hK,hkeep,hwidthstate,hcapacity,hwidths,hrow⟩:=
    hs.2 rows hrows d hd a ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected hcap
  have hm:F.m≤1:=by
    have hlength: F.m≤1/2+75*ε := (F.lengths hU).2.2.1
    linarith
  have hlength:(Z^d)^F.m≤ Z^d:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le hm
  have hstate:state.width≤2:=by rw [hwidthstate];linarith
  have hw (s:selected):0≤ F.widths s.val:=(hwidths s).1.le
  have hwcap (s:selected):F.widths s.val≤ mesh:=by
    change B.widths s.val≤ mesh
    rw [hwidth]
    apply (div_le_iff₀ (show 0< d by linarith)).mpr
    have hs:=hfine s.val
    nlinarith [hmesh.le]
  have hpos:=hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=>F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im)
    0 height hw hwcap (fun _=>le_rfl) (fun _=>le_rfl) hheight
    (fun s=>by change |-(B.external s.val).im|≤ height; simpa only [abs_neg] using hexternal s.val)
    state hQ hstate (detectorProfiles F.reverse j k σ t) ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by simpa only [Real.rpow_one] using hlength)
    (by simpa only [Real.rpow_one] using hlength) hcapacity
  have heq:=CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character (data label) (fun (_:selected)=>1) state.mask 1
    ((detectorProfiles F.reverse j k σ t).profile 0)
    ((detectorProfiles F.reverse j k σ t).profile 1)
    (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=>HeckePrimeAnnular.annularWeight (fun x=>conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hnorm:=hprofile degree F.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hp:0≤(detectorProfiles F.reverse j k σ t).control seminorms ^2:=sq_nonneg _
  have hexp:state.width+εm/4≤1+εm:=by
    rw [hwidthstate];linarith
  calc
    _≤ _:=hrow j k σ t
    _≤ C label*diagonalControl state.radial.profile*
        (detectorProfiles F.reverse j k σ t).control seminorms ^2*
        (1+|(0:ℝ)|+height)^degree*(Z^d)^(state.width+εm/4):=by
      exact heq.le.trans hpos
    _≤(Cfinal*(1+height)^(J+degree))*(Z^d)^(1+εm):=by
      rw [hΦ]
      have hpow:=Real.rpow_le_rpow_of_exponent_le hU.le hexp
      calc
        _=(C label*diagonalControl radialMajorant)*
          ((detectorProfiles F.reverse j k σ t).control seminorms ^2*
            (1+|(0:ℝ)|+height)^degree)*(Z^d)^(state.width+εm/4):=by ring
        _≤(Csum*(1+diagonalControl radialMajorant))*
          (Cprofile*(1+height)^(J+degree))*(Z^d)^(1+εm):=by
          apply mul_le_mul _ hpow (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
          apply mul_le_mul _ hnorm (by positivity) (by positivity)
          exact mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
        _=_:=by dsimp [Cfinal];ring
end
end RH.Transport.PhysicalHigh

end

theorem solution : type_of% @RH.Transport.PhysicalHigh.source_batch_plain_marked_fine_t := @RH.Transport.PhysicalHigh.source_batch_plain_marked_fine_t
