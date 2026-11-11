-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.hybrid_large_width
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T15:59:45.113293+00:00
-- url     : https://prove2.me/submissions/b6bf6131-72bf-4a2b-943d-c5b631fc21fd

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.FunProp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith


set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace S11Gaussian

private def expQuadratic (v t : ℝ) : ℝ := Real.exp (v * t ^ 2 / 2)

private theorem expQuadratic_hasDerivAt (v t : ℝ) :
    HasDerivAt (expQuadratic v) (v * t * expQuadratic v t) t := by
  unfold expQuadratic
  convert ((((hasDerivAt_id t).pow 2).const_mul v).div_const 2).exp using 1 <;> first | rfl | (try simp only [Pi.pow_apply, id_eq]; ring)

private theorem expQuadratic_deriv (v : ℝ) :
    deriv (expQuadratic v) = fun t => v * t * expQuadratic v t := by
  funext t
  exact (expQuadratic_hasDerivAt v t).deriv

private theorem expQuadratic_deriv_two (v : ℝ) :
    deriv (fun t => v * t * expQuadratic v t) =
      fun t => (v + v ^ 2 * t ^ 2) * expQuadratic v t := by
  funext t
  have h : HasDerivAt (fun t => v * t * expQuadratic v t)
      ((v + v ^ 2 * t ^ 2) * expQuadratic v t) t := by
    convert ((hasDerivAt_id t).const_mul v).mul (expQuadratic_hasDerivAt v t) using 1 <;> first | rfl | (try simp only [id_eq]; ring)
  exact h.deriv

private theorem expQuadratic_deriv_three (v : ℝ) :
    deriv (fun t => (v + v ^ 2 * t ^ 2) * expQuadratic v t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * expQuadratic v t := by
  funext t
  have h : HasDerivAt (fun t => (v + v ^ 2 * t ^ 2) * expQuadratic v t)
      ((3 * v ^ 2 * t + v ^ 3 * t ^ 3) * expQuadratic v t) t := by
    convert ((hasDerivAt_const t v).add (((hasDerivAt_id t).pow 2).const_mul (v ^ 2))).mul
      (expQuadratic_hasDerivAt v t) using 1 <;> first | rfl | (try simp only [Pi.pow_apply, Pi.add_apply, id_eq]; ring)
  exact h.deriv

private theorem expQuadratic_deriv_four (v : ℝ) :
    deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * expQuadratic v t) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * expQuadratic v t := by
  funext t
  have h : HasDerivAt (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * expQuadratic v t)
      ((3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * expQuadratic v t) t := by
    convert (((hasDerivAt_id t).const_mul (3 * v ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul (v ^ 3))).mul
      (expQuadratic_hasDerivAt v t) using 1 <;> first | rfl | (try simp only [Pi.pow_apply, Pi.add_apply, id_eq]; ring)
  exact h.deriv

theorem centered_gaussian_moment_two (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have hm : iteratedDeriv 2 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 =
      ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v := by
    simpa using iteratedDeriv_mgf_zero (μ := gaussianReal 0 v)
      (X := fun x : ℝ => x) (by simp) 2
  rw [← hm, mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  change iteratedDeriv 2 (expQuadratic (v : ℝ)) 0 = (v : ℝ)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, expQuadratic_deriv,
    expQuadratic_deriv_two]
  simp [expQuadratic]

theorem centered_gaussian_moment_three (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v) = 0 := by
  have hm : iteratedDeriv 3 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 =
      ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v := by
    simpa using iteratedDeriv_mgf_zero (μ := gaussianReal 0 v)
      (X := fun x : ℝ => x) (by simp) 3
  rw [← hm, mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  change iteratedDeriv 3 (expQuadratic (v : ℝ)) 0 = 0
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, expQuadratic_deriv,
    expQuadratic_deriv_two, expQuadratic_deriv_three]
  simp [expQuadratic]

theorem centered_gaussian_moment_four (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hm : iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 =
      ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v := by
    simpa using iteratedDeriv_mgf_zero (μ := gaussianReal 0 v)
      (X := fun x : ℝ => x) (by simp) 4
  rw [← hm, mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  change iteratedDeriv 4 (expQuadratic (v : ℝ)) 0 = 3 * (v : ℝ) ^ 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, expQuadratic_deriv,
    expQuadratic_deriv_two, expQuadratic_deriv_three, expQuadratic_deriv_four]
  simp [expQuadratic]

section RandomVariables

variable {Ω J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem gaussian_moment_eq {X : Ω → ℝ} {v : ℝ≥0}
    (hX : Measurable X) (hLaw : μ.map X = gaussianReal 0 v) (n : ℕ) :
    (∫ ω, X ω ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂gaussianReal 0 v := by
  rw [← hLaw]
  exact (integral_map (f := fun x : ℝ => x ^ n) hX.aemeasurable
    (measurable_id.pow_const n).aestronglyMeasurable).symm

theorem gaussian_mean {X : Ω → ℝ} {v : ℝ≥0}
    (hX : Measurable X) (hLaw : μ.map X = gaussianReal 0 v) :
    (∫ ω, X ω ∂μ) = 0 := by
  have h := gaussian_moment_eq hX hLaw 1
  simpa using h

theorem gaussian_second {X : Ω → ℝ} {v : ℝ≥0}
    (hX : Measurable X) (hLaw : μ.map X = gaussianReal 0 v) :
    (∫ ω, X ω ^ 2 ∂μ) = (v : ℝ) :=
  (gaussian_moment_eq hX hLaw 2).trans (centered_gaussian_moment_two v)

theorem gaussian_fourth {X : Ω → ℝ} {v : ℝ≥0}
    (hX : Measurable X) (hLaw : μ.map X = gaussianReal 0 v) :
    (∫ ω, X ω ^ 4 ∂μ) = 3 * (v : ℝ) ^ 2 :=
  (gaussian_moment_eq hX hLaw 4).trans (centered_gaussian_moment_four v)

variable [DecidableEq J]

def covarianceEntry (v : J → ℝ≥0) (i j : J) : ℝ :=
  if i = j then (v i : ℝ) else 0

variable (N : J → Ω → ℝ) (v : J → ℝ≥0)
    (hm : ∀ i, Measurable (N i))
    (hLaw : ∀ i, μ.map (N i) = gaussianReal 0 (v i))
    (hind : iIndepFun N μ)

include hm hLaw hind

theorem gaussian_pair (i j : J) :
    (∫ ω, N i ω * N j ω ∂μ) = covarianceEntry v i j := by
  by_cases hij : i = j
  · subst j
    simpa [covarianceEntry, pow_two] using gaussian_second (hm i) (hLaw i)
  · rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
      (hm i).aestronglyMeasurable (hm j).aestronglyMeasurable,
      gaussian_mean (hm i) (hLaw i)]
    simp [covarianceEntry, hij]

theorem gaussian_four_same (i : J) :
    (∫ ω, N i ω * N i ω * N i ω * N i ω ∂μ) = 3 * (v i : ℝ) ^ 2 := by
  simpa only [pow_succ, pow_zero, mul_one, one_mul] using gaussian_fourth (hm i) (hLaw i)

theorem gaussian_three_one (i j : J) (hij : i ≠ j) :
    (∫ ω, N i ω * N i ω * N i ω * N j ω ∂μ) = 0 := by
  have hi : IndepFun (fun ω => N i ω ^ 3) (N j) μ := by
    simpa only [Function.comp_def, id_eq] using
      (hind.indepFun hij).comp (measurable_id.pow_const 3) measurable_id
  have h := hi.integral_fun_mul_eq_mul_integral ((hm i).pow_const 3).aestronglyMeasurable
    (hm j).aestronglyMeasurable
  rw [gaussian_mean (hm j) (hLaw j), mul_zero] at h
  simpa only [pow_succ, pow_zero, mul_one, one_mul] using h

theorem gaussian_factor_four (i j k l : J)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (∫ ω, N i ω * N j ω * N k ω * N l ω ∂μ) =
      covarianceEntry v i j * covarianceEntry v k l := by
  have h := (hind.indepFun_mul_mul hm i j k l hik hil hjk hjl).integral_fun_mul_eq_mul_integral
    ((hm i).mul (hm j)).aestronglyMeasurable ((hm k).mul (hm l)).aestronglyMeasurable
  simp only [Pi.mul_apply] at h
  rw [gaussian_pair N v hm hLaw hind i j, gaussian_pair N v hm hLaw hind k l] at h
  simpa only [mul_assoc] using h

theorem gaussian_wick_four (i j k l : J) :
    (∫ ω, N i ω * N j ω * N k ω * N l ω ∂μ) =
      covarianceEntry v i j * covarianceEntry v k l +
      covarianceEntry v i k * covarianceEntry v j l +
      covarianceEntry v i l * covarianceEntry v j k := by
  by_cases heq0 : i = j
  · subst j
    by_cases heq1 : i = k
    · subst k
      by_cases heq2 : i = l
      · subst l
        have h := gaussian_four_same N v hm hLaw hind i
        simp [covarianceEntry] at h ⊢
        convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
      ·
        have h := gaussian_three_one N v hm hLaw hind i l heq2
        simp [covarianceEntry, heq2] at h ⊢
        convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
    ·
      by_cases heq3 : i = l
      · subst l
        have h := gaussian_three_one N v hm hLaw hind i k heq1
        simp [covarianceEntry, heq1, Ne.symm heq1] at h ⊢
        convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
      ·
        by_cases heq4 : k = l
        · subst l
          have h := gaussian_factor_four N v hm hLaw hind i i k k heq1 heq1 heq1 heq1
          simp [covarianceEntry, heq1] at h ⊢
          convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
        ·
          have h := gaussian_factor_four N v hm hLaw hind i i k l heq1 heq3 heq1 heq3
          simp [covarianceEntry, heq1, heq3, heq4] at h ⊢
          convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
  ·
    by_cases heq5 : i = k
    · subst k
      by_cases heq6 : i = l
      · subst l
        have h := gaussian_three_one N v hm hLaw hind i j heq0
        simp [covarianceEntry, heq0, Ne.symm heq0] at h ⊢
        convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
      ·
        by_cases heq7 : j = l
        · subst l
          have h := gaussian_factor_four N v hm hLaw hind i i j j heq0 heq0 heq0 heq0
          simp [covarianceEntry, heq0, Ne.symm heq0] at h ⊢
          convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
        ·
          have h := gaussian_factor_four N v hm hLaw hind i i j l heq0 heq6 heq0 heq6
          simp [covarianceEntry, heq0, heq6, heq7, Ne.symm heq0] at h ⊢
          convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
    ·
      by_cases heq8 : j = k
      · subst k
        by_cases heq9 : i = l
        · subst l
          have h := gaussian_factor_four N v hm hLaw hind i i j j heq0 heq0 heq0 heq0
          simp [covarianceEntry, heq0, Ne.symm heq0] at h ⊢
          convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
        ·
          by_cases heq10 : j = l
          · subst l
            have h := gaussian_three_one N v hm hLaw hind j i (Ne.symm heq0)
            simp [covarianceEntry, heq0, Ne.symm heq0] at h ⊢
            convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
          ·
            have h := gaussian_factor_four N v hm hLaw hind j j i l (Ne.symm heq0) heq10 (Ne.symm heq0) heq10
            simp [covarianceEntry, heq0, heq9, heq10, Ne.symm heq0] at h ⊢
            convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
      ·
        by_cases heq11 : i = l
        · subst l
          have h := gaussian_factor_four N v hm hLaw hind i i j k heq0 heq5 heq0 heq5
          simp [covarianceEntry, heq0, heq5, heq8, Ne.symm heq0, Ne.symm heq5] at h ⊢
          convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
        ·
          by_cases heq12 : j = l
          · subst l
            have h := gaussian_factor_four N v hm hLaw hind j j i k (Ne.symm heq0) heq8 (Ne.symm heq0) heq8
            simp [covarianceEntry, heq0, heq5, heq8, Ne.symm heq8] at h ⊢
            convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
          ·
            by_cases heq13 : k = l
            · subst l
              have h := gaussian_factor_four N v hm hLaw hind k k i j (Ne.symm heq5) (Ne.symm heq8) (Ne.symm heq5) (Ne.symm heq8)
              simp [covarianceEntry, heq0, heq5, heq8] at h ⊢
              convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring
            ·
              have h := gaussian_factor_four N v hm hLaw hind i j k l heq5 heq11 heq8 heq12
              simp [covarianceEntry, heq0, heq5, heq8, heq11, heq12, heq13] at h ⊢
              convert h using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with ω; ring) | ring

end RandomVariables
end S11Gaussian
end


set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace S11Independence

variable {Ω N A : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_two_mul_of_four {f g : Ω → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun w => f w * g w) 2 μ := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  exact hg.mul' hf

theorem integrable_two_of_four [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    Integrable (fun w => f w * g w) μ :=
  (memLp_two_mul_of_four hf hg).integrable (by norm_num)

theorem integrable_four_of_four {f g h k : Ω → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    (hh : MemLp h 4 μ) (hk : MemLp k 4 μ) :
    Integrable (fun w => f w * g w * h w * k w) μ := by
  have hfg := memLp_two_mul_of_four hf hg
  have hhk := memLp_two_mul_of_four hh hk
  have hi := hfg.integrable_mul hhk
  change Integrable (fun w => (f w * g w) * (h w * k w)) μ at hi
  simpa only [mul_assoc] using hi

theorem independent_products {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    {k l : ℕ} (i : Fin k → N) (a : Fin l → A) :
    IndepFun (fun w => ∏ t, X (i t) w) (fun w => ∏ t, Y (a t) w) μ := by
  have hX : Measurable (fun z : N → ℝ => ∏ t, z (i t)) := by fun_prop
  have hY : Measurable (fun z : A → ℝ => ∏ t, z (a t)) := by fun_prop
  exact h.comp hX hY

theorem integral_product_factorization {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ a, Measurable (Y a))
    {k l : ℕ} (i : Fin k → N) (a : Fin l → A) :
    (∫ w, (∏ t, X (i t) w) * (∏ t, Y (a t) w) ∂μ) =
      (∫ w, ∏ t, X (i t) w ∂μ) * (∫ w, ∏ t, Y (a t) w ∂μ) := by
  have hmX : Measurable (fun w => ∏ t, X (i t) w) := by fun_prop
  have hmY : Measurable (fun w => ∏ t, Y (a t) w) := by fun_prop
  exact (independent_products h i a).integral_fun_mul_eq_mul_integral
    hmX.aestronglyMeasurable hmY.aestronglyMeasurable

theorem independent_two {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (i j : N) (a b : A) :
    IndepFun (fun w => X i w * X j w) (fun w => Y a w * Y b w) μ := by
  simpa [Fin.prod_univ_succ] using
      independent_products h ![i, j] ![a, b]

theorem independent_four {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (i j k l : N) (a b c d : A) :
    IndepFun (fun w => X i w * X j w * X k w * X l w)
      (fun w => Y a w * Y b w * Y c w * Y d w) μ := by
  simpa [Fin.prod_univ_succ, mul_assoc] using
    independent_products h ![i, j, k, l] ![a, b, c, d]

theorem integrable_mixed_two [IsFiniteMeasure μ]
    {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (hX : ∀ i, MemLp (X i) 4 μ) (hY : ∀ a, MemLp (Y a) 4 μ)
    (i j : N) (a b : A) :
    Integrable (fun w => (X i w * Y a w) * (X j w * Y b w)) μ := by
  have hi := (independent_two h i j a b).integrable_mul
    (integrable_two_of_four (hX i) (hX j))
    (integrable_two_of_four (hY a) (hY b))
  convert hi using 1
  ext w
  simp only [Pi.mul_apply]
  ring

theorem integrable_mixed_four {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (hX : ∀ i, MemLp (X i) 4 μ) (hY : ∀ a, MemLp (Y a) 4 μ)
    (i j k l : N) (a b c d : A) :
    Integrable (fun w => (X i w * Y a w) * (X j w * Y b w) *
      (X k w * Y c w) * (X l w * Y d w)) μ := by
  have hi := (independent_four h i j k l a b c d).integrable_mul
    (integrable_four_of_four (hX i) (hX j) (hX k) (hX l))
    (integrable_four_of_four (hY a) (hY b) (hY c) (hY d))
  convert hi using 1
  ext w
  simp only [Pi.mul_apply]
  ring

theorem integral_mixed_two {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ a, Measurable (Y a))
    (i j : N) (a b : A) :
    (∫ w, (X i w * Y a w) * (X j w * Y b w) ∂μ) =
      (∫ w, X i w * X j w ∂μ) * (∫ w, Y a w * Y b w ∂μ) := by
  have he := (independent_two h i j a b).integral_fun_mul_eq_mul_integral
    ((hX i).mul (hX j)).aestronglyMeasurable
    ((hY a).mul (hY b)).aestronglyMeasurable
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with w
  ring

theorem integral_mixed_four {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ a, Measurable (Y a))
    (i j k l : N) (a b c d : A) :
    (∫ w, (X i w * Y a w) * (X j w * Y b w) *
      (X k w * Y c w) * (X l w * Y d w) ∂μ) =
      (∫ w, X i w * X j w * X k w * X l w ∂μ) *
      (∫ w, Y a w * Y b w * Y c w * Y d w ∂μ) := by
  have he := (independent_four h i j k l a b c d).integral_fun_mul_eq_mul_integral
    ((((hX i).mul (hX j)).mul (hX k)).mul (hX l)).aestronglyMeasurable
    ((((hY a).mul (hY b)).mul (hY c)).mul (hY d)).aestronglyMeasurable
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with w
  ring

theorem gaussian_memLp_four {Z : Ω → ℝ} {v : ℝ≥0}
    (hm : Measurable Z) (hlaw : μ.map Z = gaussianReal 0 v) : MemLp Z 4 μ := by
  have hi : MemLp (id : ℝ → ℝ) 4 (μ.map Z) := by
    rw [hlaw]
    simpa using memLp_id_gaussianReal (μ := 0) (v := v) (4 : ℝ≥0)
  simpa only [Function.comp_def, id_eq] using hi.comp_of_map hm.aemeasurable

theorem integral_sum_two {J K : Type*} [Fintype J] [Fintype K]
    (f : J → K → Ω → ℝ) (hf : ∀ j k, Integrable (f j k) μ) :
    (∫ w, ∑ j, ∑ k, f j k w ∂μ) = ∑ j, ∑ k, ∫ w, f j k w ∂μ := by
  simpa only [Fintype.sum_prod_type] using
    integral_finsetSum Finset.univ (f := fun p : J × K => f p.1 p.2)
      (fun p _ => hf p.1 p.2)

theorem integral_sum_four {J K L M : Type*}
    [Fintype J] [Fintype K] [Fintype L] [Fintype M]
    (f : J → K → L → M → Ω → ℝ) (hf : ∀ j k l m, Integrable (f j k l m) μ) :
    (∫ w, ∑ j, ∑ k, ∑ l, ∑ m, f j k l m w ∂μ) =
      ∑ j, ∑ k, ∑ l, ∑ m, ∫ w, f j k l m w ∂μ := by
  simpa only [Fintype.sum_prod_type] using
    integral_finsetSum Finset.univ
      (f := fun p : J × K × L × M => f p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p _ => hf p.1 p.2.1 p.2.2.1 p.2.2.2)

theorem integral_linear_two [IsFiniteMeasure μ]
    {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ a, Measurable (Y a))
    (hX : ∀ i, MemLp (X i) 4 μ) (hY : ∀ a, MemLp (Y a) 4 μ)
    {J K : Type*} [Fintype J] [Fintype K]
    (i : J → N) (a : J → A) (j : K → N) (b : K → A) :
    (∫ w, (∑ t, X (i t) w * Y (a t) w) * (∑ t, X (j t) w * Y (b t) w) ∂μ) =
      ∑ t, ∑ u, (∫ w, X (i t) w * X (j u) w ∂μ) *
        (∫ w, Y (a t) w * Y (b u) w ∂μ) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_sum_two _ (fun t u => integrable_mixed_two h hX hY (i t) (j u) (a t) (b u))]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  exact integral_mixed_two h hXm hYm (i t) (j u) (a t) (b u)

theorem integral_linear_four {X : N → Ω → ℝ} {Y : A → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => Y a w) μ)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ a, Measurable (Y a))
    (hX : ∀ i, MemLp (X i) 4 μ) (hY : ∀ a, MemLp (Y a) 4 μ)
    {J K L M : Type*} [Fintype J] [Fintype K] [Fintype L] [Fintype M]
    (i : J → N) (a : J → A) (j : K → N) (b : K → A)
    (k : L → N) (c : L → A) (l : M → N) (d : M → A) :
    (∫ w, (∑ t, X (i t) w * Y (a t) w) * (∑ t, X (j t) w * Y (b t) w) *
      (∑ t, X (k t) w * Y (c t) w) * (∑ t, X (l t) w * Y (d t) w) ∂μ) =
      ∑ t, ∑ u, ∑ v, ∑ z,
        (∫ w, X (i t) w * X (j u) w * X (k v) w * X (l z) w ∂μ) *
        (∫ w, Y (a t) w * Y (b u) w * Y (c v) w * Y (d z) w ∂μ) := by
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  have hs := integral_sum_four _ (fun t u v z =>
    integrable_mixed_four h hX hY (i t) (j u) (k v) (l z) (a t) (b u) (c v) (d z))
  simp only [mul_assoc] at hs ⊢
  rw [hs]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro z _
  simpa only [mul_assoc] using
    integral_mixed_four h hXm hYm (i t) (j u) (k v) (l z) (a t) (b u) (c v) (d z)

/-- A constant feature absorbs the additive bias into the same finite sum. -/
def biasFeature {D J : Type*} (Q : D → J → Ω → ℝ) (a : D × Option J) (w : Ω) : ℝ :=
  match a.2 with
  | none => 1
  | some j => Q a.1 j w

def biasNoiseIndex {R J : Type*} (r : R) : Option J → (R × J) ⊕ R
  | none => Sum.inr r
  | some j => Sum.inl (r, j)

theorem biasNoiseIndex_eq_iff {R J : Type*} (r s : R) (j k : Option J) :
    biasNoiseIndex r j = biasNoiseIndex s k ↔ r = s ∧ j = k := by
  cases j <;> cases k <;> simp [biasNoiseIndex]

omit [MeasurableSpace Ω] in
theorem augmented_sum {D R J : Type*} [Fintype J]
    (X : (R × J) ⊕ R → Ω → ℝ) (Q : D → J → Ω → ℝ)
    (a : D) (r : R) (w : Ω) :
    (∑ j : Option J, X (biasNoiseIndex r j) w * biasFeature Q (a, j) w) =
      (∑ j : J, X (Sum.inl (r, j)) w * Q a j w) + X (Sum.inr r) w := by
  simp [Fintype.sum_option, biasNoiseIndex, biasFeature, add_comm]

theorem measurable_biasFeature {D J : Type*} {Q : D → J → Ω → ℝ}
    (hQ : ∀ a j, Measurable (Q a j)) (a : D × Option J) :
    Measurable (biasFeature Q a) := by
  rcases a with ⟨a, j⟩
  cases j with
  | none => exact measurable_const
  | some j => exact hQ a j

theorem memLp_biasFeature [IsFiniteMeasure μ] {D J : Type*} {Q : D → J → Ω → ℝ}
    (hQ : ∀ a j, MemLp (Q a j) 4 μ) (a : D × Option J) :
    MemLp (biasFeature Q a) 4 μ := by
  rcases a with ⟨a, j⟩
  cases j with
  | none => exact memLp_const 1
  | some j => exact hQ a j

theorem independent_biasFeature {D J : Type*} {X : N → Ω → ℝ} {Q : D → J → Ω → ℝ}
    (h : IndepFun (fun w => fun i => X i w) (fun w => fun a => fun j => Q a j w) μ) :
    IndepFun (fun w => fun i => X i w) (fun w => fun a => biasFeature Q a w) μ := by
  let F : (D → J → ℝ) → D × Option J → ℝ :=
    fun q a => match a.2 with | none => 1 | some j => q a.1 j
  have hm : Measurable F := by
    apply measurable_pi_lambda
    intro a
    rcases a with ⟨a, j⟩
    cases j with
    | none => exact measurable_const
    | some j => exact (measurable_pi_apply j).comp (measurable_pi_apply a)
  exact h.comp measurable_id hm

end S11Independence
end



set_option autoImplicit false
open scoped BigOperators

namespace S11ContractionSums

variable {J : Type*} [Fintype J] [DecidableEq J]

def diagonalEntry (v : J → ℝ) (i j : J) : ℝ := if i = j then v i else 0

theorem pair_sum (v : J → ℝ) (F : J → J → ℝ) :
    (∑ i, ∑ j, diagonalEntry v i j * F i j) = ∑ i, v i * F i i := by
  simp [diagonalEntry, ite_mul]

theorem first_pairing_sum (v : J → ℝ) (F : J → J → J → J → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      diagonalEntry v i j * diagonalEntry v k l * F i j k l) =
      ∑ i, ∑ k, v i * v k * F i i k k := by
  simp [diagonalEntry, ite_mul, mul_ite]

theorem second_pairing_sum (v : J → ℝ) (F : J → J → J → J → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      diagonalEntry v i k * diagonalEntry v j l * F i j k l) =
      ∑ i, ∑ j, v i * v j * F i j i j := by
  simp [diagonalEntry, ite_mul, mul_ite]

theorem third_pairing_sum (v : J → ℝ) (F : J → J → J → J → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      diagonalEntry v i l * diagonalEntry v j k * F i j k l) =
      ∑ i, ∑ j, v i * v j * F i j j i := by
  simp [diagonalEntry, ite_mul, mul_ite]

theorem wick_sum (v : J → ℝ) (F : J → J → J → J → ℝ) (d1 d2 d3 : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (d1 * (diagonalEntry v i j * diagonalEntry v k l) +
        d2 * (diagonalEntry v i k * diagonalEntry v j l) +
        d3 * (diagonalEntry v i l * diagonalEntry v j k)) * F i j k l) =
      d1 * (∑ i, ∑ k, v i * v k * F i i k k) +
      d2 * (∑ i, ∑ j, v i * v j * F i j i j) +
      d3 * (∑ i, ∑ j, v i * v j * F i j j i) := by
  simp [diagonalEntry, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite,
    Finset.mul_sum, mul_assoc]

theorem product_sum (v : J → ℝ) (F G : J → ℝ) :
    (∑ i, v i * F i) * (∑ j, v j * G j) =
      ∑ i, ∑ j, v i * v j * (F i * G j) := by
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted_covariance_sum (v : J → ℝ) (F : J → J → ℝ) (G H : J → ℝ) :
    (∑ i, ∑ j, v i * v j * F i j) - (∑ i, v i * G i) * (∑ j, v j * H j) =
      ∑ i, ∑ j, v i * v j * (F i j - G i * H j) := by
  rw [product_sum]
  simp [mul_sub, Finset.sum_sub_distrib]

end S11ContractionSums



set_option autoImplicit false

open scoped BigOperators

namespace S11CovarianceBound

theorem double_sum_bound {m : ℕ} (B : ℝ) (C : Fin m → Fin m → ℝ)
    (hC : ∀ j k, |C j k| ≤ B * (if j = k then 1 else 0)) :
    |∑ j, ∑ k, C j k| ≤ (m : ℝ) * B := by
  calc
    |∑ j, ∑ k, C j k| ≤ ∑ j, |∑ k, C j k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, |C j k| := Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin m, ∑ k : Fin m, B * (if j = k then 1 else 0) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hC j k
    _ = (m : ℝ) * B := by simp

/-- The analytic contraction identity leaves only three finite covariance sums. -/
theorem triple_contraction_bound (m : ℕ) (hm : 0 < m) (CW B : ℝ)
    (d1 d2 d3 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (C1 C2 C3 : Fin m → Fin m → ℝ)
    (h1 : ∀ j k, |C1 j k| ≤ B * (if j = k then 1 else 0))
    (h2 : ∀ j k, |C2 j k| ≤ B * (if j = k then 1 else 0))
    (h3 : ∀ j k, |C3 j k| ≤ B * (if j = k then 1 else 0)) :
    |(CW / (m : ℝ)) ^ 2 *
      (d1 * (∑ j, ∑ k, C1 j k) + d2 * (∑ j, ∑ k, C2 j k) +
        d3 * (∑ j, ∑ k, C3 j k))| ≤
      CW ^ 2 * B / (m : ℝ) * (d1 + d2 + d3) := by
  have hb1 := double_sum_bound B C1 h1
  have hb2 := double_sum_bound B C2 h2
  have hb3 := double_sum_bound B C3 h3
  have hscale : 0 ≤ (CW / (m : ℝ)) ^ 2 := sq_nonneg _
  have hinner :
      |d1 * (∑ j, ∑ k, C1 j k) + d2 * (∑ j, ∑ k, C2 j k) +
        d3 * (∑ j, ∑ k, C3 j k)| ≤
      d1 * ((m : ℝ) * B) + d2 * ((m : ℝ) * B) + d3 * ((m : ℝ) * B) := by
    calc
      _ ≤ |d1 * (∑ j, ∑ k, C1 j k)| + |d2 * (∑ j, ∑ k, C2 j k)| +
          |d3 * (∑ j, ∑ k, C3 j k)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = d1 * |∑ j, ∑ k, C1 j k| + d2 * |∑ j, ∑ k, C2 j k| +
          d3 * |∑ j, ∑ k, C3 j k| := by simp [abs_mul, abs_of_nonneg hd1, abs_of_nonneg hd2, abs_of_nonneg hd3]
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb1 hd1)
        (mul_le_mul_of_nonneg_left hb2 hd2)) (mul_le_mul_of_nonneg_left hb3 hd3)
  rw [abs_mul, abs_of_nonneg hscale]
  calc
    _ ≤ (CW / (m : ℝ)) ^ 2 *
        (d1 * ((m : ℝ) * B) + d2 * ((m : ℝ) * B) + d3 * ((m : ℝ) * B)) :=
      mul_le_mul_of_nonneg_left hinner hscale
    _ = _ := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
      field_simp [hm0]

end S11CovarianceBound



set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Intakenext100.P88
open S11Independence

namespace S11Augmented

def noiseVariance {R : Type*} (m : ℕ) (CW CB : ℝ≥0) : ((R × Fin m) ⊕ R) → ℝ≥0
  | Sum.inl _ => CW / (m : ℝ≥0)
  | Sum.inr _ => CB

def augmentedVariance (m : ℕ) (CW CB : ℝ≥0) : Option (Fin m) → ℝ
  | none => (CB : ℝ)
  | some _ => (CW : ℝ) / (m : ℝ)

theorem covarianceEntry_biasNoiseIndex {R : Type*} [DecidableEq R]
    (m : ℕ) (CW CB : ℝ≥0) (r s : R) (j k : Option (Fin m)) :
    S11Gaussian.covarianceEntry (noiseVariance m CW CB)
      (biasNoiseIndex r j) (biasNoiseIndex s k) =
      kd r s * (if j = k then augmentedVariance m CW CB j else 0) := by
  by_cases hrs : r = s
  · subst s
    by_cases hjk : j = k
    · subst k
      cases j <;>
        simp [S11Gaussian.covarianceEntry, biasNoiseIndex, noiseVariance,
          augmentedVariance, kd]
    · simp [S11Gaussian.covarianceEntry, biasNoiseIndex_eq_iff, hjk, kd]
  · simp [S11Gaussian.covarianceEntry, biasNoiseIndex_eq_iff, hrs, kd]

variable {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {h L m : ℕ} {CW CB : ℝ≥0}
    (S : HybridLayer μ D R h L m CW CB)

theorem noise_marginals (i : (R × Fin m) ⊕ R) :
    μ.map (S.noise i) = gaussianReal 0 (noiseVariance m CW CB i) := by
  cases i with
  | inl i => exact S.gaussian (Sum.inl i)
  | inr i => exact S.gaussian (Sum.inr i)

theorem noise_memLp_four (i : (R × Fin m) ⊕ R) : MemLp (S.noise i) 4 μ :=
  gaussian_memLp_four (S.measurable_noise i) (noise_marginals S i)

theorem preactivation_eq_augmented_sum (a : D) (r : R) :
    preactivation S a r = fun w => ∑ j : Option (Fin m),
      S.noise (biasNoiseIndex r j) w *
        biasFeature (incomingQuantumOutput S.quantum) (a, j) w := by
  funext w
  exact (augmented_sum S.noise (incomingQuantumOutput S.quantum) a r w).symm

theorem noise_pair (r s : R) (j k : Option (Fin m)) :
    (∫ w, S.noise (biasNoiseIndex r j) w * S.noise (biasNoiseIndex s k) w ∂μ) =
      kd r s * (if j = k then augmentedVariance m CW CB j else 0) :=
  (S11Gaussian.gaussian_pair S.noise (noiseVariance m CW CB) S.measurable_noise
    (noise_marginals S) S.independent_noise (biasNoiseIndex r j) (biasNoiseIndex s k)).trans
    (covarianceEntry_biasNoiseIndex m CW CB r s j k)

theorem noise_wick (r s t u : R) (i j k l : Option (Fin m)) :
    (∫ w, S.noise (biasNoiseIndex r i) w * S.noise (biasNoiseIndex s j) w *
      S.noise (biasNoiseIndex t k) w * S.noise (biasNoiseIndex u l) w ∂μ) =
      (kd r s * kd t u) *
        ((if i = j then augmentedVariance m CW CB i else 0) *
          (if k = l then augmentedVariance m CW CB k else 0)) +
      (kd r t * kd s u) *
        ((if i = k then augmentedVariance m CW CB i else 0) *
          (if j = l then augmentedVariance m CW CB j else 0)) +
      (kd r u * kd s t) *
        ((if i = l then augmentedVariance m CW CB i else 0) *
          (if j = k then augmentedVariance m CW CB j else 0)) := by
  have hw := S11Gaussian.gaussian_wick_four S.noise (noiseVariance m CW CB)
    S.measurable_noise (noise_marginals S) S.independent_noise
    (biasNoiseIndex r i) (biasNoiseIndex s j) (biasNoiseIndex t k) (biasNoiseIndex u l)
  simp_rw [covarianceEntry_biasNoiseIndex] at hw
  rw [hw]
  ring

def augmentedCovariance (a b c d : D) (j k : Option (Fin m)) : ℝ :=
  (∫ w, biasFeature (incomingQuantumOutput S.quantum) (a, j) w *
    biasFeature (incomingQuantumOutput S.quantum) (b, j) w *
    biasFeature (incomingQuantumOutput S.quantum) (c, k) w *
    biasFeature (incomingQuantumOutput S.quantum) (d, k) w ∂μ) -
  (∫ w, biasFeature (incomingQuantumOutput S.quantum) (a, j) w *
    biasFeature (incomingQuantumOutput S.quantum) (b, j) w ∂μ) *
  (∫ w, biasFeature (incomingQuantumOutput S.quantum) (c, k) w *
    biasFeature (incomingQuantumOutput S.quantum) (d, k) w ∂μ)

@[simp] theorem augmentedCovariance_none_left (a b c d : D) (k : Option (Fin m)) :
    augmentedCovariance S a b c d none k = 0 := by
  simp [augmentedCovariance, biasFeature]

@[simp] theorem augmentedCovariance_none_right (a b c d : D) (j : Option (Fin m)) :
    augmentedCovariance S a b c d j none = 0 := by
  simp [augmentedCovariance, biasFeature]

@[simp] theorem augmentedCovariance_some_some (a b c d : D) (j k : Fin m) :
    augmentedCovariance S a b c d (some j) (some k) =
      productCovariance μ S.quantum a b c d j k := rfl

theorem weighted_augmentedCovariance (a b c d : D) :
    (∑ j : Option (Fin m), ∑ k : Option (Fin m),
      augmentedVariance m CW CB j * augmentedVariance m CW CB k *
        augmentedCovariance S a b c d j k) =
      ((CW : ℝ) / (m : ℝ)) ^ 2 * ∑ j : Fin m, ∑ k : Fin m,
        productCovariance μ S.quantum a b c d j k := by
  simp [Fintype.sum_option, augmentedVariance, Finset.mul_sum, pow_two, mul_assoc]

end S11Augmented
end


set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Intakenext100.P88
open S11Independence S11Augmented S11ContractionSums

namespace S11Moments

variable {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {h L m : ℕ} {CW CB : ℝ≥0}
    (S : HybridLayer μ D R h L m CW CB)

def pairFeatureMoment (a b : D) : ℝ :=
  ∑ j : Option (Fin m), augmentedVariance m CW CB j *
    ∫ w, biasFeature (incomingQuantumOutput S.quantum) (a, j) w *
      biasFeature (incomingQuantumOutput S.quantum) (b, j) w ∂μ

def fourthFeatureMoment (a b c d : D) : ℝ :=
  ∑ j : Option (Fin m), ∑ k : Option (Fin m),
    augmentedVariance m CW CB j * augmentedVariance m CW CB k *
      ∫ w, biasFeature (incomingQuantumOutput S.quantum) (a, j) w *
        biasFeature (incomingQuantumOutput S.quantum) (b, j) w *
        biasFeature (incomingQuantumOutput S.quantum) (c, k) w *
        biasFeature (incomingQuantumOutput S.quantum) (d, k) w ∂μ

theorem pair_moment (a b : D) (r s : R) :
    (∫ w, preactivation S a r w * preactivation S b s w ∂μ) =
      kd r s * pairFeatureMoment S a b := by
  rw [preactivation_eq_augmented_sum S a r, preactivation_eq_augmented_sum S b s]
  rw [integral_linear_two (independent_biasFeature S.independent_quantum)
    S.measurable_noise (measurable_biasFeature S.measurable_quantum)
    (noise_memLp_four S) (memLp_biasFeature S.fourth_moment)
    (biasNoiseIndex r) (fun j => (a, j)) (biasNoiseIndex s) (fun j => (b, j))]
  simp_rw [noise_pair]
  simp [pairFeatureMoment, Finset.mul_sum, mul_assoc, ite_mul, mul_ite, mul_add]

theorem fourth_moment (a b c d : D) (r s t u : R) :
    (∫ w, preactivation S a r w * preactivation S b s w *
      preactivation S c t w * preactivation S d u w ∂μ) =
      (kd r s * kd t u) * fourthFeatureMoment S a b c d +
      (kd r t * kd s u) * fourthFeatureMoment S a c b d +
      (kd r u * kd s t) * fourthFeatureMoment S a d b c := by
  rw [preactivation_eq_augmented_sum S a r, preactivation_eq_augmented_sum S b s,
    preactivation_eq_augmented_sum S c t, preactivation_eq_augmented_sum S d u]
  rw [integral_linear_four (independent_biasFeature S.independent_quantum)
    S.measurable_noise (measurable_biasFeature S.measurable_quantum)
    (noise_memLp_four S) (memLp_biasFeature S.fourth_moment)
    (biasNoiseIndex r) (fun j => (a, j)) (biasNoiseIndex s) (fun j => (b, j))
    (biasNoiseIndex t) (fun j => (c, j)) (biasNoiseIndex u) (fun j => (d, j))]
  simp_rw [noise_wick]
  change (∑ i, ∑ j, ∑ k, ∑ l,
    ((kd r s * kd t u) *
      (diagonalEntry (augmentedVariance m CW CB) i j *
        diagonalEntry (augmentedVariance m CW CB) k l) +
     (kd r t * kd s u) *
      (diagonalEntry (augmentedVariance m CW CB) i k *
        diagonalEntry (augmentedVariance m CW CB) j l) +
     (kd r u * kd s t) *
      (diagonalEntry (augmentedVariance m CW CB) i l *
        diagonalEntry (augmentedVariance m CW CB) j k)) *
      (∫ w, biasFeature (incomingQuantumOutput S.quantum) (a, i) w *
        biasFeature (incomingQuantumOutput S.quantum) (b, j) w *
        biasFeature (incomingQuantumOutput S.quantum) (c, k) w *
        biasFeature (incomingQuantumOutput S.quantum) (d, l) w ∂μ)) = _
  rw [wick_sum]
  have h2 : (∑ i : Option (Fin m), ∑ j : Option (Fin m),
      augmentedVariance m CW CB i * augmentedVariance m CW CB j *
        (∫ w, biasFeature (incomingQuantumOutput S.quantum) (a, i) w *
          biasFeature (incomingQuantumOutput S.quantum) (b, j) w *
          biasFeature (incomingQuantumOutput S.quantum) (c, i) w *
          biasFeature (incomingQuantumOutput S.quantum) (d, j) w ∂μ)) =
      fourthFeatureMoment S a c b d := by
    unfold fourthFeatureMoment
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    ring
  have h3 : (∑ i : Option (Fin m), ∑ j : Option (Fin m),
      augmentedVariance m CW CB i * augmentedVariance m CW CB j *
        (∫ w, biasFeature (incomingQuantumOutput S.quantum) (a, i) w *
          biasFeature (incomingQuantumOutput S.quantum) (b, j) w *
          biasFeature (incomingQuantumOutput S.quantum) (c, j) w *
          biasFeature (incomingQuantumOutput S.quantum) (d, i) w ∂μ)) =
      fourthFeatureMoment S a d b c := by
    unfold fourthFeatureMoment
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    ring
  rw [h2, h3]
  rfl

theorem feature_covariance (a b c d : D) :
    fourthFeatureMoment S a b c d - pairFeatureMoment S a b * pairFeatureMoment S c d =
      ((CW : ℝ) / (m : ℝ)) ^ 2 * ∑ j : Fin m, ∑ k : Fin m,
        productCovariance μ S.quantum a b c d j k := by
  calc
    _ = ∑ j : Option (Fin m), ∑ k : Option (Fin m),
      augmentedVariance m CW CB j * augmentedVariance m CW CB k *
        augmentedCovariance S a b c d j k := by
      exact weighted_covariance_sum (augmentedVariance m CW CB) _ _ _
    _ = _ := weighted_augmentedCovariance S a b c d

theorem connected_four_eq_contraction (a b c d : D) (r s t u : R) :
    connectedFour μ (preactivation S a r) (preactivation S b s)
      (preactivation S c t) (preactivation S d u) =
        fourContraction S a b c d r s t u := by
  unfold connectedFour
  rw [fourth_moment, pair_moment, pair_moment, pair_moment,
    pair_moment, pair_moment, pair_moment]
  calc
    _ = (kd r s * kd t u) *
        (fourthFeatureMoment S a b c d - pairFeatureMoment S a b * pairFeatureMoment S c d) +
      (kd r t * kd s u) *
        (fourthFeatureMoment S a c b d - pairFeatureMoment S a c * pairFeatureMoment S b d) +
      (kd r u * kd s t) *
        (fourthFeatureMoment S a d b c - pairFeatureMoment S a d * pairFeatureMoment S b c) := by
      ring
    _ = _ := by
      rw [feature_covariance, feature_covariance, feature_covariance]
      unfold fourContraction
      ring

end S11Moments
end



set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Intakenext100.P88

theorem solution (CW CB : ℝ≥0) (B : ℝ) (hB : 0 ≤ B) :
    ∀ {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {h L m : ℕ}
      (S : HybridLayer μ D R h L m CW CB),
      (∀ (a b c d : D) (j k : Fin m),
        |productCovariance μ S.quantum a b c d j k| ≤ B * kd j k) →
      ∀ (a b c d : D) (r s t u : R),
        |connectedFour μ (preactivation S a r) (preactivation S b s)
          (preactivation S c t) (preactivation S d u)| ≤
        (CW : ℝ) ^ 2 * B / (m : ℝ) *
          (kd r s * kd t u + kd r t * kd s u + kd r u * kd s t) := by
  intro Ω D R _ _ _ μ _ h L m S hCov a b c d r s t u
  rw [S11Moments.connected_four_eq_contraction]
  have hk (x y : R) : 0 ≤ kd x y := by
    unfold kd
    split <;> norm_num
  exact S11CovarianceBound.triple_contraction_bound m S.width_pos (CW : ℝ) B
    (kd r s * kd t u) (kd r t * kd s u) (kd r u * kd s t)
    (mul_nonneg (hk r s) (hk t u)) (mul_nonneg (hk r t) (hk s u))
    (mul_nonneg (hk r u) (hk s t))
    (productCovariance μ S.quantum a b c d)
    (productCovariance μ S.quantum a c b d)
    (productCovariance μ S.quantum a d b c)
    (hCov a b c d) (hCov a c b d) (hCov a d b c)

end


#print axioms solution
