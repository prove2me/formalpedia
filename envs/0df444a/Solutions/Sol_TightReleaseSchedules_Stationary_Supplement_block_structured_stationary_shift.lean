-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.Supplement.block_structured_stationary_shift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T18:09:10.750915+00:00
-- url     : https://prove2.me/submissions/2e48a000-1d1d-44a8-b04d-71b7fa048209

import Definitions.Def_TightReleaseSchedules_Stationary_gaussian_experiment
import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_block_class
import Theorems.Thm_TightReleaseSchedules_Stationary_common_lower_error_event

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary

namespace TRS.Dev.BlockMoments

lemma deriv_step (p p' q : ℝ → ℝ) (hp : ∀ t, HasDerivAt p (p' t) t)
    (hq : ∀ t, p' t + t * p t = q t) :
    deriv (fun t : ℝ => p t * Real.exp (t ^ 2 / 2)) =
      fun t => q t * Real.exp (t ^ 2 / 2) := by
  ext t
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2))
      (Real.exp (t ^ 2 / 2) * t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert this using 1
    simp
  have := (hp t).mul h2
  have h3 := this.deriv
  change deriv (fun t => p t * Real.exp (t ^ 2 / 2)) t = _ at h3
  rw [h3, ← hq t]
  ring

/-- Fourth moment of a standard real Gaussian. -/
lemma moment4 : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h0 : (0:ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp [integrableExpSet_fun_id_gaussianReal]
  have := iteratedDeriv_mgf_zero h0 4
  simp only [Pi.pow_apply] at this
  rw [mgf_fun_id_gaussianReal] at this
  have hf : (fun t : ℝ => Real.exp (0 * t + ((1:ℝ≥0):ℝ) * t ^ 2 / 2)) =
      fun t => (fun _ => (1:ℝ)) t * Real.exp (t ^ 2 / 2) := by
    ext t; simp
  rw [hf] at this
  have s1 := deriv_step (fun _ => (1:ℝ)) (fun _ => 0) (fun t => t)
    (fun t => hasDerivAt_const t 1) (fun t => by ring)
  have s2 := deriv_step (fun t => t) (fun _ => 1) (fun t => t ^ 2 + 1)
    (fun t => hasDerivAt_id' t) (fun t => by ring)
  have s3 := deriv_step (fun t => t ^ 2 + 1) (fun t => 2 * t) (fun t => t ^ 3 + 3 * t)
    (fun t => by simpa using (hasDerivAt_pow 2 t).add_const 1) (fun t => by ring)
  have s4 := deriv_step (fun t => t ^ 3 + 3 * t) (fun t => 3 * t ^ 2 + 3)
    (fun t => t ^ 4 + 6 * t ^ 2 + 3)
    (fun t => by
      have h : HasDerivAt (fun t : ℝ => t ^ 3 + 3 * t) (((3:ℕ):ℝ) * t ^ (3 - 1) + 3 * 1) t :=
        (hasDerivAt_pow 3 t).add ((hasDerivAt_id' t).const_mul 3)
      exact h.congr_deriv (by norm_num)) (fun t => by ring)
  rw [iteratedDeriv_succ', s1, iteratedDeriv_succ', s2, iteratedDeriv_succ', s3,
    iteratedDeriv_succ', s4, iteratedDeriv_zero] at this
  rw [← this]
  norm_num

/-- The product of `d` independent standard Gaussians. -/
noncomputable abbrev nu (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

/-- One-dimensional moments. -/
noncomputable def mom (n : ℕ) : ℝ := ∫ x, x ^ n ∂(gaussianReal 0 1)

lemma mom_zero : mom 0 = 1 := by simp [mom]
lemma mom_one : mom 1 = 0 := by simp [mom, integral_id_gaussianReal]
lemma mom_two : mom 2 = 1 := by
  have := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at this
  simpa [mom, integral_id_gaussianReal] using this
lemma mom_four : mom 4 = 3 := moment4

lemma integral_monomial {d : ℕ} (c : Fin d → ℕ) :
    ∫ y, ∏ j, y j ^ c j ∂(nu d) = ∏ j, mom (c j) := by
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin d => gaussianReal 0 1)
    (fun j (x : ℝ) => x ^ c j)
  simpa [mom] using this

lemma monomial4 {d : ℕ} (y : Fin d → ℝ) (a b k l : Fin d) :
    ∏ j, y j ^ ((if a = j then 1 else 0) + (if b = j then 1 else 0) + (if k = j then 1 else 0)
      + (if l = j then 1 else 0)) = y a * y b * y k * y l := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq, Finset.mem_univ, if_true]

lemma monomial2 {d : ℕ} (y : Fin d → ℝ) (a b : Fin d) :
    ∏ j, y j ^ ((if a = j then 1 else 0) + (if b = j then 1 else 0)) = y a * y b := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq, Finset.mem_univ, if_true]

lemma moment_two {d : ℕ} (a b : Fin d) :
    ∫ y, y a * y b ∂(nu d) = if a = b then 1 else 0 := by
  have := integral_monomial (d := d) (fun j => (if a = j then 1 else 0) + (if b = j then 1 else 0))
  simp only [monomial2] at this
  rw [this]
  by_cases hab : a = b
  · subst hab
    rw [Finset.prod_eq_single a]
    · simp [mom_two]
    · intro j _ hj
      simp [Ne.symm hj, mom_zero]
    · simp
  · rw [if_neg hab]
    refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    simp [hab, Ne.symm hab, mom_one]

lemma moment_four {d : ℕ} (a b k l : Fin d) :
    ∫ y, y a * y b * y k * y l ∂(nu d) =
      (if a = b then 1 else 0) * (if k = l then 1 else 0) +
      (if a = k then 1 else 0) * (if b = l then 1 else 0) +
      (if a = l then 1 else 0) * (if b = k then 1 else 0) := by
  have := integral_monomial (d := d) (fun j => (if a = j then 1 else 0) + (if b = j then 1 else 0)
    + (if k = j then 1 else 0) + (if l = j then 1 else 0))
  simp only [monomial4] at this
  rw [this]
  clear this
  by_cases hab : a = b
  · subst hab
    by_cases hak : a = k
    · subst hak
      by_cases hal : a = l
      · subst hal
        rw [Finset.prod_eq_single a]
        · simp [mom_four]; norm_num
        · intro j _ hj
          simp [Ne.symm hj, mom_zero]
        · simp
      · refine (Finset.prod_eq_zero (Finset.mem_univ l) ?_).trans ?_
        · simp [*, mom_one]
        · simp [hal]
    · by_cases hkl : k = l
      · subst hkl
        rw [Finset.prod_eq_mul a k hak]
        · simp [hak, Ne.symm hak, mom_two]
        · intro j _ hj
          simp [Ne.symm hj.1, Ne.symm hj.2, mom_zero]
        · simp
        · simp
      · refine (Finset.prod_eq_zero (Finset.mem_univ k) ?_).trans ?_
        · simp [*, Ne.symm hkl, mom_one]
        · simp [hak, hkl]
  · by_cases hak : a = k
    · subst hak
      by_cases hbl : b = l
      · subst hbl
        rw [Finset.prod_eq_mul a b hab]
        · simp [hab, Ne.symm hab, mom_two]
        · intro j _ hj
          simp [Ne.symm hj.1, Ne.symm hj.2, mom_zero]
        · simp
        · simp
      · by_cases hal : a = l
        · subst hal
          refine (Finset.prod_eq_zero (Finset.mem_univ b) ?_).trans ?_
          · simp [*, mom_one]
          · simp [hab, Ne.symm hab]
        · refine (Finset.prod_eq_zero (Finset.mem_univ b) ?_).trans ?_
          · simp [*, Ne.symm hbl, mom_one]
          · simp [hab, hbl, hal]
    · by_cases hal : a = l
      · subst hal
        by_cases hbk : b = k
        · subst hbk
          rw [Finset.prod_eq_mul a b hab]
          · simp [hab, Ne.symm hab, mom_two]
          · intro j _ hj
            simp [Ne.symm hj.1, Ne.symm hj.2, mom_zero]
          · simp
          · simp
        · refine (Finset.prod_eq_zero (Finset.mem_univ k) ?_).trans ?_
          · simp [*, mom_one]
          · simp [hab, hak, hbk]
      · refine (Finset.prod_eq_zero (Finset.mem_univ a) ?_).trans ?_
        · simp [*, Ne.symm hab, Ne.symm hak, Ne.symm hal, mom_one]
        · simp [hab, hak, hal]

lemma integrable_pow_gaussian (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) n).integrable_norm_pow'
  refine h.mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall (fun x => by simp [norm_pow])

lemma integrable_monomial {d : ℕ} (c : Fin d → ℕ) :
    Integrable (fun y : Fin d → ℝ => ∏ j, y j ^ c j) (nu d) :=
  Integrable.fintype_prod (f := fun j (x : ℝ) => x ^ c j) (fun j => integrable_pow_gaussian _)

lemma monomial3 {d : ℕ} (y : Fin d → ℝ) (a k l : Fin d) :
    ∏ j, y j ^ ((if a = j then 1 else 0) + (if k = j then 1 else 0) + (if l = j then 1 else 0))
      = y a * y k * y l := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq, Finset.mem_univ, if_true]

lemma integrable_two {d : ℕ} (a b : Fin d) : Integrable (fun y : Fin d → ℝ => y a * y b) (nu d) := by
  have := integrable_monomial (d := d)
    (fun j => (if a = j then 1 else 0) + (if b = j then 1 else 0))
  simpa only [monomial2] using this

lemma integrable_one {d : ℕ} (a : Fin d) : Integrable (fun y : Fin d → ℝ => y a) (nu d) := by
  have := integrable_monomial (d := d) (fun j => (if a = j then 1 else 0))
  simpa using this

lemma integrable_three {d : ℕ} (a k l : Fin d) :
    Integrable (fun y : Fin d → ℝ => y a * y k * y l) (nu d) := by
  have := integrable_monomial (d := d)
    (fun j => (if a = j then 1 else 0) + (if k = j then 1 else 0) + (if l = j then 1 else 0))
  simpa only [monomial3] using this

lemma integrable_four {d : ℕ} (a b k l : Fin d) :
    Integrable (fun y : Fin d → ℝ => y a * y b * y k * y l) (nu d) := by
  have := integrable_monomial (d := d)
    (fun j => (if a = j then 1 else 0) + (if b = j then 1 else 0) + (if k = j then 1 else 0)
      + (if l = j then 1 else 0))
  simpa only [monomial4] using this

/-- The product measure on (design, noise). -/
noncomputable abbrev om (d : ℕ) : Measure ((Fin d → ℝ) × ℝ) :=
  (nu d).prod (gaussianReal 0 1)

lemma integrable_prod_mul {d : ℕ} (f : (Fin d → ℝ) → ℝ) (g : ℝ → ℝ)
    (hf : Integrable f (nu d)) (hg : Integrable g (gaussianReal 0 1)) :
    Integrable (fun w : (Fin d → ℝ) × ℝ => f w.1 * g w.2) (om d) :=
  hf.mul_prod hg

lemma integrable_eps_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  integrable_pow_gaussian n

lemma integral_eps_one : ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

lemma integral_eps_two : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := mom_two

/-- The cross moment coordinate function. -/
def Yf {d : ℕ} (β : Fin d → ℝ) (k : Fin d) (w : (Fin d → ℝ) × ℝ) : ℝ :=
  (∑ a, β a * w.1 a + w.2) * w.1 k

lemma Yf_expand {d : ℕ} (β : Fin d → ℝ) (k : Fin d) (w : (Fin d → ℝ) × ℝ) :
    Yf β k w = (∑ a, β a * (w.1 a * w.1 k)) * (1:ℝ) + w.1 k * w.2 := by
  simp only [Yf, add_mul, Finset.sum_mul, mul_assoc, mul_one]
  ring

lemma YY_expand {d : ℕ} (β : Fin d → ℝ) (k l : Fin d) (w : (Fin d → ℝ) × ℝ) :
    Yf β k w * Yf β l w =
      (∑ a, ∑ b, β a * β b * (w.1 a * w.1 b * w.1 k * w.1 l)) * (1:ℝ) +
      (∑ a, 2 * β a * (w.1 a * w.1 k * w.1 l)) * w.2 + (w.1 k * w.1 l) * w.2 ^ 2 := by
  have h : (∑ a, β a * w.1 a) ^ 2 = ∑ a, ∑ b, β a * w.1 a * (β b * w.1 b) := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : (∑ a, β a * w.1 a) * w.1 k * w.1 l = ∑ a, β a * (w.1 a * w.1 k * w.1 l) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have h3 : (∑ a, ∑ b, β a * β b * (w.1 a * w.1 b * w.1 k * w.1 l)) =
      (∑ a, β a * w.1 a) ^ 2 * (w.1 k * w.1 l) := by
    rw [h, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  have h4 : (∑ a, 2 * β a * (w.1 a * w.1 k * w.1 l)) =
      2 * ((∑ a, β a * w.1 a) * w.1 k * w.1 l) := by
    rw [h2, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [h3, h4]
  simp only [Yf]
  ring

lemma integrable_eps : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
  simpa using integrable_pow_gaussian 1

lemma integrable_Yf {d : ℕ} (β : Fin d → ℝ) (k : Fin d) : Integrable (Yf β k) (om d) := by
  have : Yf β k = fun w => (∑ a, β a * (w.1 a * w.1 k)) * (1:ℝ) + w.1 k * w.2 :=
    funext (Yf_expand β k)
  rw [this]
  refine Integrable.add ?_ ?_
  · exact integrable_prod_mul (fun y => ∑ a, β a * (y a * y k)) (fun _ => (1:ℝ))
      (integrable_finsetSum _ (fun a _ => (integrable_two a k).const_mul _)) (integrable_const _)
  · exact integrable_prod_mul (fun y => y k) (fun x => x) (integrable_one k) integrable_eps

lemma integral_Yf {d : ℕ} (β : Fin d → ℝ) (k : Fin d) : ∫ w, Yf β k w ∂(om d) = β k := by
  have : Yf β k = fun w => (∑ a, β a * (w.1 a * w.1 k)) * (1:ℝ) + w.1 k * w.2 :=
    funext (Yf_expand β k)
  have h1 : Integrable (fun w : (Fin d → ℝ) × ℝ => (∑ a, β a * (w.1 a * w.1 k)) * (1:ℝ)) (om d) :=
    integrable_prod_mul (fun y => ∑ a, β a * (y a * y k)) (fun _ => (1:ℝ))
      (integrable_finsetSum _ (fun a _ => (integrable_two a k).const_mul _)) (integrable_const _)
  have h2 : Integrable (fun w : (Fin d → ℝ) × ℝ => w.1 k * w.2) (om d) :=
    integrable_prod_mul (fun y => y k) (fun x => x) (integrable_one k) integrable_eps
  rw [this, integral_add h1 h2]
  rw [integral_prod_mul (fun y : Fin d → ℝ => ∑ a, β a * (y a * y k)) (fun _ : ℝ => (1:ℝ)),
    integral_prod_mul (fun y : Fin d → ℝ => y k) (fun x : ℝ => x)]
  rw [integral_finsetSum _ (fun a _ => (integrable_two a k).const_mul _)]
  simp [integral_const_mul, moment_two, integral_eps_one]

lemma integrable_YY {d : ℕ} (β : Fin d → ℝ) (k l : Fin d) :
    Integrable (fun w => Yf β k w * Yf β l w) (om d) := by
  have : (fun w => Yf β k w * Yf β l w) = fun w : (Fin d → ℝ) × ℝ =>
      (∑ a, ∑ b, β a * β b * (w.1 a * w.1 b * w.1 k * w.1 l)) * (1:ℝ) +
      (∑ a, 2 * β a * (w.1 a * w.1 k * w.1 l)) * w.2 + (w.1 k * w.1 l) * w.2 ^ 2 :=
    funext (YY_expand β k l)
  rw [this]
  refine Integrable.add (Integrable.add ?_ ?_) ?_
  · exact integrable_prod_mul (fun y => ∑ a, ∑ b, β a * β b * (y a * y b * y k * y l))
      (fun _ => (1:ℝ))
      (integrable_finsetSum _ (fun a _ => integrable_finsetSum _
        (fun b _ => (integrable_four a b k l).const_mul _))) (integrable_const _)
  · exact integrable_prod_mul (fun y => ∑ a, 2 * β a * (y a * y k * y l)) (fun x => x)
      (integrable_finsetSum _ (fun a _ => (integrable_three a k l).const_mul _)) integrable_eps
  · exact integrable_prod_mul (fun y => y k * y l) (fun x => x ^ 2) (integrable_two k l)
      (integrable_eps_pow 2)

lemma integral_YY {d : ℕ} (β : Fin d → ℝ) (k l : Fin d) :
    ∫ w, Yf β k w * Yf β l w ∂(om d) =
      (∑ a, β a ^ 2) * (if k = l then 1 else 0) + 2 * β k * β l + (if k = l then 1 else 0) := by
  have : (fun w => Yf β k w * Yf β l w) = fun w : (Fin d → ℝ) × ℝ =>
      (∑ a, ∑ b, β a * β b * (w.1 a * w.1 b * w.1 k * w.1 l)) * (1:ℝ) +
      (∑ a, 2 * β a * (w.1 a * w.1 k * w.1 l)) * w.2 + (w.1 k * w.1 l) * w.2 ^ 2 :=
    funext (YY_expand β k l)
  have h1 : Integrable (fun w : (Fin d → ℝ) × ℝ =>
      (∑ a, ∑ b, β a * β b * (w.1 a * w.1 b * w.1 k * w.1 l)) * (1:ℝ)) (om d) :=
    integrable_prod_mul (fun y => ∑ a, ∑ b, β a * β b * (y a * y b * y k * y l))
      (fun _ => (1:ℝ))
      (integrable_finsetSum _ (fun a _ => integrable_finsetSum _
        (fun b _ => (integrable_four a b k l).const_mul _))) (integrable_const _)
  have h2 : Integrable (fun w : (Fin d → ℝ) × ℝ =>
      (∑ a, 2 * β a * (w.1 a * w.1 k * w.1 l)) * w.2) (om d) :=
    integrable_prod_mul (fun y => ∑ a, 2 * β a * (y a * y k * y l)) (fun x => x)
      (integrable_finsetSum _ (fun a _ => (integrable_three a k l).const_mul _)) integrable_eps
  have h3 : Integrable (fun w : (Fin d → ℝ) × ℝ => (w.1 k * w.1 l) * w.2 ^ 2) (om d) :=
    integrable_prod_mul (fun y => y k * y l) (fun x => x ^ 2) (integrable_two k l)
      (integrable_eps_pow 2)
  have e1 := integral_add (h1.add h2) h3
  have e2 := integral_add h1 h2
  simp only [Pi.add_apply] at e1
  rw [this, e1, e2]
  rw [integral_prod_mul (fun y : Fin d → ℝ => ∑ a, ∑ b, β a * β b * (y a * y b * y k * y l))
      (fun _ : ℝ => (1:ℝ)),
    integral_prod_mul (fun y : Fin d → ℝ => ∑ a, 2 * β a * (y a * y k * y l)) (fun x : ℝ => x),
    integral_prod_mul (fun y : Fin d → ℝ => y k * y l) (fun x : ℝ => x ^ 2)]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
        (fun b _ => (integrable_four a b k l).const_mul _))]
  simp_rw [integral_finsetSum _ (fun b _ => (integrable_four _ b k l).const_mul _)]
  simp [integral_const_mul, moment_four, integral_eps_one, moment_two, integral_eps_two]
  by_cases hkl : k = l
  · subst hkl
    simp [mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq, ← sq, ite_mul, mul_ite, two_mul]
    ring
  · simp [hkl, mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq, ite_mul, mul_ite, two_mul,
      Ne.symm hkl]
    ring

/-- Coordinates of a row. -/
def Phi (T d : ℕ) (i : Fin T) (z : GaussianRows T d) : (Fin d → ℝ) × ℝ :=
  (fun k => (z i).1 k, (z i).2)

lemma measurable_Phi (T d : ℕ) (i : Fin T) : Measurable (Phi T d i) := by
  unfold Phi
  fun_prop

lemma map_Phi (T d : ℕ) (i : Fin T) : (gaussianRows T d).map (Phi T d i) = om d := by
  have h1 : (gaussianRows T d).map (fun z : GaussianRows T d => z i) =
      (stdGaussian (Vector d)).prod (gaussianReal 0 1) :=
    (measurePreserving_eval (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1))
      i).map_eq
  have h2 : (stdGaussian (Vector d)).map (fun x : Vector d => (x : Fin d → ℝ)) = nu d := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id'
  have : Phi T d i = (Prod.map (fun x : Vector d => (x : Fin d → ℝ)) id) ∘
      (fun z : GaussianRows T d => z i) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), h1,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h2, Measure.map_id]

lemma measurable_Yf {d : ℕ} (β : Fin d → ℝ) (k : Fin d) : Measurable (Yf β k) := by
  unfold Yf
  fun_prop

lemma integrable_transfer {T d : ℕ} (i : Fin T) (G : (Fin d → ℝ) × ℝ → ℝ) (hG : Measurable G)
    (h : Integrable G (om d)) : Integrable (fun z => G (Phi T d i z)) (gaussianRows T d) := by
  rw [← map_Phi T d i] at h
  exact (integrable_map_measure hG.aestronglyMeasurable
    (measurable_Phi T d i).aemeasurable).1 h

lemma integral_transfer {T d : ℕ} (i : Fin T) (G : (Fin d → ℝ) × ℝ → ℝ) (hG : Measurable G) :
    ∫ z, G (Phi T d i z) ∂(gaussianRows T d) = ∫ w, G w ∂(om d) := by
  rw [← map_Phi T d i, integral_map (measurable_Phi T d i).aemeasurable hG.aestronglyMeasurable]

lemma cross_apply {T d : ℕ} (θ₀ : Vector d) (θ : Fin T → Vector d) (i : Fin T)
    (z : GaussianRows T d) (k : Fin d) :
    crossMoment θ₀ (observations θ z i) k = Yf (fun a => (θ i - θ₀) a) k (Phi T d i z) := by
  simp only [crossMoment, observations, Yf, Phi, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
    PiLp.sub_apply, RCLike.inner_apply, conj_trivial]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

instance instProbGR (T d : ℕ) : IsProbabilityMeasure (gaussianRows T d) := by
  unfold gaussianRows
  infer_instance

section Row

variable {T d : ℕ} (θ₀ : Vector d) (θ : Fin T → Vector d) (i : Fin T)

lemma cross_fun_eq (k : Fin d) :
    (fun z => crossMoment θ₀ (observations θ z i) k) =
      fun z => Yf (fun a => (θ i - θ₀) a) k (Phi T d i z) :=
  funext (fun z => cross_apply θ₀ θ i z k)

lemma cross_integrable_coord (k : Fin d) :
    Integrable (fun z => crossMoment θ₀ (observations θ z i) k) (gaussianRows T d) := by
  rw [cross_fun_eq]
  exact integrable_transfer i _ (measurable_Yf _ k) (integrable_Yf _ k)

lemma cross_integral_coord (k : Fin d) :
    ∫ z, crossMoment θ₀ (observations θ z i) k ∂(gaussianRows T d) = (θ i - θ₀) k := by
  rw [cross_fun_eq, integral_transfer i _ (measurable_Yf _ k), integral_Yf]

lemma cross_integrable_mul (k l : Fin d) :
    Integrable (fun z => crossMoment θ₀ (observations θ z i) k *
      crossMoment θ₀ (observations θ z i) l) (gaussianRows T d) := by
  have : (fun z => crossMoment θ₀ (observations θ z i) k *
      crossMoment θ₀ (observations θ z i) l) =
      fun z => (fun w => Yf (fun a => (θ i - θ₀) a) k w * Yf (fun a => (θ i - θ₀) a) l w)
        (Phi T d i z) := funext (fun z => by rw [cross_apply, cross_apply])
  rw [this]
  exact integrable_transfer i _ ((measurable_Yf _ k).mul (measurable_Yf _ l)) (integrable_YY _ k l)

lemma cross_integral_mul (k l : Fin d) :
    ∫ z, crossMoment θ₀ (observations θ z i) k * crossMoment θ₀ (observations θ z i) l
      ∂(gaussianRows T d) =
      (∑ a, ((θ i - θ₀) a) ^ 2) * (if k = l then 1 else 0) + 2 * (θ i - θ₀) k * (θ i - θ₀) l
        + (if k = l then 1 else 0) := by
  have : (fun z => crossMoment θ₀ (observations θ z i) k *
      crossMoment θ₀ (observations θ z i) l) =
      fun z => (fun w => Yf (fun a => (θ i - θ₀) a) k w * Yf (fun a => (θ i - θ₀) a) l w)
        (Phi T d i z) := funext (fun z => by rw [cross_apply, cross_apply])
  rw [this, integral_transfer i (fun w => Yf (fun a => (θ i - θ₀) a) k w *
    Yf (fun a => (θ i - θ₀) a) l w) ((measurable_Yf _ k).mul (measurable_Yf _ l)), integral_YY]

lemma cross_measurable_coord (k : Fin d) :
    Measurable (fun z : GaussianRows T d => crossMoment θ₀ (observations θ z i) k) := by
  rw [cross_fun_eq]
  exact (measurable_Yf _ k).comp (measurable_Phi T d i)

lemma cross_memLp (k : Fin d) :
    MemLp (fun z => crossMoment θ₀ (observations θ z i) k) 2 (gaussianRows T d) := by
  rw [memLp_two_iff_integrable_sq (cross_measurable_coord θ₀ θ i k).aestronglyMeasurable]
  simpa [sq] using cross_integrable_mul θ₀ θ i k k

lemma norm_sq_sum (v : Vector d) : ‖v‖ ^ 2 = ∑ a, (v a) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

lemma cross_cov (k l : Fin d) :
    crossCovariance θ₀ θ i k l =
      (1 + ‖θ i - θ₀‖ ^ 2) * (if k = l then 1 else 0) + (θ i - θ₀) k * (θ i - θ₀) l := by
  unfold crossCovariance
  rw [covariance_eq_sub (cross_memLp θ₀ θ i k) (cross_memLp θ₀ θ i l)]
  have h := cross_integral_mul θ₀ θ i k l
  simp only [Pi.mul_apply] at h ⊢
  rw [h, cross_integral_coord, cross_integral_coord, norm_sq_sum]
  ring

/-- Centered coordinate of the cross moment of row `i`. -/
noncomputable def Dk (i : Fin T) (k : Fin d) (z : GaussianRows T d) : ℝ :=
  crossMoment θ₀ (observations θ z i) k - (θ i - θ₀) k

lemma Dk_memLp (k : Fin d) : MemLp (Dk θ₀ θ i k) 2 (gaussianRows T d) :=
  (cross_memLp θ₀ θ i k).sub (memLp_const _)

lemma Dk_integral (k : Fin d) : ∫ z, Dk θ₀ θ i k z ∂(gaussianRows T d) = 0 := by
  unfold Dk
  rw [integral_sub (cross_integrable_coord θ₀ θ i k) (integrable_const _), cross_integral_coord]
  simp

lemma Dk_sq (k : Fin d) :
    ∫ z, Dk θ₀ θ i k z * Dk θ₀ θ i k z ∂(gaussianRows T d) = crossCovariance θ₀ θ i k k := by
  unfold crossCovariance
  rw [covariance_self (cross_measurable_coord θ₀ θ i k).aemeasurable,
    variance_eq_integral (cross_measurable_coord θ₀ θ i k).aemeasurable,
    cross_integral_coord]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp [Dk, sq]

lemma Dk_measurable (k : Fin d) : Measurable (Dk θ₀ θ i k) := by
  unfold Dk
  exact (cross_measurable_coord θ₀ θ i k).sub_const _

lemma Dk_indep (k : Fin d) (j : Fin T) (hij : i ≠ j) :
    ∫ z, Dk θ₀ θ i k z * Dk θ₀ θ j k z ∂(gaussianRows T d) = 0 := by
  let g : Fin T → (Vector d × ℝ) → ℝ := fun m r =>
    crossMoment θ₀ (r.1, inner ℝ r.1 (θ m) + r.2) k - (θ m - θ₀) k
  have hg : ∀ m, Measurable (g m) := by
    intro m
    simp only [g, crossMoment]
    fun_prop
  have hind := iIndepFun_pi (μ := fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1))
    (X := g) (fun m => (hg m).aemeasurable)
  have h2 := hind.indepFun hij
  have e1 : Dk θ₀ θ i k = fun z : GaussianRows T d => g i (z i) := rfl
  have e2 : Dk θ₀ θ j k = fun z : GaussianRows T d => g j (z j) := rfl
  have h3 : IndepFun (Dk θ₀ θ i k) (Dk θ₀ θ j k) (gaussianRows T d) := by
    rw [e1, e2]; exact h2
  rw [h3.integral_fun_mul_eq_mul_integral (Dk_measurable θ₀ θ i k).aestronglyMeasurable
    (Dk_measurable θ₀ θ j k).aestronglyMeasurable]
  rw [Dk_integral θ₀ θ i k, zero_mul]

lemma Dk_mul_integrable (k : Fin d) (m n : Fin T) :
    Integrable (fun z => Dk θ₀ θ m k z * Dk θ₀ θ n k z) (gaussianRows T d) :=
  (Dk_memLp θ₀ θ m k).integrable_mul (Dk_memLp θ₀ θ n k)

lemma sum_second_moment (I : Finset (Fin T)) (k : Fin d) :
    ∫ z, (∑ m ∈ I, Dk θ₀ θ m k z) ^ 2 ∂(gaussianRows T d) =
      ∑ m ∈ I, crossCovariance θ₀ θ m k k := by
  have h : (fun z => (∑ m ∈ I, Dk θ₀ θ m k z) ^ 2) =
      fun z => ∑ m ∈ I, ∑ n ∈ I, Dk θ₀ θ m k z * Dk θ₀ θ n k z := by
    ext z; rw [sq, Finset.sum_mul_sum]
  rw [h, integral_finsetSum _ (fun m _ => integrable_finsetSum _
    (fun n _ => Dk_mul_integrable θ₀ θ k m n))]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [integral_finsetSum _ (fun n _ => Dk_mul_integrable θ₀ θ k m n)]
  rw [Finset.sum_eq_single m]
  · exact Dk_sq θ₀ θ m k
  · intro n _ hn
    exact Dk_indep θ₀ θ m k n (Ne.symm hn)
  · intro h; exact absurd hm h

lemma sum_sq_integrable (I : Finset (Fin T)) (k : Fin d) :
    Integrable (fun z => (∑ m ∈ I, Dk θ₀ θ m k z) ^ 2) (gaussianRows T d) := by
  have h : (fun z => (∑ m ∈ I, Dk θ₀ θ m k z) ^ 2) =
      fun z => ∑ m ∈ I, ∑ n ∈ I, Dk θ₀ θ m k z * Dk θ₀ θ n k z := by
    ext z; rw [sq, Finset.sum_mul_sum]
  rw [h]
  exact integrable_finsetSum _ (fun m _ => integrable_finsetSum _
    (fun n _ => Dk_mul_integrable θ₀ θ k m n))

end Row

end TRS.Dev.BlockMoments
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

namespace TRS.Dev.BlockMoments

/-- Squared norm of the block `S` part of a vector. -/
def bsq {d : ℕ} (S : Finset (Fin d)) (v : Vector d) : ℝ := ∑ k ∈ S, (v k) ^ 2

lemma norm_blockProjection_sq {d : ℕ} (S : Finset (Fin d)) (v : Vector d) :
    ‖blockProjection S v‖ ^ 2 = bsq S v := by
  unfold bsq blockProjection
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, WithLp.ofLp_toLp]
  exact Finset.sum_coe_sort S (fun k => v k ^ 2)

lemma bsq_nonneg {d : ℕ} (S : Finset (Fin d)) (v : Vector d) : 0 ≤ bsq S v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma bsq_sub_le {d : ℕ} (S : Finset (Fin d)) (u v : Vector d) :
    bsq S (u - v) ≤ (Real.sqrt (bsq S u) + Real.sqrt (bsq S v)) ^ 2 := by
  have h1 : bsq S (u - v) = ‖blockProjection S u - blockProjection S v‖ ^ 2 := by
    rw [← norm_blockProjection_sq]
    congr 2
  rw [h1]
  have h2 := norm_sub_le (blockProjection S u) (blockProjection S v)
  have e1 : ‖blockProjection S u‖ = Real.sqrt (bsq S u) := by
    rw [← norm_blockProjection_sq, Real.sqrt_sq (norm_nonneg _)]
  have e2 : ‖blockProjection S v‖ = Real.sqrt (bsq S v) := by
    rw [← norm_blockProjection_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [e1, e2] at h2
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- Block variance of the anchored average. -/
lemma avg_block_second_moment {T d : ℕ} (θ₀ : Vector d) (θ : Fin T → Vector d)
    (S : Finset (Fin d)) (I : Finset (Fin T)) (hI : I.Nonempty) (c : ℝ)
    (hc : ∀ m ∈ I, ∑ k ∈ S, crossCovariance θ₀ θ m k k ≤ c) :
    Integrable (fun z => bsq S (anchoredAverage θ₀ I (observations θ z) -
        pathAverage (fun i => θ i - θ₀) I)) (gaussianRows T d) ∧
    ∫ z, bsq S (anchoredAverage θ₀ I (observations θ z) -
        pathAverage (fun i => θ i - θ₀) I) ∂(gaussianRows T d) ≤ c / I.card := by
  have hfun : (fun z => bsq S (anchoredAverage θ₀ I (observations θ z) -
        pathAverage (fun i => θ i - θ₀) I)) =
      fun z => ((I.card : ℝ)⁻¹) ^ 2 * ∑ k ∈ S, (∑ m ∈ I, Dk θ₀ θ m k z) ^ 2 := by
    ext z
    unfold bsq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [anchoredAverage, pathAverage, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      WithLp.ofLp_sum, Finset.sum_apply, Dk, Finset.sum_sub_distrib]
    ring
  have hc0 : (0:ℝ) < I.card := by exact_mod_cast hI.card_pos
  rw [hfun]
  refine ⟨(integrable_finsetSum _ (fun k _ => sum_sq_integrable θ₀ θ I k)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => sum_sq_integrable θ₀ θ I k)]
  simp_rw [sum_second_moment θ₀ θ I]
  rw [Finset.sum_comm]
  have h1 : ∑ m ∈ I, ∑ k ∈ S, crossCovariance θ₀ θ m k k ≤ ∑ m ∈ I, c :=
    Finset.sum_le_sum hc
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((I.card : ℝ)⁻¹) ^ 2 * (I.card * c) = c / I.card := by
    field_simp
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

lemma block_trace {T d : ℕ} (θ₀ : Vector d) (θ : Fin T → Vector d) (S : Finset (Fin d))
    (m : Fin T) :
    ∑ k ∈ S, crossCovariance θ₀ θ m k k =
      (1 + ‖θ m - θ₀‖ ^ 2) * (S.card : ℝ) + bsq S (θ m - θ₀) := by
  simp only [cross_cov, if_true, ← sq]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp [bsq]
  ring

end TRS.Dev.BlockMoments
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

namespace TRS.Dev.BlockCopy

lemma proj_spec {d : ℕ} (K : Set (Vector d)) (hne : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) (x : Vector d) :
    convexProjection K x ∈ K ∧
      ∀ w ∈ K, inner ℝ (x - convexProjection K x) (w - convexProjection K x) ≤ 0 := by
  have hh : K.Nonempty ∧ IsClosed K ∧ Convex ℝ K := ⟨hne, hc, hv⟩
  have hdef : convexProjection K x =
      Classical.choose (exists_norm_eq_iInf_of_complete_convex hh.1 hh.2.1.isComplete hh.2.2 x) := by
    unfold convexProjection
    rw [dif_pos hh]
  obtain ⟨hmem, heq⟩ :=
    Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hh.1 hh.2.1.isComplete hh.2.2 x)
  rw [hdef]
  refine ⟨hmem, ?_⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hv hmem).1 heq

lemma proj_lipschitz {d : ℕ} (K : Set (Vector d)) (hne : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) : LipschitzWith 1 (convexProjection K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨hp, hpi⟩ := proj_spec K hne hc hv x
  obtain ⟨hq, hqi⟩ := proj_spec K hne hc hv y
  set p := convexProjection K x
  set q := convexProjection K y
  have h1 := hpi q hq
  have h2 := hqi p hp
  have h3 : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
    have e1 : inner ℝ (x - p) (q - p) = -inner ℝ (x - p) (p - q) := by
      rw [← inner_neg_right, neg_sub]
    have e2 : inner ℝ (x - p - (y - q)) (p - q) =
        inner ℝ (x - p) (p - q) - inner ℝ (y - q) (p - q) := inner_sub_left _ _ _
    have e3 : inner ℝ (x - y) (p - q) = inner ℝ (x - p - (y - q)) (p - q) +
        inner ℝ (p - q) (p - q) := by
      rw [← inner_add_left]; congr 1; abel
    rw [real_inner_self_eq_norm_sq] at e3
    linarith
  have h4 : inner ℝ (x - y) (p - q) ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
  rw [dist_eq_norm, dist_eq_norm]
  simp only [NNReal.coe_one, one_mul]
  by_cases h0 : ‖p - q‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma anchoredAverage_continuous {T d : ℕ} (θ₀ : Vector d) (I : Finset (Fin T)) :
    Continuous (fun h : Data T d => anchoredAverage θ₀ I h) := by
  unfold anchoredAverage crossMoment
  have hs : Continuous (fun h : Data T d => ∑ i ∈ I,
      ((h i).2 - inner ℝ (h i).1 θ₀) • (h i).1) := by
    apply continuous_finset_sum
    intro i _
    have h1 : Continuous (fun h : Data T d => (h i).1) := (continuous_apply i).fst
    have h2 : Continuous (fun h : Data T d => (h i).2) := (continuous_apply i).snd
    exact (h2.sub (Continuous.inner h1 continuous_const)).smul h1
  exact hs.const_smul (I.card : ℝ)⁻¹

lemma obs_continuous {T d : ℕ} (θ : Fin T → Vector d) :
    Continuous (fun z : GaussianRows T d => observations θ z) := by
  unfold observations
  apply continuous_pi
  intro i
  have h1 : Continuous (fun z : GaussianRows T d => (z i).1) := (continuous_apply i).fst
  have h2 : Continuous (fun z : GaussianRows T d => (z i).2) := (continuous_apply i).snd
  exact h1.prodMk ((Continuous.inner h1 continuous_const).add h2)


lemma foldl_spec {α β : Type*} (c : β → Prop) [DecidablePred c] (h : β → α) (w : α) (l : List β) :
    (List.foldl (fun r j => if c j then h j else r) w l = w ∧ ∀ k ∈ l, ¬ c k) ∨
    ∃ j, c j ∧ List.foldl (fun r j => if c j then h j else r) w l = h j ∧
      ∃ l₁ l₂, l = l₁ ++ j :: l₂ ∧ ∀ k ∈ l₂, ¬ c k := by
  induction l generalizing w with
  | nil => left; simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases ih (if c a then h a else w) with ⟨h1, h2⟩ | ⟨j, hj, hr, l₁, l₂, hl, hl₂⟩
    · by_cases ha : c a
      · right
        refine ⟨a, ha, ?_, [], l, rfl, h2⟩
        rw [h1]; simp [ha]
      · left
        refine ⟨?_, ?_⟩
        · rw [h1]; simp [ha]
        · intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact ha
          · exact h2 k hk
    · right
      exact ⟨j, hj, hr, a :: l₁, l₂, by simp [hl], hl₂⟩

/-- The deployed predictor is `θ₀` or the head of the last slot with date `≤ i`. -/
lemma deployed_spec {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (ω : Transcript s T d) (i : Fin T) :
    (deployed θ₀ π ω i = θ₀ ∧ ∀ j : Fin B, i.val < π.date j ω) ∨
    ∃ j : Fin B, π.date j ω ≤ i.val ∧ deployed θ₀ π ω i = π.head j ω ∧
      ∀ k : Fin B, j < k → i.val < π.date k ω := by
  unfold deployed
  rcases foldl_spec (fun j : Fin B => π.date j ω ≤ i.val) (fun j => π.head j ω) θ₀
    (List.finRange B) with ⟨h1, h2⟩ | ⟨j, hj, hr, l₁, l₂, hl, hl₂⟩
  · left
    refine ⟨h1, fun j => ?_⟩
    have := h2 j (List.mem_finRange j)
    omega
  · right
    refine ⟨j, hj, hr, fun k hk => ?_⟩
    have hp := List.pairwise_lt_finRange B
    rw [hl] at hp
    have hkmem : k ∈ l₁ ++ j :: l₂ := hl ▸ List.mem_finRange k
    rcases List.mem_append.1 hkmem with hk1 | hk2
    · have := (List.pairwise_append.1 hp).2.2 k hk1 j (List.mem_cons_self)
      exact absurd (lt_trans this hk) (lt_irrefl _)
    · rcases List.mem_cons.1 hk2 with rfl | hk3
      · exact absurd hk (lt_irrefl _)
      · have := hl₂ k hk3
        omega

end TRS.Dev.BlockCopy
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments

namespace TRS.Dev.BlockUpper

lemma mem_blockBall_iff {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ)
    (hΔ : ∀ i, 0 < Δ i) (β : Vector d) :
    β ∈ blockBall S Δ ↔ ∀ i, bsq (S i) β ≤ Δ i ^ 2 := by
  unfold blockBall
  simp only [Set.mem_setOf_eq]
  refine forall_congr' (fun i => ?_)
  rw [← norm_blockProjection_sq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hΔ i).le (by norm_num)).symm

lemma blockBall_convex {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :
    Convex ℝ (blockBall S Δ) := by
  intro x hx y hy a b ha hb hab i
  have h : blockProjection (S i) (a • x + b • y) =
      a • blockProjection (S i) x + b • blockProjection (S i) y := by
    ext k; simp [blockProjection]
  rw [h]
  calc ‖a • blockProjection (S i) x + b • blockProjection (S i) y‖
      ≤ ‖a • blockProjection (S i) x‖ + ‖b • blockProjection (S i) y‖ := norm_add_le _ _
    _ = a * ‖blockProjection (S i) x‖ + b * ‖blockProjection (S i) y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg hb]
    _ ≤ a * Δ i + b * Δ i := by
        gcongr
        · exact hx i
        · exact hy i
    _ = Δ i := by rw [← add_mul, hab, one_mul]

lemma blockBall_closed {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :
    IsClosed (blockBall S Δ) := by
  unfold blockBall
  simp only [Set.setOf_forall]
  refine isClosed_iInter (fun i => ?_)
  have hc : Continuous (fun β : Vector d => ‖blockProjection (S i) β‖) := by
    refine continuous_norm.comp ?_
    unfold blockProjection
    refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi (fun k => ?_)
    exact (EuclideanSpace.proj (k.val : Fin d)).continuous
  exact isClosed_le hc continuous_const

lemma blockBall_nonempty {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ)
    (hΔ : ∀ i, 0 < Δ i) : (blockBall S Δ).Nonempty := by
  refine ⟨0, fun i => ?_⟩
  have : blockProjection (S i) (0 : Vector d) = 0 := by ext k; simp [blockProjection]
  rw [this, norm_zero]; exact (hΔ i).le

lemma sum_sq_le_of_inner (E F P : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (h1 : E ≤ P)
    (h2 : P ^ 2 ≤ F * E) : E ≤ F := by
  by_contra h
  push Not at h
  have hE0 : 0 < E := by linarith
  have : E ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hE h1 2
  nlinarith

/-- Blockwise nonexpansiveness and the diameter bound of the product-ball projection. -/
lemma proj_block {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (β x : Vector d) (hβ : β ∈ blockBall S Δ) (i : Fin K) :
    bsq (S i) (convexProjection (blockBall S Δ) x - β) ≤ bsq (S i) (x - β) ∧
    bsq (S i) (convexProjection (blockBall S Δ) x - β) ≤ 4 * Δ i ^ 2 := by
  have hspec := TRS.Dev.BlockCopy.proj_spec (blockBall S Δ) (blockBall_nonempty S Δ hΔ)
    (blockBall_closed S Δ) (blockBall_convex S Δ) x
  set p := convexProjection (blockBall S Δ) x with hp
  obtain ⟨hpK, hvar⟩ := hspec
  have hpK' := (mem_blockBall_iff S Δ hΔ p).1 hpK
  have hβ' := (mem_blockBall_iff S Δ hΔ β).1 hβ
  classical
  let w : Vector d := WithLp.toLp 2 (fun k => if k ∈ S i then β k else p k)
  have hw : w ∈ blockBall S Δ := by
    rw [mem_blockBall_iff S Δ hΔ]
    intro j
    by_cases hj : j = i
    · subst hj
      have : bsq (S j) w = bsq (S j) β := by
        unfold bsq
        refine Finset.sum_congr rfl (fun k hk => ?_)
        simp [w, hk]
      rw [this]; exact hβ' j
    · have : bsq (S j) w = bsq (S j) p := by
        unfold bsq
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hki : k ∉ S i := by
          intro hki
          exact Finset.disjoint_left.1 (hS.2.1 hj) hk hki |>.elim
        simp [w, hki]
      rw [this]; exact hpK' j
  have hin := hvar w hw
  have hin2 : ∑ k ∈ S i, (x k - p k) * (β k - p k) ≤ 0 := by
    have : inner ℝ (x - p) (w - p) = ∑ k ∈ S i, (x k - p k) * (β k - p k) := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, conj_trivial, PiLp.sub_apply]
      rw [← Finset.sum_subset (Finset.subset_univ (S i))]
      · refine Finset.sum_congr rfl (fun k hk => ?_)
        simp [w, hk]; ring
      · intro k _ hk
        simp [w, hk]
    rw [← this]; exact hin
  have hE : bsq (S i) (p - β) = ∑ k ∈ S i, (p k - β k) ^ 2 := rfl
  have hF : bsq (S i) (x - β) = ∑ k ∈ S i, (x k - β k) ^ 2 := rfl
  have hEP : bsq (S i) (p - β) ≤ ∑ k ∈ S i, (x k - β k) * (p k - β k) := by
    have : ∑ k ∈ S i, (x k - p k) * (β k - p k) =
        bsq (S i) (p - β) - (∑ k ∈ S i, (x k - β k) * (p k - β k)) := by
      rw [hE, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    linarith
  have hcs : (∑ k ∈ S i, (x k - β k) * (p k - β k)) ^ 2 ≤
      bsq (S i) (x - β) * bsq (S i) (p - β) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (S i) (fun k => x k - β k) (fun k => p k - β k)
    rw [hF, hE]
    exact this
  refine ⟨sum_sq_le_of_inner _ _ _ (bsq_nonneg _ _) (bsq_nonneg _ _) hEP hcs, ?_⟩
  have h3 := bsq_sub_le (S i) p β
  have h4 : Real.sqrt (bsq (S i) p) ≤ Δ i := Real.sqrt_le_iff.2 ⟨(hΔ i).le, hpK' i⟩
  have h5 : Real.sqrt (bsq (S i) β) ≤ Δ i := Real.sqrt_le_iff.2 ⟨(hΔ i).le, hβ' i⟩
  have h6 : (Real.sqrt (bsq (S i) p) + Real.sqrt (bsq (S i) β)) ^ 2 ≤ (Δ i + Δ i) ^ 2 := by
    gcongr
  nlinarith

end TRS.Dev.BlockUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockCopy

namespace TRS.Dev.BlockUpper

/-- The head released at date `n`. -/
noncomputable def blockHead (T d K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (Δ : Fin K → ℝ) (n : ℕ) (h : Data T d) : Vector d :=
  if n = 0 ∨ T ≤ n then θ₀ else
    θ₀ + convexProjection (blockBall S Δ)
      (anchoredAverage θ₀ (Finset.univ.filter (fun i : Fin T => i.val < n)) h)

lemma blockHead_measurable (T d K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (n : ℕ) :
    Measurable (blockHead T d K θ₀ S Δ n) := by
  unfold blockHead
  by_cases h : n = 0 ∨ T ≤ n
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]
    have hl := proj_lipschitz (blockBall S Δ) (blockBall_nonempty S Δ hΔ) (blockBall_closed S Δ)
      (blockBall_convex S Δ)
    exact measurable_const.add (hl.continuous.measurable.comp
      (anchoredAverage_continuous θ₀ _).measurable)

lemma sum_bsq {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S) (v : Vector d) :
    ∑ i, bsq (S i) v = ‖v‖ ^ 2 := by
  classical
  have hU : (Finset.univ : Finset (Fin K)).biUnion S = Finset.univ := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    obtain ⟨i, hi⟩ := hS.2.2 c
    exact ⟨i, hi⟩
  have hdisj : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint S := by
    intro a _ b _ hab
    exact hS.2.1 hab
  unfold bsq
  rw [← Finset.sum_biUnion hdisj, hU, norm_sq_sum]

lemma norm_le_one_of_mem {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) (β : Vector d)
    (hβ : β ∈ blockBall S Δ) : ‖β‖ ≤ 1 := by
  have h1 := sum_bsq S hS β
  have h2 : ∑ i, bsq (S i) β ≤ ∑ i, Δ i ^ 2 :=
    Finset.sum_le_sum (fun i _ => (mem_blockBall_iff S Δ hΔ β).1 hβ i)
  have : ‖β‖ ^ 2 ≤ 1 := by linarith
  nlinarith [norm_nonneg β]

lemma card_filter_lt (T n : ℕ) (hn : n ≤ T) :
    (Finset.univ.filter (fun i : Fin T => i.val < n)).card = n := by
  rw [Fin.card_filter_val_lt]; omega

/-- Block error of the head released at a date `1 ≤ n < T`. -/
lemma head_bound (T d K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) (θ : Vector d) (hθ : θ - θ₀ ∈ blockBall S Δ) (i : Fin K)
    (n : ℕ) (hn1 : 1 ≤ n) (hnT : n < T) :
    ∫⁻ z, ENNReal.ofReal
        (bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ))
      ∂(gaussianRows T d) ≤
      ENNReal.ofReal (min (3 * ((S i).card : ℝ) / n) (4 * Δ i ^ 2)) := by
  have hβ1 := norm_le_one_of_mem S hS Δ hΔ hΔsum _ hθ
  set I : Finset (Fin T) := Finset.univ.filter (fun i : Fin T => i.val < n) with hI
  have hcard : I.card = n := card_filter_lt T n hnT.le
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have hpath : pathAverage (fun _ : Fin T => θ - θ₀) I = θ - θ₀ := by
    unfold pathAverage
    rw [Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith), one_smul]
  have hnT' : blockHead T d K θ₀ S Δ n = fun h =>
      θ₀ + convexProjection (blockBall S Δ) (anchoredAverage θ₀ I h) := by
    funext h
    unfold blockHead
    rw [if_neg (by omega)]
  have hdi : (S i).card ≥ 1 := Finset.card_pos.2 (hS.1 i)
  have hdi' : (1 : ℝ) ≤ (S i).card := by exact_mod_cast hdi
  have hβi := (mem_blockBall_iff S Δ hΔ _).1 hθ i
  have hΔi1 := hΔ₁ i
  have hc : ∀ m ∈ I, ∑ k ∈ S i, crossCovariance θ₀ (fun _ : Fin T => θ) m k k ≤
      3 * ((S i).card : ℝ) := by
    intro m _
    rw [block_trace]
    have h1 : ‖(fun _ : Fin T => θ) m - θ₀‖ ^ 2 ≤ 1 := by
      have := norm_nonneg (θ - θ₀)
      show ‖θ - θ₀‖ ^ 2 ≤ 1
      nlinarith
    have h2 : bsq (S i) ((fun _ : Fin T => θ) m - θ₀) ≤ 1 := by
      show bsq (S i) (θ - θ₀) ≤ 1
      have := hΔ i
      nlinarith
    have h3 : (1 + ‖(fun _ : Fin T => θ) m - θ₀‖ ^ 2) * ((S i).card : ℝ) ≤ 2 * (S i).card :=
      by nlinarith
    nlinarith
  obtain ⟨hint, hbound⟩ := avg_block_second_moment θ₀ (fun _ : Fin T => θ) (S i) I hIne _ hc
  rw [hpath] at hint hbound
  have hpt : ∀ z, bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ) ≤
      min (bsq (S i) (anchoredAverage θ₀ I (observations (fun _ : Fin T => θ) z) - (θ - θ₀)))
        (4 * Δ i ^ 2) := by
    intro z
    rw [hnT']
    have e : θ₀ + convexProjection (blockBall S Δ)
        (anchoredAverage θ₀ I (observations (fun _ : Fin T => θ) z)) - θ =
        convexProjection (blockBall S Δ)
          (anchoredAverage θ₀ I (observations (fun _ : Fin T => θ) z)) - (θ - θ₀) := by abel
    simp only [e]
    exact le_min (proj_block S hS Δ hΔ _ _ hθ i).1 (proj_block S hS Δ hΔ _ _ hθ i).2
  rw [ENNReal.ofReal_mono.map_min]
  refine le_min ?_ ?_
  · calc _ ≤ ∫⁻ z, ENNReal.ofReal (bsq (S i) (anchoredAverage θ₀ I
            (observations (fun _ : Fin T => θ) z) - (θ - θ₀))) ∂(gaussianRows T d) :=
          lintegral_mono (fun z => ENNReal.ofReal_le_ofReal ((hpt z).trans (min_le_left _ _)))
      _ = ENNReal.ofReal (∫ z, bsq (S i) (anchoredAverage θ₀ I
            (observations (fun _ : Fin T => θ) z) - (θ - θ₀)) ∂(gaussianRows T d)) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall (fun z => bsq_nonneg _ _))).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hcard] at hbound
          exact hbound
  · calc _ ≤ ∫⁻ z, ENNReal.ofReal (4 * Δ i ^ 2) ∂(gaussianRows T d) :=
          lintegral_mono (fun z => ENNReal.ofReal_le_ofReal ((hpt z).trans (min_le_right _ _)))
      _ = ENNReal.ofReal (4 * Δ i ^ 2) := by simp

end TRS.Dev.BlockUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockCopy

namespace TRS.Dev.BlockUpper

lemma measurable_bsq {d : ℕ} (S : Finset (Fin d)) : Measurable (fun v : Vector d => bsq S v) := by
  unfold bsq
  refine Finset.measurable_sum _ (fun k _ => ?_)
  have : Measurable (fun v : Vector d => v k) :=
    (measurable_pi_apply k).comp (PiLp.continuous_ofLp 2 _).measurable
  exact this.pow_const 2

lemma half_min_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / 2 : ℝ) * min (3 * a) (4 * b) ≤ 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    have : min (3 * a) (4 * b) ≤ 3 * a := min_le_left _ _
    linarith
  · rw [min_eq_right h]
    have : min (3 * a) (4 * b) ≤ 4 * b := min_le_right _ _
    linarith

lemma block_round (T d K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) (θ : Vector d) (hθ : θ - θ₀ ∈ blockBall S Δ) (i : Fin K)
    (n : ℕ) (hnT : n < T) :
    ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) *
        bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ))
      ∂(gaussianRows T d) ≤
      ENNReal.ofReal (2 * blockCoeff (S i).card (Δ i) n) := by
  have hdi : (1 : ℝ) ≤ (S i).card := by exact_mod_cast Finset.card_pos.2 (hS.1 i)
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have hh : ∀ z, blockHead T d K θ₀ S Δ 0 (observations (fun _ : Fin T => θ) z) = θ₀ := by
      intro z; simp [blockHead]
    simp only [hh]
    rw [lintegral_const, measure_univ, mul_one]
    apply ENNReal.ofReal_le_ofReal
    have h1 : bsq (S i) (θ₀ - θ) = bsq (S i) (θ - θ₀) := by
      unfold bsq
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [PiLp.sub_apply]; ring
    rw [h1]
    have h2 := (mem_blockBall_iff S Δ hΔ _).1 hθ i
    simp only [blockCoeff, if_true]
    nlinarith
  · have hb := head_bound T d K θ₀ S hS Δ hΔ hΔ₁ hΔsum θ hθ i n hn1 hnT
    have hm : Measurable (fun z : GaussianRows T d => ENNReal.ofReal
        (bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ))) := by
      refine Measurable.ennreal_ofReal ((measurable_bsq (S i)).comp ?_)
      exact (((blockHead_measurable T d K θ₀ S Δ hΔ n).comp
        (obs_continuous (fun _ : Fin T => θ)).measurable).sub measurable_const)
    have e : ∀ z, ENNReal.ofReal ((1 / 2 : ℝ) *
        bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ)) =
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal
        (bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ)) :=
      fun z => ENNReal.ofReal_mul (by norm_num)
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (1 / 2) * _ ≤ ENNReal.ofReal (1 / 2) *
          ENNReal.ofReal (min (3 * ((S i).card : ℝ) / n) (4 * Δ i ^ 2)) := by gcongr
      _ = ENNReal.ofReal ((1 / 2) * min (3 * ((S i).card : ℝ) / n) (4 * Δ i ^ 2)) :=
          (ENNReal.ofReal_mul (by norm_num)).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hn0 : n ≠ 0 := by omega
          simp only [blockCoeff, hn0, if_false]
          have h3 := half_min_le (((S i).card : ℝ) / n) (Δ i ^ 2) (by positivity) (by positivity)
          have h4 : 3 * ((S i).card : ℝ) / n = 3 * (((S i).card : ℝ) / n) := by ring
          rw [h4]
          exact h3

end TRS.Dev.BlockUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockCopy

namespace TRS.Dev.BlockUpper

/-- Per-round half squared error of a head released at date `n < T`. -/
lemma round_all (T d K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) (θ : Vector d) (hθ : θ - θ₀ ∈ blockBall S Δ)
    (n : ℕ) (hnT : n < T) :
    ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) *
        ‖blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ‖ ^ 2)
      ∂(gaussianRows T d) ≤
      ENNReal.ofReal (2 * ∑ i, blockCoeff (S i).card (Δ i) n) := by
  have hm : ∀ i : Fin K, Measurable (fun z : GaussianRows T d => ENNReal.ofReal ((1 / 2 : ℝ) *
        bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ))) := by
    intro i
    refine Measurable.ennreal_ofReal (measurable_const.mul ((measurable_bsq (S i)).comp ?_))
    exact (((blockHead_measurable T d K θ₀ S Δ hΔ n).comp
        (obs_continuous (fun _ : Fin T => θ)).measurable).sub measurable_const)
  have e : ∀ z, ENNReal.ofReal ((1 / 2 : ℝ) *
        ‖blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ‖ ^ 2) =
      ∑ i, ENNReal.ofReal ((1 / 2 : ℝ) *
        bsq (S i) (blockHead T d K θ₀ S Δ n (observations (fun _ : Fin T => θ) z) - θ)) := by
    intro z
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (by norm_num) (bsq_nonneg _ _)), ← Finset.mul_sum, sum_bsq S hS]
  simp_rw [e]
  rw [lintegral_finset_sum _ (fun i _ => hm i)]
  calc _ ≤ ∑ i : Fin K, ENNReal.ofReal (2 * blockCoeff (S i).card (Δ i) n) :=
        Finset.sum_le_sum (fun i _ => block_round T d K θ₀ S hS Δ hΔ hΔ₁ hΔsum θ hθ i n hnT)
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg, ← Finset.mul_sum]
        intro i _
        have : 0 ≤ blockCoeff (S i).card (Δ i) n := by
          unfold blockCoeff
          split_ifs
          · positivity
          · exact le_min (by positivity) (by positivity)
        positivity

lemma sum_Ico_phases' {M : Type*} [AddCommMonoid M] (t : ℕ → ℕ) (ht : Monotone t) (f : ℕ → M)
    (n : ℕ) :
    ∑ i ∈ Finset.Ico (t 0) (t n), f i =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (t j) (t (j + 1)), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f (ht (Nat.zero_le n)) (ht (Nat.le_succ n))).symm

def tt (T B : ℕ) (τ : Fin (B + 2) → ℕ) (m : ℕ) : ℕ := if hm : m < B + 2 then τ ⟨m, hm⟩ else T

lemma tt_mono (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) : Monotone (tt T B τ) := by
  obtain ⟨h0, hlast, hmono⟩ := hτ
  intro a b hab
  simp only [tt]
  by_cases hb : b < B + 2
  · have ha : a < B + 2 := lt_of_le_of_lt hab hb
    simp only [ha, hb, dif_pos]
    exact hmono (by simpa using hab)
  · by_cases ha : a < B + 2
    · simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      rw [← hlast]
      exact hmono (by simp [Fin.le_def]; omega)
    · simp [ha, hb]

lemma tt_zero (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) : tt T B τ 0 = 0 := by
  simp [tt, hτ.1]

lemma tt_last (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    tt T B τ (B + 1) = T := by
  simp only [tt]
  rw [dif_pos (by omega)]
  exact hτ.2.1

lemma tt_cast (T B : ℕ) (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) :
    tt T B τ j.val = τ j.castSucc := by
  simp only [tt]; rw [dif_pos (by omega)]; rfl

lemma tt_succ (T B : ℕ) (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) :
    tt T B τ (j.val + 1) = τ j.succ := by
  simp only [tt]; rw [dif_pos (by omega)]; rfl

lemma exists_phase (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) (i : ℕ) (hi : i < T) :
    ∃ j : Fin (B + 1), τ j.castSucc ≤ i ∧ i < τ j.succ := by
  classical
  have hex : ∃ m, i < tt T B τ m := ⟨B + 1, by rw [tt_last T B τ hτ]; exact hi⟩
  set m := Nat.find hex with hm
  have hm1 : i < tt T B τ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, tt_zero T B τ hτ] at hm1
    omega
  have hmB : m ≤ B + 1 := Nat.find_min' hex (by rw [tt_last T B τ hτ]; exact hi)
  have hprev : ¬ i < tt T B τ (m - 1) := Nat.find_min hex (by omega)
  refine ⟨⟨m - 1, by omega⟩, ?_, ?_⟩
  · have := tt_cast T B τ ⟨m - 1, by omega⟩
    simp only at this
    rw [← this]; omega
  · have := tt_succ T B τ ⟨m - 1, by omega⟩
    simp only at this
    rw [← this]
    have e : m - 1 + 1 = m := by omega
    rw [e]; exact hm1

/-- Summing a per-round bound over the phases of a schedule. -/
lemma phase_sum_bound (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ)
    (g : ℕ → ℝ≥0∞) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (h : ∀ j : Fin (B + 1), ∀ i, τ j.castSucc ≤ i → i < τ j.succ →
      g i ≤ ENNReal.ofReal (F (τ j.castSucc))) :
    ∑ i ∈ Finset.range T, g i ≤
      ENNReal.ofReal (∑ j : Fin (B + 1), phaseLength τ j * F (phaseStart τ j)) := by
  have hmono : Monotone τ := hτ.2.2
  have ht := tt_mono T B τ hτ
  have t0 := tt_zero T B τ hτ
  have tB := tt_last T B τ hτ
  have tj := tt_cast T B τ
  have tj1 := tt_succ T B τ
  set t := tt T B τ with htdef
  have hs := sum_Ico_phases' t ht (fun i => g i) (B + 1)
  rw [t0, tB] at hs
  rw [Finset.range_eq_Ico, hs]
  rw [Finset.sum_range]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_le_sum (fun j _ => ?_)
    calc ∑ i ∈ Finset.Ico (t j.val) (t (j.val + 1)), g i
        ≤ ∑ i ∈ Finset.Ico (t j.val) (t (j.val + 1)), ENNReal.ofReal (F (τ j.castSucc)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Finset.mem_Ico, tj, tj1] at hi
          exact h j i hi.1 hi.2
      _ = ENNReal.ofReal (phaseLength τ j * F (phaseStart τ j)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, tj, tj1]
          have hle : τ j.castSucc ≤ τ j.succ := hmono (by simp [Fin.le_def])
          have hpl : phaseLength τ j = ((τ j.succ - τ j.castSucc : ℕ) : ℝ) := by
            unfold phaseLength; rw [Nat.cast_sub hle]
          rw [hpl, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          rfl
  · intro j _
    unfold phaseLength phaseStart
    have hle : τ j.castSucc ≤ τ j.succ := hmono (by simp [Fin.le_def])
    have : (τ j.castSucc : ℝ) ≤ τ j.succ := by exact_mod_cast hle
    exact mul_nonneg (by linarith) (hF _)

end TRS.Dev.BlockUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockCopy

namespace TRS.Dev.BlockUpper

lemma head_eq (T d B K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ)
    (τ : Fin (B + 2) → ℕ) (j : Fin B) (ω : Transcript unitSeed T d) :
    (blockGridPolicy T d B K θ₀ S Δ τ).head j ω =
      blockHead T d K θ₀ S Δ (slotDate τ j) ω.2 := rfl

lemma date_eq (T d B K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ)
    (τ : Fin (B + 2) → ℕ) (j : Fin B) (ω : Transcript unitSeed T d) :
    (blockGridPolicy T d B K θ₀ S Δ τ).date j ω = slotDate τ j := rfl

lemma phase_deployed (T d B K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (Δ : Fin K → ℝ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) (j : Fin (B + 1))
    (i : Fin T) (h1 : τ j.castSucc ≤ i.val) (h2 : i.val < τ j.succ)
    (ω : Transcript unitSeed T d) :
    deployed θ₀ (blockGridPolicy T d B K θ₀ S Δ τ) ω i =
      blockHead T d K θ₀ S Δ (τ j.castSucc) ω.2 := by
  have hmono : Monotone τ := hτ.2.2
  rcases deployed_spec θ₀ (blockGridPolicy T d B K θ₀ S Δ τ) ω i with
    ⟨h, hall⟩ | ⟨k, hk, hdep, hlater⟩
  · rw [h]
    by_cases hj : j.val = 0
    · have h0 : τ j.castSucc = 0 := by
        have : j.castSucc = 0 := Fin.ext hj
        rw [this]; exact hτ.1
      rw [h0]; simp [blockHead]
    · exfalso
      let k : Fin B := ⟨j.val - 1, by omega⟩
      have := hall k
      rw [date_eq] at this
      have e : slotDate τ k = τ j.castSucc := by
        unfold slotDate; congr 1; ext; simp [k]; omega
      rw [e] at this
      omega
  · rw [hdep, head_eq]
    rw [date_eq] at hk
    have hlt : k.succ.castSucc < j.succ := by
      refine hmono.reflect_lt ?_
      unfold slotDate at hk
      omega
    have hkj : k.val + 1 < j.val + 1 := by simpa [Fin.lt_def] using hlt
    have hkeq : k.val + 1 = j.val := by
      by_contra hne
      have hlt2 : k.val + 1 < j.val := by omega
      let k' : Fin B := ⟨k.val + 1, by omega⟩
      have hk' : k < k' := by simp [Fin.lt_def, k']
      have h3 := hlater k' hk'
      rw [date_eq] at h3
      have : slotDate τ k' ≤ τ j.castSucc := by
        unfold slotDate
        exact hmono (by simp [Fin.le_def, k']; omega)
      omega
    have : slotDate τ k = τ j.castSucc := by
      unfold slotDate; congr 1; ext; simp; omega
    rw [this]

lemma isCausal_block (T d B K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    IsCausal (blockGridPolicy T d B K θ₀ S Δ τ) := by
  have hmono : Monotone τ := hτ.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j ω
    rw [date_eq]
    unfold slotDate
    rw [← hτ.2.1]
    exact hmono (by simp [Fin.le_def])
  · intro ω a b hab
    simp only [date_eq]
    unfold slotDate
    have hab' : a.val ≤ b.val := hab
    exact hmono (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
  · intro j n
    show @MeasurableSet _ (information unitSeed T d n)
      {ω : Transcript unitSeed T d | slotDate τ j ≤ n}
    by_cases h : slotDate τ j ≤ n
    · simp only [h, Set.setOf_true]; exact @MeasurableSet.univ _ (information unitSeed T d n)
    · simp only [h, Set.setOf_false]; exact @MeasurableSet.empty _ (information unitSeed T d n)
  · intro j n
    show @Measurable _ _ (information unitSeed T d n) _
      (fun ω : Transcript unitSeed T d => if slotDate τ j ≤ n then
        blockHead T d K θ₀ S Δ (slotDate τ j) ω.2 else 0)
    by_cases h : slotDate τ j ≤ n
    · simp only [h, if_true]
      have hΨ : @Measurable _ _ (information unitSeed T d n) inferInstance
          (fun ω : Transcript unitSeed T d =>
            (ω.1, fun i : Fin T => if i.val < n then ω.2 i else ((0 : Vector d), (0 : ℝ)))) :=
        comap_measurable _
      have hg : Measurable (fun ω' : Transcript unitSeed T d =>
          blockHead T d K θ₀ S Δ (slotDate τ j) ω'.2) :=
        (blockHead_measurable T d K θ₀ S Δ hΔ _).comp measurable_snd
      have e : (fun ω : Transcript unitSeed T d => blockHead T d K θ₀ S Δ (slotDate τ j) ω.2) =
          (fun ω' : Transcript unitSeed T d =>
            blockHead T d K θ₀ S Δ (slotDate τ j) ω'.2) ∘
          (fun ω : Transcript unitSeed T d =>
            (ω.1, fun i : Fin T => if i.val < n then ω.2 i else ((0 : Vector d), (0 : ℝ)))) := by
        funext ω
        simp only [Function.comp]
        unfold blockHead
        split_ifs with h1
        · rfl
        · congr 2
          unfold anchoredAverage
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          have : i.val < slotDate τ j := (Finset.mem_filter.1 hi).2
          show crossMoment θ₀ (ω.2 i) = crossMoment θ₀ (if i.val < n then ω.2 i else (0, 0))
          rw [if_pos (lt_of_lt_of_le this h)]
      rw [e]
      exact hg.comp hΨ
    · simp only [h, if_false]
      exact measurable_const

lemma lintegral_snd_prob {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    (P : Measure S) [IsProbabilityMeasure P] (ν : Measure X) [SFinite ν]
    (F : X → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F ω.2 ∂(P.prod ν) = ∫⁻ x, F x ∂ν := by
  rw [lintegral_prod (fun ω : S × X => F ω.2) (hF.comp measurable_snd).aemeasurable]
  simp

lemma coeff_nonneg (dᵢ : ℕ) (Δᵢ : ℝ) (n : ℕ) : 0 ≤ blockCoeff dᵢ Δᵢ n := by
  unfold blockCoeff
  split_ifs
  · positivity
  · exact le_min (by positivity) (by positivity)

/-- Worst-case risk of the grid on a schedule is at most twice the program value. -/
theorem worst_le (T d B K : ℕ) (hT : 0 < T) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    blockWorstRisk θ₀ S Δ (blockGridPolicy T d B K θ₀ S Δ τ) ≤
      ENNReal.ofReal (2 * blockProgram S Δ τ) := by
  unfold blockWorstRisk
  apply iSup_le
  rintro ⟨θ, hθ⟩
  show policyRisk θ₀ (blockGridPolicy T d B K θ₀ S Δ τ) (fun _ => θ) ≤ _
  set π := blockGridPolicy T d B K θ₀ S Δ τ with hπ
  have hmono : Monotone τ := hτ.2.2
  have hτT : ∀ m : Fin (B + 2), τ m ≤ T := by
    intro m; rw [← hτ.2.1]; exact hmono (by simp [Fin.le_def]; omega)
  have hobs : Measurable (fun z : GaussianRows T d => observations (fun _ : Fin T => θ) z) :=
    (obs_continuous _).measurable
  set e : ℕ → GaussianRows T d → ℝ := fun i z =>
    if hi : i < T then ‖deployed θ₀ π (((), observations (fun _ : Fin T => θ) z) :
      Transcript unitSeed T d) ⟨i, hi⟩ - θ‖ ^ 2 else 0 with he
  have hephase : ∀ i, i < T → ∃ j : Fin (B + 1), τ j.castSucc ≤ i ∧ i < τ j.succ ∧
      ∀ z, e i z = ‖blockHead T d K θ₀ S Δ (τ j.castSucc)
        (observations (fun _ : Fin T => θ) z) - θ‖ ^ 2 := by
    intro i hi
    obtain ⟨j, hj1, hj2⟩ := exists_phase T B τ hτ i hi
    refine ⟨j, hj1, hj2, fun z => ?_⟩
    simp only [he, dif_pos hi]
    rw [phase_deployed T d B K θ₀ S Δ τ hτ j ⟨i, hi⟩ hj1 hj2]
  have he_meas : ∀ i, Measurable (e i) := by
    intro i
    by_cases hi : i < T
    · obtain ⟨j, -, -, hj⟩ := hephase i hi
      have : e i = fun z => ‖blockHead T d K θ₀ S Δ (τ j.castSucc)
        (observations (fun _ : Fin T => θ) z) - θ‖ ^ 2 := funext hj
      rw [this]
      exact ((((blockHead_measurable T d K θ₀ S Δ hΔ _).comp hobs).sub
        measurable_const).norm).pow_const 2
    · have : e i = fun _ => 0 := by funext z; simp [he, hi]
      rw [this]; exact measurable_const
  have h1 : policyRisk θ₀ π (fun _ => θ) =
      ∫⁻ ω : unitSeed.space × GaussianRows T d,
        (fun z : GaussianRows T d => ∑ i ∈ Finset.range T,
          ENNReal.ofReal ((1 / 2 : ℝ) * e i z)) ω.2
        ∂(unitSeed.law.prod (gaussianRows T d)) := by
    unfold policyRisk
    apply lintegral_congr
    intro ω
    show _ = ∑ i ∈ Finset.range T, ENNReal.ofReal ((1 / 2 : ℝ) * e i ω.2)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by norm_num) (by
      simp only [he]; split_ifs <;> positivity)), ← Finset.mul_sum]
    congr 2
    rw [← Fin.sum_univ_eq_sum_range (fun i => e i ω.2) T]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [he, dif_pos i.isLt]
    rfl
  have hmi : ∀ i, Measurable (fun z : GaussianRows T d =>
      ENNReal.ofReal ((1 / 2 : ℝ) * e i z)) :=
    fun i => Measurable.ennreal_ofReal (measurable_const.mul (he_meas i))
  have hm : Measurable (fun z : GaussianRows T d => ∑ i ∈ Finset.range T,
      ENNReal.ofReal ((1 / 2 : ℝ) * e i z)) :=
    Finset.measurable_sum _ (fun i _ => hmi i)
  rw [h1, lintegral_snd_prob unitSeed.law (gaussianRows T d) _ hm]
  rw [lintegral_finset_sum _ (fun i _ => hmi i)]
  have hbound := phase_sum_bound T B τ hτ
    (fun i => ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) * e i z) ∂(gaussianRows T d))
    (fun n => 2 * ∑ k, blockCoeff (S k).card (Δ k) n)
    (fun n => by
      have : 0 ≤ ∑ k, blockCoeff (S k).card (Δ k) n :=
        Finset.sum_nonneg (fun k _ => coeff_nonneg (S k).card (Δ k) n)
      linarith) (by
    intro j i hi1 hi2
    have hiT : i < T := lt_of_lt_of_le hi2 (hτT _)
    obtain ⟨j', hj1, hj2, hj3⟩ := hephase i hiT
    have hjj : j' = j := by
      -- uniqueness of the phase
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : j'.succ ≤ j.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          have := Fin.lt_def.1 hlt; omega
        have := hmono this
        omega
      · have : j.succ ≤ j'.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          have := Fin.lt_def.1 hgt; omega
        have := hmono this
        omega
    subst hjj
    have hnT : τ j'.castSucc < T := lt_of_le_of_lt hi1 hiT
    simp only [hj3]
    exact round_all T d K θ₀ S hS Δ hΔ hΔ₁ hΔsum θ hθ _ hnT)
  calc _ ≤ ENNReal.ofReal (∑ j : Fin (B + 1), phaseLength τ j *
        (2 * ∑ k, blockCoeff (S k).card (Δ k) (phaseStart τ j))) := hbound
    _ = ENNReal.ofReal (2 * blockProgram S Δ τ) := by
        congr 1
        unfold blockProgram
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

end TRS.Dev.BlockUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

namespace TRS.Dev.BlockUpper

lemma schedule_finite (T B : ℕ) : {τ : Fin (B + 2) → ℕ | IsSchedule T B τ}.Finite := by
  refine Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin (B + 2) => Set.Iic T)
    (fun _ => Set.finite_Iic T)) ?_
  intro τ hτ m _
  show τ m ≤ T
  rw [← hτ.2.1]
  exact hτ.2.2 (by simp [Fin.le_def]; omega)

lemma schedule_nonempty (T B : ℕ) : {τ : Fin (B + 2) → ℕ | IsSchedule T B τ}.Nonempty := by
  refine ⟨fun m => if m = 0 then 0 else T, ?_, ?_, ?_⟩
  · simp
  · have : Fin.last (B + 1) ≠ 0 := by simp [Fin.ext_iff]
    simp [this]
  · intro a b hab
    by_cases ha : a = 0
    · simp [ha]
    · have hb : b ≠ 0 := by
        intro hb; subst hb
        exact ha (le_antisymm hab (Fin.zero_le _))
      simp [ha, hb]

lemma optimum_attained (T B : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :
    ∃ τ, IsSchedule T B τ ∧ blockProgram S Δ τ = blockOptimum T B S Δ := by
  have hfin := (schedule_finite T B).image (blockProgram S Δ)
  have hne := (schedule_nonempty T B).image (blockProgram S Δ)
  have := hne.csInf_mem hfin
  obtain ⟨τ, hτ, h⟩ := this
  exact ⟨τ, hτ, h⟩

theorem upper_parts (T d B K : ℕ) (hT : 0 < T) (θ₀ : Vector d)
    (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) :
    blockMinimaxRisk T d B K θ₀ S Δ ≤ ENNReal.ofReal (2 * blockOptimum T B S Δ) ∧
    (∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ → blockProgram S Δ τ = blockOptimum T B S Δ →
      IsCausal (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      HasDeterministicDates (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      blockWorstRisk θ₀ S Δ (blockGridPolicy T d B K θ₀ S Δ τ) ≤
        ENNReal.ofReal (2 * blockOptimum T B S Δ)) := by
  have key : ∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ →
      blockProgram S Δ τ = blockOptimum T B S Δ →
      IsCausal (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      HasDeterministicDates (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      blockWorstRisk θ₀ S Δ (blockGridPolicy T d B K θ₀ S Δ τ) ≤
        ENNReal.ofReal (2 * blockOptimum T B S Δ) := by
    intro τ hτ hopt
    refine ⟨isCausal_block T d B K θ₀ S Δ hΔ τ hτ, fun j => ⟨slotDate τ j, fun _ => rfl⟩, ?_⟩
    have := worst_le T d B K hT θ₀ S hS Δ hΔ hΔ₁ hΔsum τ hτ
    rwa [hopt] at this
  refine ⟨?_, key⟩
  obtain ⟨τ, hτ, hopt⟩ := optimum_attained T B S Δ
  obtain ⟨hc, -, hw⟩ := key τ hτ hopt
  exact le_trans (sInf_le ⟨unitSeed, blockGridPolicy T d B K θ₀ S Δ τ, hc, rfl⟩) hw

end TRS.Dev.BlockUpper
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper

noncomputable section

namespace TRS.Dev.BlockLower

/-- The top level used in block `i`. -/
def Lof (T : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) (i : Fin K) : ℤ :=
  max (firstLevel (S i).card (Δ i)) ⌈Real.logb 2 (T : ℝ)⌉

abbrev FDraws (T : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :=
  (i : Fin K) → PriorDraws (S i) (Δ i) (Lof T S Δ i)

def fullLaw (T : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :
    Measure (FDraws T S Δ) :=
  Measure.pi (fun i => uniformLevels (S i) (Δ i) (Lof T S Δ i))

abbrev FSample (s : RandomSeed) (T d : ℕ) {K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :=
  s.space × (FDraws T S Δ × GaussianRows T d)

def flaw (s : RandomSeed) (T d : ℕ) {K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :
    Measure (FSample s T d S Δ) :=
  s.law.prod ((fullLaw T S Δ).prod (gaussianRows T d))

/-- The chosen coordinate of each block. -/
def pt {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S) (i : Fin K) : S i :=
  ⟨(hS.1 i).choose, (hS.1 i).choose_spec⟩

/-- The deterministic part of the block displacement. -/
def aVec {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S) (Δ : Fin K → ℝ)
    (i : Fin K) : BlockVector (S i) :=
  (Δ i / 2) • EuclideanSpace.single (pt S hS i) (1 : ℝ)

/-- The block displacement of the target. -/
def disp (T : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (u : FDraws T S Δ) : Vector d :=
  ∑ i, embedBlock (S i) (aVec S hS Δ i + hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i))

def targ (T : ℕ) {d K : ℕ} (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (u : FDraws T S Δ) : Vector d :=
  θ₀ + disp T S hS Δ u

lemma embed_sum_apply {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (f : (j : Fin K) → BlockVector (S j)) (i : Fin K) (k : Fin d) (hk : k ∈ S i) :
    (∑ j, embedBlock (S j) (f j)) k = f i ⟨k, hk⟩ := by
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · simp [embedBlock, hk]
  · intro j _ hj
    have : k ∉ S j := fun hkj =>
      Finset.disjoint_left.1 (hS.2.1 hj) hkj hk
    simp [embedBlock, this]
  · simp

lemma bsq_embed_sum {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (f : (j : Fin K) → BlockVector (S j)) (i : Fin K) :
    bsq (S i) (∑ j, embedBlock (S j) (f j)) = ‖f i‖ ^ 2 := by
  unfold bsq
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Finset.sum_coe_sort (S i)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [embed_sum_apply S hS f i k.1 k.2]

lemma norm_single_block {d : ℕ} (S : Finset (Fin d)) (p : S) :
    ‖(EuclideanSpace.single p (1 : ℝ) : BlockVector S)‖ = 1 := by simp

lemma norm_aVec {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (i : Fin K) : ‖aVec S hS Δ i‖ = Δ i / 2 := by
  unfold aVec
  rw [norm_smul, norm_single_block, Real.norm_eq_abs, abs_of_pos (by linarith [hΔ i])]
  ring

lemma disp_mem (T : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (u : FDraws T S Δ)
    (hH : ∀ i, ‖hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)‖ < Δ i / 32) :
    disp T S hS Δ u ∈ blockBall S Δ := by
  rw [mem_blockBall_iff S Δ hΔ]
  intro i
  unfold disp
  rw [bsq_embed_sum S hS]
  have h1 := norm_add_le (aVec S hS Δ i) (hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i))
  rw [norm_aVec S hS Δ hΔ] at h1
  have h2 := hH i
  have h3 := hΔ i
  have h4 : 0 ≤ ‖aVec S hS Δ i + hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)‖ := norm_nonneg _
  nlinarith

/-- Reshuffle `(u,(σ,z)) ↦ (σ,(u,z))`. -/
def reshuffle (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β × γ) ≃ᵐ β × (α × γ) :=
  (MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm (α := α) (β := β)).prodCongr (MeasurableEquiv.refl γ))).trans
    MeasurableEquiv.prodAssoc

lemma reshuffle_mp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (reshuffle α β γ) (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  unfold reshuffle
  have h1 := (measurePreserving_prodAssoc μ ν ρ).symm
  have h2 : MeasurePreserving (Prod.map Prod.swap (id : γ → γ)) ((μ.prod ν).prod ρ)
      ((ν.prod μ).prod ρ) := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
        (MeasurePreserving.id ρ)
  have h3 := measurePreserving_prodAssoc ν μ ρ
  exact h3.comp (h2.comp h1)

instance instProbUC : IsProbabilityMeasure uniformCoordinate := by
  constructor
  have hemb : MeasurableEmbedding (Subtype.val : CubeCoordinate → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  unfold uniformCoordinate
  rw [Measure.smul_apply, hemb.comap_apply]
  simp
  have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := rfl
  rw [this, Real.volume_Icc]
  norm_num
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.inv_mul_cancel] <;> simp

instance instProbU {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    IsProbabilityMeasure (uniformLevels S Δ L) := by
  unfold uniformLevels; infer_instance

instance instProbFull (T : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) :
    IsProbabilityMeasure (fullLaw T S Δ) := by
  unfold fullLaw; infer_instance

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper

noncomputable section

namespace TRS.Dev.BlockLower

/-- Realized transcript at a prior sample. -/
def ftr {s : RandomSeed} {T d K : ℕ} (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (ω : FSample s T d S Δ) : Transcript s T d :=
  (ω.1, observations (fun _ : Fin T => targ T θ₀ S hS Δ ω.2.1) ω.2.2)

/-- Per-sample loss. -/
def pathLoss {s : RandomSeed} {T d B K : ℕ} (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (π : ReleasePolicy s T d B)
    (ω : FSample s T d S Δ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin T,
    ‖deployed θ₀ π (ftr θ₀ S hS Δ ω) i - targ T θ₀ S hS Δ ω.2.1‖ ^ 2)

theorem prior_le_worst {s : RandomSeed} {T d B K : ℕ} (θ₀ : Vector d)
    (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S) (Δ : Fin K → ℝ)
    (hΔ : ∀ i, 0 < Δ i) (π : ReleasePolicy s T d B)
    (hH : ∀ (u : FDraws T S Δ) i, ‖hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)‖ < Δ i / 32) :
    ∫⁻ ω, pathLoss θ₀ S hS Δ π ω ∂(flaw s T d S Δ) ≤ blockWorstRisk θ₀ S Δ π := by
  have hmp := reshuffle_mp (fullLaw T S Δ) s.law (gaussianRows T d)
  have h1 : ∫⁻ ω, pathLoss θ₀ S hS Δ π ω ∂(flaw s T d S Δ) =
      ∫⁻ p, pathLoss θ₀ S hS Δ π (reshuffle _ _ _ p)
        ∂((fullLaw T S Δ).prod (s.law.prod (gaussianRows T d))) := by
    have := hmp.lintegral_comp_emb (reshuffle _ _ _).measurableEmbedding
      (pathLoss θ₀ S hS Δ π)
    unfold flaw
    exact this.symm
  rw [h1]
  refine (lintegral_prod_le _).trans ?_
  have h2 : ∀ u : FDraws T S Δ,
      ∫⁻ y, pathLoss θ₀ S hS Δ π (reshuffle _ _ _ (u, y)) ∂(s.law.prod (gaussianRows T d)) ≤
        blockWorstRisk θ₀ S Δ π := by
    intro u
    have hmem : targ T θ₀ S hS Δ u - θ₀ ∈ blockBall S Δ := by
      have : targ T θ₀ S hS Δ u - θ₀ = disp T S hS Δ u := by unfold targ; abel
      rw [this]
      exact disp_mem T S hS Δ hΔ u (hH u)
    refine le_trans (le_of_eq ?_) (le_iSup _ ⟨_, hmem⟩)
    unfold policyRisk pathLoss ftr
    rfl
  calc ∫⁻ x, ∫⁻ y, pathLoss θ₀ S hS Δ π (reshuffle _ _ _ (x, y)) ∂(s.law.prod (gaussianRows T d))
        ∂(fullLaw T S Δ) ≤ ∫⁻ x, blockWorstRisk θ₀ S Δ π ∂(fullLaw T S Δ) :=
        lintegral_mono h2
    _ = blockWorstRisk θ₀ S Δ π := by rw [lintegral_const, measure_univ, mul_one]

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.BlockLower

/-- Add the linear predictor of a known vector `w` to every label. -/
def adjust {T d : ℕ} (w : Vector d) (h : Data T d) : Data T d :=
  fun t => ((h t).1, (h t).2 + inner ℝ (h t).1 w)

lemma measurable_adjust (T d : ℕ) :
    Measurable (fun p : Vector d × Data T d => adjust p.1 p.2) := by
  unfold adjust
  refine measurable_pi_lambda _ (fun t => ?_)
  have h1 : Measurable (fun p : Vector d × Data T d => (p.2 t).1) :=
    ((measurable_pi_apply t).comp measurable_snd).fst
  have h2 : Measurable (fun p : Vector d × Data T d => (p.2 t).2) :=
    ((measurable_pi_apply t).comp measurable_snd).snd
  exact h1.prodMk (h2.add (h1.inner measurable_fst))

/-- Transcript change of seed. -/
def tmap {s s' : RandomSeed} {T d : ℕ} (φ : s'.space → s.space × Vector d)
    (ω : Transcript s' T d) : Transcript s T d :=
  ((φ ω.1).1, adjust (φ ω.1).2 ω.2)

lemma measurable_tmap {s s' : RandomSeed} {T d : ℕ} (φ : s'.space → s.space × Vector d)
    (hφ : Measurable φ) : Measurable (tmap (T := T) (d := d) φ) := by
  unfold tmap
  refine (hφ.comp measurable_fst).fst.prodMk ?_
  exact (measurable_adjust T d).comp (((hφ.comp measurable_fst).snd).prodMk measurable_snd)

def trunc {s : RandomSeed} (T d n : ℕ) (ω : Transcript s T d) : Transcript s T d :=
  (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))

lemma tmap_trunc {s s' : RandomSeed} {T d : ℕ} (φ : s'.space → s.space × Vector d) (n : ℕ)
    (ω : Transcript s' T d) :
    tmap φ (trunc T d n ω) = trunc T d n (tmap φ ω) := by
  unfold tmap trunc adjust
  ext1
  · rfl
  · funext i
    by_cases h : i.val < n <;> simp [h]

lemma measurable_tmap_info {s s' : RandomSeed} {T d : ℕ} (φ : s'.space → s.space × Vector d)
    (hφ : Measurable φ) (n : ℕ) :
    @Measurable _ _ (information s' T d n) (information s T d n) (tmap φ) := by
  rw [measurable_iff_comap_le]
  unfold information
  rw [MeasurableSpace.comap_comp]
  have : (fun ω : Transcript s T d => (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) ∘
      tmap φ = tmap φ ∘ (fun ω : Transcript s' T d =>
        (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) := by
    funext ω
    exact (tmap_trunc φ n ω).symm
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.1 (measurable_tmap φ hφ))

/-- The policy that runs `π` on the seed-adjusted transcript. -/
def shifted {s s' : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B)
    (φ : s'.space → s.space × Vector d) : ReleasePolicy s' T d B where
  date := fun j ω => π.date j (tmap φ ω)
  head := fun j ω => π.head j (tmap φ ω)

lemma isCausal_shifted {s s' : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (φ : s'.space → s.space × Vector d) (hφ : Measurable φ) :
    IsCausal (shifted π φ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hπ
  refine ⟨fun j ω => h1 j _, fun ω a b hab => h2 _ hab, ?_, ?_⟩
  · intro j n
    exact (measurable_tmap_info φ hφ n) (h3 j n)
  · intro j n
    exact @Measurable.comp _ _ _ (information s' T d n) (information s T d n) _ _ _
      (h4 j n) (measurable_tmap_info φ hφ n)

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper

noncomputable section

namespace TRS.Dev.BlockLower

def vecOf {d : ℕ} {S : Finset (Fin d)} (v : S → CubeCoordinate) : BlockVector S :=
  WithLp.toLp 2 (fun i : S => (v i : ℝ))

lemma measurable_vecOf {d : ℕ} {S : Finset (Fin d)} : Measurable (vecOf (S := S)) := by
  unfold vecOf
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

lemma measurable_hiddenShift {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    Measurable (hiddenShift S Δ L) := by
  unfold hiddenShift
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  have : Measurable fun u : PriorDraws S Δ L => vecOf (u ℓ) :=
    measurable_vecOf.comp (measurable_pi_apply ℓ)
  exact this.const_smul (levelAmplitude ℓ.val)

lemma measurable_embedBlock {d : ℕ} (S : Finset (Fin d)) : Measurable (embedBlock S) := by
  unfold embedBlock
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ S
  · simp only [h, dif_pos]
    exact (measurable_pi_apply (⟨i, h⟩ : S)).comp (PiLp.continuous_ofLp 2 _).measurable
  · simp [h]

lemma embedBlock_add {d : ℕ} (S : Finset (Fin d)) (v w : BlockVector S) :
    embedBlock S (v + w) = embedBlock S v + embedBlock S w := by
  ext i
  unfold embedBlock
  by_cases h : i ∈ S <;> simp [h]

lemma le_zpow_ceil (x : ℝ) (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉ := by
  have h1 : x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
  have h2 : (2 : ℝ) ^ (Real.logb 2 x) ≤ (2 : ℝ) ^ ((⌈Real.logb 2 x⌉ : ℤ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
  rw [Real.rpow_intCast] at h2
  linarith

lemma blockProj_embed {d : ℕ} (S : Finset (Fin d)) (h : BlockVector S) :
    blockProjection S (embedBlock S h) = h := by
  ext i
  simp [blockProjection, embedBlock]

lemma blockProj_sub {d : ℕ} (S : Finset (Fin d)) (v w : Vector d) :
    blockProjection S (v - w) = blockProjection S v - blockProjection S w := by
  ext i; simp [blockProjection]

/-- The centre of the prior. -/
def ctr (T : ℕ) {d K : ℕ} (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) : Vector d :=
  θ₀ + ∑ j, embedBlock (S j) (aVec S hS Δ j)

/-- The contribution of the other blocks. -/
def wvec (T : ℕ) {d m : ℕ} (S : Fin (m + 1) → Finset (Fin d)) (Δ : Fin (m + 1) → ℝ)
    (i : Fin (m + 1))
    (r : (j : Fin m) → PriorDraws (S (i.succAbove j)) (Δ (i.succAbove j))
      (Lof T S Δ (i.succAbove j))) : Vector d :=
  ∑ j : Fin m, embedBlock (S (i.succAbove j))
    (hiddenShift (S (i.succAbove j)) (Δ (i.succAbove j)) (Lof T S Δ (i.succAbove j)) (r j))

lemma targ_eq (T : ℕ) {d m : ℕ} (θ₀ : Vector d) (S : Fin (m + 1) → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (u : FDraws T S Δ) :
    targ T θ₀ S hS Δ u = ctr T θ₀ S hS Δ +
      embedBlock (S i) (hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)) +
      wvec T S Δ i (fun j => u (i.succAbove j)) := by
  unfold targ disp ctr wvec
  simp only [embedBlock_add, Finset.sum_add_distrib]
  rw [Fin.sum_univ_succAbove (fun j => embedBlock (S j)
    (hiddenShift (S j) (Δ j) (Lof T S Δ j) (u j))) i]
  abel

lemma wvec_apply_zero (T : ℕ) {d m : ℕ} (S : Fin (m + 1) → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin (m + 1) → ℝ) (i : Fin (m + 1))
    (r : (j : Fin m) → PriorDraws (S (i.succAbove j)) (Δ (i.succAbove j))
      (Lof T S Δ (i.succAbove j))) (k : Fin d) (hk : k ∈ S i) : wvec T S Δ i r k = 0 := by
  unfold wvec
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : k ∉ S (i.succAbove j) := fun hkj =>
    Finset.disjoint_left.1 (hS.2.1 (Fin.succAbove_ne i j)) hkj hk
  simp [embedBlock, this]

lemma measurable_wvec (T : ℕ) {d m : ℕ} (S : Fin (m + 1) → Finset (Fin d))
    (Δ : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    Measurable (wvec T S Δ i) := by
  unfold wvec
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact (measurable_embedBlock _).comp
    ((measurable_hiddenShift _ _ _).comp (measurable_pi_apply j))

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper

noncomputable section

namespace TRS.Dev.BlockLower

lemma psi_mp {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (A : Measure α) (B : Measure β) (C : Measure γ) (D : Measure δ)
    [SFinite A] [SFinite B] [SFinite C] [SFinite D] :
    MeasurePreserving (fun p : α × ((β × γ) × δ) => ((p.1, p.2.1.2), (p.2.1.1, p.2.2)))
      (A.prod ((B.prod C).prod D)) ((A.prod C).prod (B.prod D)) := by
  have h1 : MeasurePreserving (Prod.map (id : α → α) (MeasurableEquiv.prodAssoc : (β × γ) × δ ≃ᵐ β × (γ × δ)))
      (A.prod ((B.prod C).prod D)) (A.prod (B.prod (C.prod D))) :=
    (MeasurePreserving.id A).prod (measurePreserving_prodAssoc B C D)
  have h2 := reshuffle_mp A B (C.prod D)
  have h3 : MeasurePreserving (Prod.map (id : β → β)
      (MeasurableEquiv.prodAssoc : (α × γ) × δ ≃ᵐ α × (γ × δ)).symm)
      (B.prod (A.prod (C.prod D))) (B.prod ((A.prod C).prod D)) :=
    (MeasurePreserving.id B).prod (measurePreserving_prodAssoc A C D).symm
  have h4 := reshuffle_mp B (A.prod C) D
  have := h4.comp (h3.comp (h2.comp h1))
  exact this

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper

noncomputable section

namespace TRS.Dev.BlockLower

theorem block_event {s : RandomSeed} {T d B m : ℕ} (hT : 0 < T) (hd : 0 < d) (θ₀ : Vector d)
    (S : Fin (m + 1) → Finset (Fin d)) (hS : IsBlockPartition S) (Δ : Fin (m + 1) → ℝ)
    (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (π : ReleasePolicy s T d B) (hπ : IsCausal π) (i : Fin (m + 1)) :
    ∃ E : Set (FSample s T d S Δ), MeasurableSet E ∧
      ENNReal.ofReal (1 - (B : ℝ) * ((Lof T S Δ i - firstLevel (S i).card (Δ i) + 1 : ℤ) : ℝ) *
        (9 / 25 : ℝ) ^ (S i).card) ≤ flaw s T d S Δ E ∧
      ∀ ω ∈ E, ∀ j : Fin B, π.date j (ftr θ₀ S hS Δ ω) < T →
        (2 : ℝ) ^ (-19 : ℤ) * (S i).card /
          max (π.date j (ftr θ₀ S hS Δ ω) : ℝ) (16 * (S i).card / Δ i ^ 2) ≤
        bsq (S i) (π.head j (ftr θ₀ S hS Δ ω) - targ T θ₀ S hS Δ ω.2.1) := by
  classical
  let R : Type := (j : Fin m) → PriorDraws (S (i.succAbove j)) (Δ (i.succAbove j))
    (Lof T S Δ (i.succAbove j))
  let restLaw : Measure R := Measure.pi (fun j => uniformLevels (S (i.succAbove j))
    (Δ (i.succAbove j)) (Lof T S Δ (i.succAbove j)))
  haveI : IsProbabilityMeasure restLaw := by
    show IsProbabilityMeasure (Measure.pi (fun j => uniformLevels (S (i.succAbove j))
      (Δ (i.succAbove j)) (Lof T S Δ (i.succAbove j))))
    infer_instance
  let s' : RandomSeed :=
    { space := s.space × R
      measurableSpace := inferInstance
      law := s.law.prod restLaw
      probability := inferInstance }
  let φ : s'.space → s.space × Vector d := fun p => (p.1, wvec T S Δ i p.2)
  have hφ : Measurable φ := measurable_fst.prodMk ((measurable_wvec T S Δ i).comp measurable_snd)
  have hπ' : IsCausal (shifted π φ) := isCausal_shifted π hπ φ hφ
  have hSi : 0 < (S i).card := Finset.card_pos.2 (hS.1 i)
  have hL : firstLevel (S i).card (Δ i) ≤ Lof T S Δ i := le_max_left _ _
  have hLT : (T : ℝ) ≤ (2 : ℝ) ^ Lof T S Δ i :=
    le_trans (le_zpow_ceil T (by exact_mod_cast hT))
      (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  have key := common_lower_error_event T d hT hd (S i) hSi (Δ i) (hΔ i) (hΔ₁ i)
    (Lof T S Δ i) hL hLT (fun _ => ctr T θ₀ S hS Δ) (blockProjection (S i) (ctr T θ₀ S hS Δ))
    (fun _ => rfl) s'
  obtain ⟨-, -, hc⟩ := key
  obtain ⟨E', hE'm, hE'μ, hE'⟩ := hc B (shifted π φ) hπ'
  let e := MeasurableEquiv.piFinSuccAbove
    (fun j : Fin (m + 1) => PriorDraws (S j) (Δ j) (Lof T S Δ j)) i
  have hemp : MeasurePreserving e (fullLaw T S Δ)
      ((uniformLevels (S i) (Δ i) (Lof T S Δ i)).prod restLaw) :=
    measurePreserving_piFinSuccAbove
      (fun j : Fin (m + 1) => uniformLevels (S j) (Δ j) (Lof T S Δ j)) i
  have h1 : MeasurePreserving (Prod.map (id : s.space → s.space)
      (Prod.map e (id : GaussianRows T d → GaussianRows T d)))
      (flaw s T d S Δ)
      (s.law.prod (((uniformLevels (S i) (Δ i) (Lof T S Δ i)).prod restLaw).prod
        (gaussianRows T d))) :=
    (MeasurePreserving.id s.law).prod (hemp.prod (MeasurePreserving.id _))
  have h2 := psi_mp s.law (uniformLevels (S i) (Δ i) (Lof T S Δ i)) restLaw (gaussianRows T d)
  have hΨ := h2.comp h1
  set Ψ : FSample s T d S Δ → PriorSample s' T d (S i) (Δ i) (Lof T S Δ i) :=
    fun ω => ((ω.1, (e ω.2.1).2), ((e ω.2.1).1, ω.2.2)) with hΨdef
  have hΨ' : MeasurePreserving Ψ (flaw s T d S Δ) (priorLaw s' T d (S i) (Δ i) (Lof T S Δ i)) :=
    hΨ
  refine ⟨Ψ ⁻¹' E', hΨ'.measurable hE'm, ?_, ?_⟩
  · rw [hΨ'.measure_preimage hE'm.nullMeasurableSet]
    exact hE'μ
  · intro ω hω j hlt
    have htr : tmap φ (priorTranscript (s := s') (S := S i) (Δ := Δ i) (L := Lof T S Δ i)
        (fun _ : Fin T => ctr T θ₀ S hS Δ) (Ψ ω)) = ftr θ₀ S hS Δ ω := by
      unfold tmap priorTranscript ftr
      refine Prod.ext rfl ?_
      funext t
      simp only [adjust, observations]
      rw [targ_eq T θ₀ S hS Δ i ω.2.1]
      refine Prod.ext rfl ?_
      simp only [φ, hΨdef]
      have he1 : (e ω.2.1).1 = ω.2.1 i := rfl
      have he2 : (e ω.2.1).2 = fun j => ω.2.1 (i.succAbove j) := rfl
      rw [he1, he2]
      simp only [inner_add_right]
      ring
    have hmem : Ψ ω ∈ E' := hω
    have hlt' : (shifted π φ).date j (priorTranscript (s := s') (S := S i) (Δ := Δ i)
        (L := Lof T S Δ i) (fun _ : Fin T => ctr T θ₀ S hS Δ) (Ψ ω)) < T := by
      show π.date j (tmap φ _) < T
      rw [htr]; exact hlt
    have h := hE' (Ψ ω) hmem j hlt'
    have hd' : (shifted π φ).date j (priorTranscript (s := s') (S := S i) (Δ := Δ i)
        (L := Lof T S Δ i) (fun _ : Fin T => ctr T θ₀ S hS Δ) (Ψ ω)) =
        π.date j (ftr θ₀ S hS Δ ω) := by
      show π.date j (tmap φ _) = _
      rw [htr]
    have hh : (shifted π φ).head j (priorTranscript (s := s') (S := S i) (Δ := Δ i)
        (L := Lof T S Δ i) (fun _ : Fin T => ctr T θ₀ S hS Δ) (Ψ ω)) =
        π.head j (ftr θ₀ S hS Δ ω) := by
      show π.head j (tmap φ _) = _
      rw [htr]
    rw [hd', hh] at h
    refine h.trans (le_of_eq ?_)
    -- identify the error
    have e1 : blockProjection (S i) (π.head j (ftr θ₀ S hS Δ ω)) -
        blockProjection (S i) (ctr T θ₀ S hS Δ) -
        hiddenShift (S i) (Δ i) (Lof T S Δ i) (Ψ ω).2.1 =
        blockProjection (S i) (π.head j (ftr θ₀ S hS Δ ω) - ctr T θ₀ S hS Δ -
          embedBlock (S i) (hiddenShift (S i) (Δ i) (Lof T S Δ i) (ω.2.1 i))) := by
      rw [blockProj_sub, blockProj_sub, blockProj_embed]
      rfl
    have e2 : bsq (S i) (π.head j (ftr θ₀ S hS Δ ω) - ctr T θ₀ S hS Δ -
          embedBlock (S i) (hiddenShift (S i) (Δ i) (Lof T S Δ i) (ω.2.1 i))) =
        bsq (S i) (π.head j (ftr θ₀ S hS Δ ω) - targ T θ₀ S hS Δ ω.2.1) := by
      unfold bsq
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [targ_eq T θ₀ S hS Δ i ω.2.1]
      have hw := wvec_apply_zero T S hS Δ i (fun j => ω.2.1 (i.succAbove j)) k hk
      simp only [PiLp.sub_apply, PiLp.add_apply] at hw ⊢
      rw [hw]; ring
    rw [e1, norm_blockProjection_sq, e2]

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper TRS.Dev.BlockCopy

noncomputable section

namespace TRS.Dev.BlockLower

/-- The realized schedule of a policy on a transcript. -/
def sched {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) (ω : Transcript s T d) :
    Fin (B + 2) → ℕ :=
  fun m => if m.val = 0 then 0 else if h : m.val - 1 < B then π.date ⟨m.val - 1, h⟩ ω else T

lemma sched_slot {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B)
    (ω : Transcript s T d) (j : Fin B) : sched π ω j.succ.castSucc = π.date j ω := by
  unfold sched
  have h1 : (j.succ.castSucc : Fin (B + 2)).val = j.val + 1 := by simp
  simp only [h1]
  rw [if_neg (by omega), dif_pos (by omega)]
  rfl

lemma sched_isSchedule {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (ω : Transcript s T d) : IsSchedule T B (sched π ω) := by
  obtain ⟨h1, h2, -, -⟩ := hπ
  refine ⟨?_, ?_, ?_⟩
  · simp [sched]
  · simp only [sched, Fin.val_last]
    rw [if_neg (by omega), dif_neg (by omega)]
  · intro a b hab
    have hab' : a.val ≤ b.val := hab
    unfold sched
    by_cases ha : a.val = 0
    · simp [ha]
    · have hb : b.val ≠ 0 := by omega
      simp only [ha, hb, if_false]
      by_cases hb1 : b.val - 1 < B
      · have ha1 : a.val - 1 < B := by omega
        rw [dif_pos hb1, dif_pos ha1]
        exact h2 ω (by simp [Fin.le_def]; omega)
      · rw [dif_neg hb1]
        by_cases ha1 : a.val - 1 < B
        · rw [dif_pos ha1]; exact h1 _ _
        · rw [dif_neg ha1]

lemma deployed_phase_gen {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (ω : Transcript s T d) (τ : Fin (B + 2) → ℕ) (hτ0 : τ 0 = 0) (hmono : Monotone τ)
    (hdate : ∀ k : Fin B, π.date k ω = τ k.succ.castSucc) (j : Fin (B + 1)) (i : Fin T)
    (h1 : τ j.castSucc ≤ i.val) (h2 : i.val < τ j.succ) :
    (j.val = 0 ∧ deployed θ₀ π ω i = θ₀) ∨
    (∃ k : Fin B, k.val + 1 = j.val ∧ deployed θ₀ π ω i = π.head k ω ∧
      π.date k ω = τ j.castSucc) := by
  rcases deployed_spec θ₀ π ω i with ⟨h, hall⟩ | ⟨k, hk, hdep, hlater⟩
  · left
    refine ⟨?_, h⟩
    by_contra hj
    let k : Fin B := ⟨j.val - 1, by omega⟩
    have := hall k
    rw [hdate] at this
    have e : τ k.succ.castSucc = τ j.castSucc := by
      congr 1; ext; simp [k]; omega
    rw [e] at this
    omega
  · right
    refine ⟨k, ?_, hdep, ?_⟩
    · rw [hdate] at hk
      have hlt : k.succ.castSucc < j.succ := by
        refine hmono.reflect_lt ?_
        omega
      have hkj : k.val + 1 < j.val + 1 := by simpa [Fin.lt_def] using hlt
      by_contra hne
      have hlt2 : k.val + 1 < j.val := by omega
      let k' : Fin B := ⟨k.val + 1, by omega⟩
      have hk' : k < k' := by simp [Fin.lt_def, k']
      have h3 := hlater k' hk'
      rw [hdate] at h3
      have : τ k'.succ.castSucc ≤ τ j.castSucc := by
        exact hmono (by simp [Fin.le_def, k']; omega)
      omega
    · rw [hdate]
      have hkj : k.val + 1 = j.val := by
        rw [hdate] at hk
        have hlt : k.succ.castSucc < j.succ := by
          refine hmono.reflect_lt ?_
          omega
        have hkj : k.val + 1 < j.val + 1 := by simpa [Fin.lt_def] using hlt
        by_contra hne
        have hlt2 : k.val + 1 < j.val := by omega
        let k' : Fin B := ⟨k.val + 1, by omega⟩
        have hk' : k < k' := by simp [Fin.lt_def, k']
        have h3 := hlater k' hk'
        rw [hdate] at h3
        have : τ k'.succ.castSucc ≤ τ j.castSucc := by
          exact hmono (by simp [Fin.le_def, k']; omega)
        omega
      congr 1; ext; simp; omega

/-- Lower bound version of the phase sum. -/
lemma phase_sum_lower (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ)
    (g : ℕ → ℝ) (F : ℕ → ℝ)
    (h : ∀ j : Fin (B + 1), ∀ i, τ j.castSucc ≤ i → i < τ j.succ → F (τ j.castSucc) ≤ g i) :
    ∑ j : Fin (B + 1), phaseLength τ j * F (phaseStart τ j) ≤ ∑ i ∈ Finset.range T, g i := by
  have hmono : Monotone τ := hτ.2.2
  have ht := tt_mono T B τ hτ
  have t0 := tt_zero T B τ hτ
  have tB := tt_last T B τ hτ
  have tj := tt_cast T B τ
  have tj1 := tt_succ T B τ
  have hs := sum_Ico_phases' (tt T B τ) ht g (B + 1)
  rw [t0, tB] at hs
  rw [Finset.range_eq_Ico, hs, Finset.sum_range]
  refine Finset.sum_le_sum (fun j _ => ?_)
  calc phaseLength τ j * F (phaseStart τ j)
      = ∑ i ∈ Finset.Ico (tt T B τ j.val) (tt T B τ (j.val + 1)), F (τ j.castSucc) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, tj, tj1]
        have hle : τ j.castSucc ≤ τ j.succ := hmono (by simp [Fin.le_def])
        have hpl : phaseLength τ j = ((τ j.succ - τ j.castSucc : ℕ) : ℝ) := by
          unfold phaseLength; rw [Nat.cast_sub hle]
        rw [hpl]; rfl
    _ ≤ ∑ i ∈ Finset.Ico (tt T B τ j.val) (tt T B τ (j.val + 1)), g i := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [Finset.mem_Ico, tj, tj1] at hi
        exact h j i hi.1 hi.2

lemma coeff_lower (dᵢ : ℕ) (Δᵢ : ℝ) (hd : 0 < dᵢ) (hΔ : 0 < Δᵢ) (n : ℕ) :
    (2 : ℝ) ^ (-23 : ℤ) * blockCoeff dᵢ Δᵢ n ≤
      (2 : ℝ) ^ (-19 : ℤ) * dᵢ / max (n : ℝ) (16 * (dᵢ : ℝ) / Δᵢ ^ 2) := by
  have hd' : (0 : ℝ) < dᵢ := by exact_mod_cast hd
  have hx : 0 < 16 * (dᵢ : ℝ) / Δᵢ ^ 2 := by positivity
  have hmax : 0 < max (n : ℝ) (16 * (dᵢ : ℝ) / Δᵢ ^ 2) := lt_max_of_lt_right hx
  rw [le_div_iff₀ hmax]
  have e1 : (2 : ℝ) ^ (-23 : ℤ) = (2 : ℝ) ^ (-19 : ℤ) / 16 := by norm_num
  have h19 : (0 : ℝ) < (2 : ℝ) ^ (-19 : ℤ) := by positivity
  unfold blockCoeff
  by_cases hn : n = 0
  · simp only [hn, if_true, Nat.cast_zero]
    rw [max_eq_right hx.le, e1]
    field_simp
    nlinarith [hΔ]
  · simp only [hn, if_false]
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [e1]
    -- coeff = min (d/n) Δ²
    rcases le_total (n : ℝ) (16 * (dᵢ : ℝ) / Δᵢ ^ 2) with h | h
    · rw [max_eq_right h]
      have : min ((dᵢ : ℝ) / n) (Δᵢ ^ 2) ≤ Δᵢ ^ 2 := min_le_right _ _
      calc (2 : ℝ) ^ (-19 : ℤ) / 16 * min ((dᵢ : ℝ) / n) (Δᵢ ^ 2) * (16 * (dᵢ : ℝ) / Δᵢ ^ 2)
          ≤ (2 : ℝ) ^ (-19 : ℤ) / 16 * Δᵢ ^ 2 * (16 * (dᵢ : ℝ) / Δᵢ ^ 2) := by gcongr
        _ = (2 : ℝ) ^ (-19 : ℤ) * dᵢ := by field_simp
    · rw [max_eq_left h]
      have : min ((dᵢ : ℝ) / n) (Δᵢ ^ 2) ≤ (dᵢ : ℝ) / n := min_le_left _ _
      calc (2 : ℝ) ^ (-19 : ℤ) / 16 * min ((dᵢ : ℝ) / n) (Δᵢ ^ 2) * (n : ℝ)
          ≤ (2 : ℝ) ^ (-19 : ℤ) / 16 * ((dᵢ : ℝ) / n) * n := by gcongr
        _ = (2 : ℝ) ^ (-19 : ℤ) / 16 * dᵢ := by field_simp
        _ ≤ (2 : ℝ) ^ (-19 : ℤ) * dᵢ := by nlinarith

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper TRS.Dev.BlockCopy

noncomputable section

namespace TRS.Dev.BlockLower

lemma first_phase_bound (T : ℕ) {d K : ℕ} (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (u : FDraws T S Δ)
    (hH : ∀ i, ‖hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)‖ < Δ i / 32) (i : Fin K) :
    (2 : ℝ) ^ (-23 : ℤ) * Δ i ^ 2 ≤ bsq (S i) (θ₀ - targ T θ₀ S hS Δ u) := by
  have e : bsq (S i) (θ₀ - targ T θ₀ S hS Δ u) = bsq (S i) (disp T S hS Δ u) := by
    unfold bsq
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [targ, PiLp.sub_apply, PiLp.add_apply]
    ring
  rw [e]
  unfold disp
  rw [bsq_embed_sum S hS]
  have h1 := norm_sub_norm_le (aVec S hS Δ i) (-(hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)))
  rw [sub_neg_eq_add, norm_neg, norm_aVec S hS Δ hΔ] at h1
  have h2 := hH i
  have h3 := hΔ i
  have h4 : Δ i / 2 - Δ i / 32 ≤ ‖aVec S hS Δ i + hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)‖ := by
    linarith
  have h5 : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 / 8 := by norm_num
  have h6 : Δ i ^ 2 / 8 ≤ ‖aVec S hS Δ i + hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)‖ ^ 2 := by
    nlinarith
  have h7 := mul_le_mul_of_nonneg_right h5 (sq_nonneg (Δ i))
  exact h7.trans (by linarith [h6])

theorem pointwise_lower {s : RandomSeed} {T d B K : ℕ} (θ₀ : Vector d)
    (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S) (Δ : Fin K → ℝ)
    (hΔ : ∀ i, 0 < Δ i) (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (ω : FSample s T d S Δ)
    (hH : ∀ i, ‖hiddenShift (S i) (Δ i) (Lof T S Δ i) (ω.2.1 i)‖ < Δ i / 32)
    (hG : ∀ i, ∀ j : Fin B, π.date j (ftr θ₀ S hS Δ ω) < T →
      (2 : ℝ) ^ (-19 : ℤ) * (S i).card /
        max (π.date j (ftr θ₀ S hS Δ ω) : ℝ) (16 * (S i).card / Δ i ^ 2) ≤
      bsq (S i) (π.head j (ftr θ₀ S hS Δ ω) - targ T θ₀ S hS Δ ω.2.1)) :
    (2 : ℝ) ^ (-24 : ℤ) * blockProgram S Δ (sched π (ftr θ₀ S hS Δ ω)) ≤
      (1 / 2 : ℝ) * ∑ t : Fin T,
        ‖deployed θ₀ π (ftr θ₀ S hS Δ ω) t - targ T θ₀ S hS Δ ω.2.1‖ ^ 2 := by
  set X := ftr θ₀ S hS Δ ω with hX
  set θ := targ T θ₀ S hS Δ ω.2.1 with hθ
  set τ := sched π X with hτdef
  have hτ : IsSchedule T B τ := sched_isSchedule π hπ X
  let g : ℕ → ℝ := fun t => if h : t < T then ‖deployed θ₀ π X ⟨t, h⟩ - θ‖ ^ 2 else 0
  let F : ℕ → ℝ := fun n => (2 : ℝ) ^ (-23 : ℤ) * ∑ i, blockCoeff (S i).card (Δ i) n
  have hphase : ∀ j : Fin (B + 1), ∀ t, τ j.castSucc ≤ t → t < τ j.succ →
      F (τ j.castSucc) ≤ g t := by
    intro j t ht1 ht2
    have hτT : τ j.succ ≤ T := by
      rw [← hτ.2.1]; exact hτ.2.2 (by simp [Fin.le_def]; omega)
    have htT : t < T := lt_of_lt_of_le ht2 hτT
    simp only [g, dif_pos htT]
    rw [← sum_bsq S hS]
    unfold F
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases deployed_phase_gen θ₀ π X τ hτ.1 hτ.2.2
      (fun k => (sched_slot π X k).symm) j ⟨t, htT⟩ ht1 ht2 with ⟨hj0, hdep⟩ | ⟨k, hk, hdep, hdate⟩
    · have hτ0 : τ j.castSucc = 0 := by
        have : j.castSucc = 0 := Fin.ext hj0
        rw [this]; exact hτ.1
      rw [hdep, hτ0]
      have := first_phase_bound T θ₀ S hS Δ hΔ ω.2.1 hH i
      simpa [blockCoeff] using this
    · rw [hdep]
      have hlt : π.date k X < T := by rw [hdate]; omega
      have h1 := hG i k hlt
      rw [hdate] at h1
      exact le_trans (coeff_lower (S i).card (Δ i) (Finset.card_pos.2 (hS.1 i)) (hΔ i) _) h1
  have hsum := phase_sum_lower T B τ hτ g F hphase
  have hgsum : ∑ t ∈ Finset.range T, g t = ∑ t : Fin T,
      ‖deployed θ₀ π X t - θ‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range g T]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [g]
  rw [hgsum] at hsum
  have hprog : (2 : ℝ) ^ (-24 : ℤ) * blockProgram S Δ τ =
      (1 / 2 : ℝ) * ∑ j : Fin (B + 1), phaseLength τ j * F (phaseStart τ j) := by
    unfold blockProgram F
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : (2 : ℝ) ^ (-24 : ℤ) = (1 / 2) * (2 : ℝ) ^ (-23 : ℤ) := by norm_num
    rw [this]; ring
  rw [hprog]
  linarith

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper TRS.Dev.BlockCopy

noncomputable section

namespace TRS.Dev.BlockLower

lemma log16 : Real.log 16 = 4 * Real.log 2 := by
  have : (16 : ℝ) = 2 ^ 4 := by norm_num
  rw [this, Real.log_pow]; norm_num

lemma one_sub_ofReal_le (δ : ℝ) : 1 - ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal δ := by
  rw [tsub_le_iff_right]
  have := ENNReal.ofReal_add_le (p := δ) (q := 1 - δ)
  simp only [add_sub_cancel, ENNReal.ofReal_one] at this
  exact this

lemma good_prob {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {K : ℕ} (E : Fin K → Set α) (hE : ∀ i, MeasurableSet (E i)) (δ : Fin K → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hμ : ∀ i, ENNReal.ofReal (1 - δ i) ≤ μ (E i))
    (hsum : ∑ i, δ i ≤ 1 / 2) :
    ENNReal.ofReal (1 / 2) ≤ μ (⋂ i, E i) := by
  have hc : ∀ i, μ (E i)ᶜ ≤ ENNReal.ofReal (δ i) := by
    intro i
    rw [prob_compl_eq_one_sub (hE i)]
    exact (tsub_le_tsub_left (hμ i) 1).trans (one_sub_ofReal_le _)
  have hG : μ (⋂ i, E i)ᶜ ≤ ENNReal.ofReal (1 / 2) := by
    rw [Set.compl_iInter]
    calc μ (⋃ i, (E i)ᶜ) ≤ ∑ i, μ (E i)ᶜ := measure_iUnion_fintype_le _ _
      _ ≤ ∑ i, ENNReal.ofReal (δ i) := Finset.sum_le_sum (fun i _ => hc i)
      _ = ENNReal.ofReal (∑ i, δ i) := (ENNReal.ofReal_sum_of_nonneg (fun i _ => hδ i)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
  have hmeas : MeasurableSet (⋂ i, E i) := MeasurableSet.iInter hE
  rw [prob_compl_eq_one_sub hmeas] at hG
  have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2) ≤ μ (⋂ i, E i) := by
    rw [tsub_le_iff_right, add_comm]
    exact tsub_le_iff_right.1 hG
  refine le_trans ?_ h1
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper TRS.Dev.BlockCopy

noncomputable section

namespace TRS.Dev.BlockLower

lemma logTwo_eq (x : ℝ) : logTwo x = Real.logb 2 x := rfl

lemma firstLevel_ge4 (c : ℕ) (Δ : ℝ) (hc : 1 ≤ c) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    4 ≤ firstLevel c Δ := by
  unfold firstLevel
  have h16 : (16 : ℝ) ≤ 16 * c / Δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : Δ ^ 2 ≤ 1 := by nlinarith
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
    nlinarith
  have h4 : (4 : ℝ) ≤ logTwo (16 * c / Δ ^ 2) := by
    unfold logTwo
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have := Real.log_le_log (by norm_num) h16
    rw [log16] at this; linarith
  calc (4 : ℤ) = ⌈(4 : ℝ)⌉ := by simp
    _ ≤ _ := Int.ceil_mono h4

lemma nlev_le (T c : ℕ) (Δ : ℝ) (hT8 : 8 ≤ T) (hc : 1 ≤ c) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    (((max (firstLevel c Δ) ⌈Real.logb 2 (T : ℝ)⌉ - firstLevel c Δ + 1 : ℤ)) : ℝ) ≤
      Real.logb 2 (T : ℝ) := by
  have h4 := firstLevel_ge4 c Δ hc hΔ hΔ₁
  have h3 : (3 : ℝ) ≤ Real.logb 2 (T : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num
    exact_mod_cast hT8
  rcases le_total (firstLevel c Δ) ⌈Real.logb 2 (T : ℝ)⌉ with h | h
  · rw [max_eq_right h]
    push_cast
    have h1 : (⌈Real.logb 2 (T : ℝ)⌉ : ℝ) < Real.logb 2 (T : ℝ) + 1 := Int.ceil_lt_add_one _
    have h2 : (4 : ℝ) ≤ (firstLevel c Δ : ℝ) := by exact_mod_cast h4
    linarith
  · rw [max_eq_left h]
    push_cast
    linarith

lemma pow_small (c : ℕ) (M : ℝ) (hM : 1 ≤ M) (h : 1 + logTwo M ≤ c) :
    (9 / 25 : ℝ) ^ c ≤ 1 / (2 * M) := by
  have hM0 : 0 < M := by linarith
  have h1 : (9 / 25 : ℝ) ^ c ≤ (1 / 2 : ℝ) ^ c := pow_le_pow_left₀ (by norm_num) (by norm_num) c
  have h2 : (1 / 2 : ℝ) ^ c = (1 / 2 : ℝ) ^ (c : ℝ) := (Real.rpow_natCast _ _).symm
  have h3 : (1 / 2 : ℝ) ^ (c : ℝ) ≤ (1 / 2 : ℝ) ^ (1 + Real.logb 2 M) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by rw [logTwo_eq] at h; exact h)
  have h4 : (1 / 2 : ℝ) ^ (1 + Real.logb 2 M) = 1 / (2 * M) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, one_div, Real.inv_rpow (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hM0]
    field_simp
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ = _ := h4

lemma union_numeric (T B K : ℕ) {d : ℕ} (S : Fin K → Finset (Fin d))
    (hS : IsBlockPartition S) (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hT8 : 8 ≤ T)
    (hdim : ∀ i, 1 + logTwo (max 1 ((K : ℝ) * B * logTwo T)) ≤ ((S i).card : ℝ)) :
    ∑ i, (B : ℝ) * ((Lof T S Δ i - firstLevel (S i).card (Δ i) + 1 : ℤ) : ℝ) *
      (9 / 25 : ℝ) ^ (S i).card ≤ 1 / 2 := by
  set M : ℝ := max 1 ((K : ℝ) * B * logTwo T) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hKM : (K : ℝ) * B * logTwo T ≤ M := le_max_right _ _
  have hlT : 0 ≤ logTwo T := by
    rw [logTwo_eq]
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ T))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hterm : ∀ i, (B : ℝ) * ((Lof T S Δ i - firstLevel (S i).card (Δ i) + 1 : ℤ) : ℝ) *
      (9 / 25 : ℝ) ^ (S i).card ≤ (B : ℝ) * logTwo T * (1 / (2 * M)) := by
    intro i
    have h1 := nlev_le T (S i).card (Δ i) hT8 (Finset.card_pos.2 (hS.1 i)) (hΔ i) (hΔ₁ i)
    have h2 := pow_small (S i).card M hM1 (hdim i)
    have h0 : 0 ≤ (9 / 25 : ℝ) ^ (S i).card := by positivity
    unfold Lof
    rw [logTwo_eq]
    calc _ ≤ (B : ℝ) * Real.logb 2 (T : ℝ) * (9 / 25 : ℝ) ^ (S i).card := by gcongr
      _ ≤ _ := by gcongr
  calc _ ≤ ∑ _i : Fin K, (B : ℝ) * logTwo T * (1 / (2 * M)) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (K : ℝ) * B * logTwo T / (2 * M) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    _ ≤ M / (2 * M) := by gcongr
    _ = 1 / 2 := by field_simp

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.BlockMoments TRS.Dev.BlockUpper TRS.Dev.BlockCopy

noncomputable section

namespace TRS.Dev.BlockLower

instance instProbFlaw (s : RandomSeed) (T d : ℕ) {K : ℕ} (S : Fin K → Finset (Fin d))
    (Δ : Fin K → ℝ) : IsProbabilityMeasure (flaw s T d S Δ) := by
  unfold flaw; infer_instance

lemma optimum_le (T B : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ)
    (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    blockOptimum T B S Δ ≤ blockProgram S Δ τ := by
  unfold blockOptimum scheduleMin
  exact csInf_le ((schedule_finite T B).image (blockProgram S Δ)).bddBelow
    (Set.mem_image_of_mem _ hτ)

theorem lower_main (T d B K : ℕ) (hT : 0 < T) (hd : 0 < d) (θ₀ : Vector d)
    (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S) (Δ : Fin K → ℝ)
    (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1) (hT8 : 8 ≤ T)
    (hdim : ∀ i, 1 + logTwo (max 1 ((K : ℝ) * B * logTwo T)) ≤ ((S i).card : ℝ)) :
    ENNReal.ofReal ((2 : ℝ) ^ (-25 : ℤ) * blockOptimum T B S Δ) ≤
      blockMinimaxRisk T d B K θ₀ S Δ := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := by
    obtain ⟨i, _⟩ := hS.2.2 ⟨0, hd⟩
    exact ⟨K - 1, by have := i.pos; omega⟩
  unfold blockMinimaxRisk
  apply le_sInf
  rintro v ⟨s, π, hπ, rfl⟩
  -- hidden shifts are small
  have hH : ∀ (u : FDraws T S Δ) i,
      ‖hiddenShift (S i) (Δ i) (Lof T S Δ i) (u i)‖ < Δ i / 32 := by
    intro u i
    have hL : firstLevel (S i).card (Δ i) ≤ Lof T S Δ i := le_max_left _ _
    have hLT : (T : ℝ) ≤ (2 : ℝ) ^ Lof T S Δ i :=
      le_trans (le_zpow_ceil T (by exact_mod_cast hT))
        (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
    exact (common_lower_error_event T d hT hd (S i) (Finset.card_pos.2 (hS.1 i)) (Δ i) (hΔ i)
      (hΔ₁ i) (Lof T S Δ i) hL hLT (fun _ => 0) (blockProjection (S i) 0) (fun _ => rfl)
      s).1 (u i)
  choose E hEm hEμ hEprop using
    fun i => block_event hT hd θ₀ S hS Δ hΔ hΔ₁ π hπ i
  have hδ : ∀ i, 0 ≤ (B : ℝ) * ((Lof T S Δ i - firstLevel (S i).card (Δ i) + 1 : ℤ) : ℝ) *
      (9 / 25 : ℝ) ^ (S i).card := by
    intro i
    have : (0 : ℤ) ≤ Lof T S Δ i - firstLevel (S i).card (Δ i) + 1 := by
      have : firstLevel (S i).card (Δ i) ≤ Lof T S Δ i := le_max_left _ _
      omega
    have h' : (0 : ℝ) ≤ ((Lof T S Δ i - firstLevel (S i).card (Δ i) + 1 : ℤ) : ℝ) := by
      exact_mod_cast this
    positivity
  have hsum := union_numeric T B (m + 1) S hS Δ hΔ hΔ₁ hT8 hdim
  have hGprob := good_prob (flaw s T d S Δ) E hEm _ hδ hEμ hsum
  set G : Set (FSample s T d S Δ) := ⋂ i, E i with hGdef
  have hGm : MeasurableSet G := MeasurableSet.iInter hEm
  have hpath : ∀ ω ∈ G, ENNReal.ofReal ((2 : ℝ) ^ (-24 : ℤ) * blockOptimum T B S Δ) ≤
      pathLoss θ₀ S hS Δ π ω := by
    intro ω hω
    have hωi : ∀ i, ω ∈ E i := fun i => Set.mem_iInter.1 hω i
    have h1 := pointwise_lower θ₀ S hS Δ hΔ π hπ ω (fun i => hH ω.2.1 i)
      (fun i j hj => (hEprop i ω (hωi i)) j hj)
    have h2 := optimum_le T B S Δ _ (sched_isSchedule π hπ (ftr θ₀ S hS Δ ω))
    unfold pathLoss
    apply ENNReal.ofReal_le_ofReal
    have h3 : (2 : ℝ) ^ (-24 : ℤ) * blockOptimum T B S Δ ≤
        (2 : ℝ) ^ (-24 : ℤ) * blockProgram S Δ (sched π (ftr θ₀ S hS Δ ω)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hprior := prior_le_worst θ₀ S hS Δ hΔ π hH
  refine le_trans ?_ hprior
  calc ENNReal.ofReal ((2 : ℝ) ^ (-25 : ℤ) * blockOptimum T B S Δ)
      = ENNReal.ofReal (1 / 2) *
        ENNReal.ofReal ((2 : ℝ) ^ (-24 : ℤ) * blockOptimum T B S Δ) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; norm_num; ring
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-24 : ℤ) * blockOptimum T B S Δ) * flaw s T d S Δ G := by
        rw [mul_comm]; gcongr
    _ = ∫⁻ ω, G.indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-24 : ℤ) * blockOptimum T B S Δ)) ω
          ∂(flaw s T d S Δ) := (lintegral_indicator_const hGm _).symm
    _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ G
        · rw [Set.indicator_of_mem hω]; exact hpath ω hω
        · rw [Set.indicator_of_notMem hω]; exact zero_le

end TRS.Dev.BlockLower
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary
open TightReleaseSchedules.Stationary.Supplement

/-
Explicit-constant plan for clause (c) (carried out in BlockLower1 .. BlockLower11).

Prior: theta(u) = theta0 + sum_i embed_i(a_i + H_i(u_i)), a_i = (Delta_i/2) e_{s_i}, H_i the
Lemma 4.2 prior of block i (levels l0(i) .. L_i, L_i = max(l0(i), ceil log2 T)), blocks independent.
* every theta(u) is in the block class (norm of block i <= Delta_i/2 + Delta_i/32 <= Delta_i), so
  (prior average of the loss) <= blockWorstRisk                                  [prior_le_worst].
* per block i, an event E_i with Pr(E_i^c) <= B * (#levels_i) * (9/25)^{d_i}: the sibling lemma
  `common_lower_error_event` is applied with the seed enlarged by the other blocks' hidden draws
  (the policy is run on the label-shifted transcript, which stays causal)       [block_event].
* #levels_i <= log2 T (l0 >= 4, T >= 8) and (9/25)^{d_i} <= 2^{-d_i} <= 1/(2M),
  M = max{1, K B log2 T}, so sum_i Pr(E_i^c) <= K B log2 T / (2M) <= 1/2         [union_numeric].
* on G = cap E_i, for the realized schedule tau (dates of the policy) and every round t in phase j,
  sum_i |P_i(w_t - theta)|^2 >= 2^-19 sum_i d_i / max{tau_j, 16 d_i/Delta_i^2}
  >= 2^-23 sum_i min{d_i/tau_j, Delta_i^2}  (and >= 2^-23 sum_i Delta_i^2 in phase 0, since
  (15/32)^2 >= 1/8), hence half squared loss >= 2^-24 E(tau) >= 2^-24 E*_B    [pointwise_lower].
* risk >= Pr(G) 2^-24 E*_B >= 2^-25 E*_B.                                        [lower_main].
-/

open TRS.Dev.BlockUpper TRS.Dev.BlockLower in
theorem TRS.chk_block_structured_stationary_shift (T d B K : ℕ) (hT : 0 < T) (hd : 0 < d)
    (S : Fin K → Finset (Fin d)) (hS : IsBlockPartition S)
    (Δ : Fin K → ℝ) (hΔ : ∀ i, 0 < Δ i) (hΔ₁ : ∀ i, Δ i ≤ 1)
    (hΔsum : ∑ i, Δ i ^ 2 ≤ 1) (θ₀ : Vector d) :
    blockMinimaxRisk T d B K θ₀ S Δ ≤ ENNReal.ofReal (2 * blockOptimum T B S Δ) ∧
    (∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ → blockProgram S Δ τ = blockOptimum T B S Δ →
      IsCausal (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      HasDeterministicDates (blockGridPolicy T d B K θ₀ S Δ τ) ∧
      blockWorstRisk θ₀ S Δ (blockGridPolicy T d B K θ₀ S Δ τ) ≤
        ENNReal.ofReal (2 * blockOptimum T B S Δ)) ∧
    (8 ≤ T →
      (∀ i, 1 + logTwo (max 1 ((K : ℝ) * B * logTwo T)) ≤ ((S i).card : ℝ)) →
      ENNReal.ofReal ((2 : ℝ) ^ (-25 : ℤ) * blockOptimum T B S Δ) ≤
        blockMinimaxRisk T d B K θ₀ S Δ) := by
  obtain ⟨h1, h2⟩ := upper_parts T d B K hT θ₀ S hS Δ hΔ hΔ₁ hΔsum
  exact ⟨h1, h2, fun hT8 hdim => lower_main T d B K hT hd θ₀ S hS Δ hΔ hΔ₁ hT8 hdim⟩
end

theorem solution : type_of% @TRS.chk_block_structured_stationary_shift := @TRS.chk_block_structured_stationary_shift
