-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.anchored_cross_moments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:34:50.924178+00:00
-- url     : https://prove2.me/submissions/7b078a6d-73f3-48fe-89ba-c2d3cda06dc5

import Definitions.Def_TightReleaseSchedules_Stationary_gaussian_experiment

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open TightReleaseSchedules.Stationary

namespace TRS.Dev.AnchoredCrossMoments

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

lemma trace_le (hβ : ‖θ i - θ₀‖ ≤ 1) :
    (∑ k : Fin d, crossCovariance θ₀ θ i k k) ≤ 2 * (d : ℝ) + 1 := by
  simp only [cross_cov, if_true, ← sq]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have h1 : ∑ k : Fin d, (θ i - θ₀) k ^ 2 = ‖θ i - θ₀‖ ^ 2 := (norm_sq_sum _).symm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, h1]
  have h2 : ‖θ i - θ₀‖ ^ 2 ≤ 1 := by
    have := norm_nonneg (θ i - θ₀)
    nlinarith
  have h3 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

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

lemma avg_sub_sq (I : Finset (Fin T)) (z : GaussianRows T d) :
    ‖anchoredAverage θ₀ I (observations θ z) - pathAverage (fun i => θ i - θ₀) I‖ ^ 2 =
      ((I.card : ℝ)⁻¹) ^ 2 * ∑ k : Fin d, (∑ m ∈ I, Dk θ₀ θ m k z) ^ 2 := by
  rw [norm_sq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [anchoredAverage, pathAverage, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply, Dk, Finset.sum_sub_distrib]
  ring

lemma avg_second_moment (I : Finset (Fin T)) (hI : I.Nonempty)
    (hβ : ∀ i, ‖θ i - θ₀‖ ≤ 1) :
    Integrable (fun z => ‖anchoredAverage θ₀ I (observations θ z) -
        pathAverage (fun i => θ i - θ₀) I‖ ^ 2) (gaussianRows T d) ∧
    ∫ z, ‖anchoredAverage θ₀ I (observations θ z) - pathAverage (fun i => θ i - θ₀) I‖ ^ 2
        ∂(gaussianRows T d) ≤ (2 * (d : ℝ) + 1) / I.card := by
  have hfun : (fun z => ‖anchoredAverage θ₀ I (observations θ z) -
        pathAverage (fun i => θ i - θ₀) I‖ ^ 2) =
      fun z => ((I.card : ℝ)⁻¹) ^ 2 * ∑ k : Fin d, (∑ m ∈ I, Dk θ₀ θ m k z) ^ 2 :=
    funext (avg_sub_sq θ₀ θ I)
  have hc : (0:ℝ) < I.card := by exact_mod_cast hI.card_pos
  rw [hfun]
  refine ⟨(integrable_finsetSum _ (fun k _ => sum_sq_integrable θ₀ θ I k)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => sum_sq_integrable θ₀ θ I k)]
  simp_rw [sum_second_moment θ₀ θ I]
  rw [Finset.sum_comm]
  have h1 : ∑ m ∈ I, ∑ k : Fin d, crossCovariance θ₀ θ m k k ≤ ∑ m ∈ I, (2 * (d : ℝ) + 1) :=
    Finset.sum_le_sum (fun m _ => trace_le θ₀ θ m (hβ m))
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((I.card : ℝ)⁻¹) ^ 2 * (I.card * (2 * (d:ℝ) + 1)) = (2 * (d : ℝ) + 1) / I.card := by
    field_simp
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end Row

lemma proj_facts {d : ℕ} (K : Set (Vector d)) (hK : IsClosed K) (hc : Convex ℝ K) (p : Vector d)
    (hp : p ∈ K) (x : Vector d) :
    convexProjection K x ∈ K ∧ ‖convexProjection K x - p‖ ≤ ‖x - p‖ := by
  have hne : K.Nonempty ∧ IsClosed K ∧ Convex ℝ K := ⟨⟨p, hp⟩, hK, hc⟩
  have hspec := Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne.1 hne.2.1.isComplete hne.2.2 x)
  have hdef : convexProjection K x = Classical.choose
      (exists_norm_eq_iInf_of_complete_convex hne.1 hne.2.1.isComplete hne.2.2 x) := by
    unfold convexProjection
    rw [dif_pos hne]
  rw [hdef]
  obtain ⟨hv, heq⟩ := hspec
  set v := Classical.choose
      (exists_norm_eq_iInf_of_complete_convex hne.1 hne.2.1.isComplete hne.2.2 x) with hvdef
  refine ⟨hv, ?_⟩
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hc hv).1 heq p hp
  have h1 : x - p = (x - v) + (v - p) := by abel
  have h2 : ‖x - p‖ ^ 2 = ‖x - v‖ ^ 2 + 2 * inner ℝ (x - v) (v - p) + ‖v - p‖ ^ 2 := by
    rw [h1]
    exact norm_add_sq_real _ _
  have h3 : inner ℝ (x - v) (v - p) = - inner ℝ (x - v) (p - v) := by
    rw [← inner_neg_right]
    congr 1
    abel
  have h4 : ‖v - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
    nlinarith [sq_nonneg ‖x - v‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h4

end TRS.Dev.AnchoredCrossMoments

open TRS.Dev.AnchoredCrossMoments in
theorem TRS.chk_anchored_cross_moments (T d : ℕ) (hT : 0 < T) (hd : 0 < d)
    (θ₀ : Vector d) (θ : Fin T → Vector d) (hβ : ∀ i, ‖θ i - θ₀‖ ≤ 1) :
    (∀ i,
      Integrable (fun z => crossMoment θ₀ (observations θ z i)) (gaussianRows T d) ∧
      Integrable (fun z => ‖crossMoment θ₀ (observations θ z i)‖ ^ 2) (gaussianRows T d) ∧
      (∫ z, crossMoment θ₀ (observations θ z i) ∂(gaussianRows T d)) = θ i - θ₀ ∧
      (∀ k l, crossCovariance θ₀ θ i k l =
        (1 + ‖θ i - θ₀‖ ^ 2) * (if k = l then 1 else 0) +
          (θ i - θ₀) k * (θ i - θ₀) l) ∧
      (∑ k : Fin d, crossCovariance θ₀ θ i k k) ≤ 2 * (d : ℝ) + 1) ∧
    (∀ (I : Finset (Fin T)), I.Nonempty → ∀ K : Set (Vector d),
      IsClosed K → Convex ℝ K → pathAverage (fun i => θ i - θ₀) I ∈ K →
      (∫⁻ z, ENNReal.ofReal
        (‖convexProjection K (anchoredAverage θ₀ I (observations θ z)) -
          pathAverage (fun i => θ i - θ₀) I‖ ^ 2) ∂(gaussianRows T d)) ≤
        min (ENNReal.ofReal ((2 * (d : ℝ) + 1) / I.card)) (Metric.ediam K ^ 2)) := by
  refine ⟨fun i => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact integrable_piLp_iff.2 (fun k => cross_integrable_coord θ₀ θ i k)
  · have : (fun z => ‖crossMoment θ₀ (observations θ z i)‖ ^ 2) =
        fun z => ∑ k : Fin d, crossMoment θ₀ (observations θ z i) k *
          crossMoment θ₀ (observations θ z i) k := by
      ext z; rw [norm_sq_sum]; simp [sq]
    rw [this]
    exact integrable_finsetSum _ (fun k _ => cross_integrable_mul θ₀ θ i k k)
  · ext k
    rw [eval_integral_piLp (fun k => cross_integrable_coord θ₀ θ i k) k]
    exact cross_integral_coord θ₀ θ i k
  · exact cross_cov θ₀ θ i
  · exact trace_le θ₀ θ i (hβ i)
  · intro I hI K hK hc hp
    obtain ⟨hint, hbound⟩ := avg_second_moment θ₀ θ I hI hβ
    refine le_min ?_ ?_
    · calc (∫⁻ z, ENNReal.ofReal
            (‖convexProjection K (anchoredAverage θ₀ I (observations θ z)) -
              pathAverage (fun i => θ i - θ₀) I‖ ^ 2) ∂(gaussianRows T d))
          ≤ ∫⁻ z, ENNReal.ofReal (‖anchoredAverage θ₀ I (observations θ z) -
              pathAverage (fun i => θ i - θ₀) I‖ ^ 2) ∂(gaussianRows T d) := by
            refine lintegral_mono (fun z => ENNReal.ofReal_le_ofReal ?_)
            exact pow_le_pow_left₀ (norm_nonneg _) (proj_facts K hK hc _ hp _).2 2
        _ = ENNReal.ofReal (∫ z, ‖anchoredAverage θ₀ I (observations θ z) -
              pathAverage (fun i => θ i - θ₀) I‖ ^ 2 ∂(gaussianRows T d)) :=
            (ofReal_integral_eq_lintegral_ofReal hint
              (Filter.Eventually.of_forall (fun z => by positivity))).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hbound
    · calc (∫⁻ z, ENNReal.ofReal
            (‖convexProjection K (anchoredAverage θ₀ I (observations θ z)) -
              pathAverage (fun i => θ i - θ₀) I‖ ^ 2) ∂(gaussianRows T d))
          ≤ ∫⁻ z, Metric.ediam K ^ 2 ∂(gaussianRows T d) := by
            refine lintegral_mono (fun z => ?_)
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ← edist_eq_enorm_sub]
            exact pow_le_pow_left' (Metric.edist_le_ediam_of_mem
              (proj_facts K hK hc _ hp _).1 hp) 2
        _ = Metric.ediam K ^ 2 := by simp
end

theorem solution : type_of% @TRS.chk_anchored_cross_moments := @TRS.chk_anchored_cross_moments
