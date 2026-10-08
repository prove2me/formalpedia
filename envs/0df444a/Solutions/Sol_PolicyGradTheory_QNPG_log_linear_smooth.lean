-- Prove2me | solution 1 for PolicyGradTheory.QNPG.log_linear_smooth
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:55:31.386998+00:00
-- url     : https://prove2.me/submissions/99baa38d-cacd-4522-b6a4-f5005db09721

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting



namespace PolicyGradTheory.QNPG

section LL
variable {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}

lemma qn_Z_pos (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) :
    0 < ∑ b, Real.exp (inner ℝ θ (φ s b)) :=
  Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty

lemma qn_ll_eq (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    logLinearPolicy φ θ s a = Real.exp (inner ℝ θ (φ s a)) / ∑ b, Real.exp (inner ℝ θ (φ s b)) := rfl

lemma qn_ll_pos (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    0 < logLinearPolicy φ θ s a := by
  rw [qn_ll_eq]; exact div_pos (Real.exp_pos _) (qn_Z_pos φ θ s)

lemma qn_ll_sum (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) :
    ∑ a, logLinearPolicy φ θ s a = 1 := by
  simp only [qn_ll_eq, ← Finset.sum_div]
  exact div_self (qn_Z_pos φ θ s).ne'

/-- mean feature -/
noncomputable def qnMean (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (s : S) : EuclideanSpace ℝ (Fin d) :=
  ∑ b, logLinearPolicy φ θ s b • φ s b

lemma qn_inner_hasFDeriv (v θ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ x v) (innerSL ℝ v) θ := by
  have := (innerSL ℝ v).hasFDerivAt (x := θ)
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp [real_inner_comm]

lemma qn_ll_hasGrad (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (s : S) (a : A) :
    HasGradientAt (fun x => Real.log (logLinearPolicy φ x s a)) (φ s a - qnMean φ θ s) θ := by
  have heq : (fun x => Real.log (logLinearPolicy φ x s a)) =
      fun x => inner ℝ x (φ s a) - Real.log (∑ b, Real.exp (inner ℝ x (φ s b))) := by
    funext x
    rw [qn_ll_eq, Real.log_div (Real.exp_pos _).ne' (qn_Z_pos φ x s).ne', Real.log_exp]
  rw [heq, hasGradientAt_iff_hasFDerivAt]
  have hZ := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun b _ => (qn_inner_hasFDeriv (φ s b) θ).exp)
  have h := HasFDerivAt.fun_sub (qn_inner_hasFDeriv (φ s a) θ) (hZ.log (qn_Z_pos φ θ s).ne')
  refine h.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, qnMean, inner_sub_left,
    sum_inner, inner_smul_left, qn_ll_eq]
  simp only [Finset.sum_fn, conj_trivial]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  field_simp

lemma qn_ll_grad (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (s : S) (a : A) :
    gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ = φ s a - qnMean φ θ s :=
  (qn_ll_hasGrad φ θ s a).gradient

lemma qn_cov_bound {A : Type} [Fintype A] (p e y : A → ℝ) (hp : ∀ b, 0 ≤ p b) (hs : ∑ b, p b = 1)
    (E0 Y0 : ℝ) (hE : 0 ≤ E0) (hY : 0 ≤ Y0) (he : ∀ b, |e b| ≤ E0) (hy : ∀ b, |y b| ≤ Y0) :
    ∑ b, p b * e b * y b - (∑ b, p b * e b) * (∑ b, p b * y b) ≤ E0 * Y0 := by
  set me := ∑ b, p b * e b with hme
  set my := ∑ b, p b * y b with hmy
  have hcov : ∑ b, p b * e b * y b - me * my =
      ∑ b, Real.sqrt (p b) * (e b - me) * (Real.sqrt (p b) * (y b - my)) := by
    have : ∀ b, Real.sqrt (p b) * (e b - me) * (Real.sqrt (p b) * (y b - my)) =
        p b * e b * y b - my * (p b * e b) - me * (p b * y b) + me * my * p b := by
      intro b
      have := Real.mul_self_sqrt (hp b)
      linear_combination (e b - me) * (y b - my) * this
    simp_rw [this]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, ← hme, ← hmy]
    ring
  have hvar : ∀ (u : A → ℝ) (U : ℝ), (∀ b, |u b| ≤ U) →
      ∑ b, (Real.sqrt (p b) * (u b - ∑ c, p c * u c)) ^ 2 ≤ U ^ 2 := by
    intro u U hu
    set m := ∑ c, p c * u c with hm
    have h1 : ∀ b, (Real.sqrt (p b) * (u b - m)) ^ 2 = p b * u b ^ 2 - 2 * m * (p b * u b) + m ^ 2 * p b := by
      intro b
      rw [mul_pow, Real.sq_sqrt (hp b)]; ring
    simp_rw [h1]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, ← hm]
    have h2 : ∑ b, p b * u b ^ 2 ≤ ∑ b, p b * U ^ 2 := by
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hp b)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hu b) 2
    rw [← Finset.sum_mul, hs] at h2
    nlinarith [sq_nonneg m]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => Real.sqrt (p b) * (e b - me)) (fun b => Real.sqrt (p b) * (y b - my))
  have hv1 := hvar e E0 he
  have hv2 := hvar y Y0 hy
  rw [← hcov] at hcs
  have hsq : (∑ b, p b * e b * y b - me * my) ^ 2 ≤ (E0 * Y0) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ E0 ^ 2 * Y0 ^ 2 := mul_le_mul hv1 hv2 (Finset.sum_nonneg fun b _ => sq_nonneg _)
          (sq_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ E0 * Y0 := mul_nonneg hE hY
  by_contra hc
  push_neg at hc
  nlinarith

lemma qn_mvt_cov {A : Type} [Fintype A] [Nonempty A] (c e y : A → ℝ) (E0 Y0 : ℝ)
    (hE : 0 ≤ E0) (hY : 0 ≤ Y0) (he : ∀ b, |e b| ≤ E0) (hy : ∀ b, |y b| ≤ Y0) :
    (∑ b, Real.exp (c b + e b) * y b) / (∑ b, Real.exp (c b + e b)) -
      (∑ b, Real.exp (c b) * y b) / (∑ b, Real.exp (c b)) ≤ E0 * Y0 := by
  let N : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b) * y b
  let Z : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b)
  let N' : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b) * e b * y b
  let Z' : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b) * e b
  have hZpos : ∀ t, 0 < Z t := fun t =>
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hexp : ∀ b t, HasDerivAt (fun t => Real.exp (c b + t * e b))
      (Real.exp (c b + t * e b) * e b) t := by
    intro b t
    have h1 : HasDerivAt (fun t => c b + t * e b) (e b) t := by
      simpa using ((hasDerivAt_id t).mul_const (e b)).const_add (c b)
    exact h1.exp
  have hN : ∀ t, HasDerivAt N (N' t) t := by
    intro t
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hexp b t).mul_const (y b))
    simpa [N, N'] using this
  have hZ : ∀ t, HasDerivAt Z (Z' t) t := by
    intro t
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => hexp b t)
    simpa [Z, Z'] using this
  have hF : ∀ t, HasDerivAt (fun t => N t / Z t)
      ((N' t * Z t - N t * Z' t) / Z t ^ 2) t := fun t =>
    (hN t).div (hZ t) (hZpos t).ne'
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope (fun t => N t / Z t)
    (fun t => (N' t * Z t - N t * Z' t) / Z t ^ 2) (zero_lt_one' ℝ)
    (fun t _ => (hF t).continuousAt.continuousWithinAt) (fun t _ => hF t)
  have hgoal : (∑ b, Real.exp (c b + e b) * y b) / (∑ b, Real.exp (c b + e b)) -
      (∑ b, Real.exp (c b) * y b) / (∑ b, Real.exp (c b)) = N 1 / Z 1 - N 0 / Z 0 := by
    simp [N, Z]
  rw [hgoal, show N 1 / Z 1 - N 0 / Z 0 = (N 1 / Z 1 - N 0 / Z 0) / (1 - 0) by norm_num, ← hξ]
  set p : A → ℝ := fun b => Real.exp (c b + ξ * e b) / Z ξ with hpdef
  have hp : ∀ b, 0 ≤ p b := fun b => div_nonneg (Real.exp_pos _).le (hZpos ξ).le
  have hs : ∑ b, p b = 1 := by
    simp only [hpdef, ← Finset.sum_div]; exact div_self (hZpos ξ).ne'
  have key := qn_cov_bound p e y hp hs E0 Y0 hE hY he hy
  have hZne := (hZpos ξ).ne'
  have e1 : ∑ b, p b * e b * y b = N' ξ / Z ξ := by
    simp only [hpdef, N', Finset.sum_div]; congr 1; ext b; field_simp
  have e2 : ∑ b, p b * e b = Z' ξ / Z ξ := by
    simp only [hpdef, Z', Finset.sum_div]; congr 1; ext b; field_simp
  have e3 : ∑ b, p b * y b = N ξ / Z ξ := by
    simp only [hpdef, N, Finset.sum_div]; congr 1; ext b; field_simp
  rw [e1, e2, e3] at key
  have : (N' ξ * Z ξ - N ξ * Z' ξ) / Z ξ ^ 2 = N' ξ / Z ξ - Z' ξ / Z ξ * (N ξ / Z ξ) := by
    field_simp
  rw [this]; exact key

theorem log_linear_smooth_core {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (hφ : ∀ s a, ‖φ s a‖ ≤ B) (s : S) (a : A) :
    ∀ θ θ' : EuclideanSpace ℝ (Fin d),
      ‖gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ -
        gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ'‖ ≤
        B ^ 2 * ‖θ - θ'‖ := by
  intro θ θ'
  have hB : 0 ≤ B := (norm_nonneg _).trans (hφ s a)
  rw [qn_ll_grad, qn_ll_grad, sub_sub_sub_cancel_left]
  set x := qnMean φ θ' s - qnMean φ θ s with hx
  set v := θ' - θ with hv
  have hmean : ∀ ϑ : EuclideanSpace ℝ (Fin d), inner ℝ (qnMean φ ϑ s) x =
      (∑ b, Real.exp (inner ℝ ϑ (φ s b)) * inner ℝ (φ s b) x) /
        ∑ b, Real.exp (inner ℝ ϑ (φ s b)) := by
    intro ϑ
    simp only [qnMean, sum_inner, inner_smul_left, conj_trivial, qn_ll_eq, Finset.sum_div]
    congr 1; ext b; ring
  have hxx : ‖x‖ ^ 2 = inner ℝ (qnMean φ θ' s) x - inner ℝ (qnMean φ θ s) x := by
    rw [← inner_sub_left, ← hx, real_inner_self_eq_norm_sq]
  have h1 : ∀ b, inner ℝ θ' (φ s b) = inner ℝ θ (φ s b) + inner ℝ v (φ s b) := by
    intro b; rw [← inner_add_left, hv, add_sub_cancel]
  rw [hmean, hmean] at hxx
  simp_rw [h1] at hxx
  have key := qn_mvt_cov (fun b => inner ℝ θ (φ s b)) (fun b => inner ℝ v (φ s b))
    (fun b => inner ℝ (φ s b) x) (‖v‖ * B) (B * ‖x‖) (mul_nonneg (norm_nonneg _) hB)
    (mul_nonneg hB (norm_nonneg _))
    (fun b => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hφ s b) (norm_nonneg _)))
    (fun b => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hφ s b) (norm_nonneg _)))
  rw [← hxx] at key
  rw [norm_sub_rev θ θ', ← hv]
  rcases (norm_nonneg x).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

end LL

end PolicyGradTheory.QNPG

open PolicyGradTheory.QNPG


theorem solution {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (hφ : ∀ s a, ‖φ s a‖ ≤ B) (s : S) (a : A) :
    ∀ θ θ' : EuclideanSpace ℝ (Fin d),
      ‖gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ -
        gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ'‖ ≤
        B ^ 2 * ‖θ - θ'‖ := by
  exact log_linear_smooth_core φ B hφ s a
