-- Prove2me | solution 1 for SuttonBartoRL.PolicyGradient.softmax_eligibility
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:43:12.041133+00:00
-- url     : https://prove2.me/submissions/5e9fb9ae-41bf-477c-95c7-295c4b3864f8

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_SoftmaxPolicy

set_option autoImplicit false

open SuttonBartoRL.PolicyGradient in
theorem solution {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (x : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    HasGradientAt (fun θ' => Real.log (softmaxPolicy (linearPref x) θ' s a))
      (x s a - ∑ b, softmaxPolicy (linearPref x) θ s b • x s b) θ := by
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun θ' => ∑ b, Real.exp (inner ℝ θ' (x s b)) with hG
  have hGpos : ∀ θ', 0 < G θ' := fun θ' =>
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hfun : (fun θ' => Real.log (softmaxPolicy (linearPref x) θ' s a)) =
      fun θ' => inner ℝ θ' (x s a) - Real.log (G θ') := by
    funext θ'
    simp only [softmaxPolicy, linearPref]
    rw [Real.log_div (Real.exp_pos _).ne' (hGpos θ').ne', Real.log_exp]
  have hlin : ∀ v : EuclideanSpace ℝ (Fin d),
      HasFDerivAt (fun θ' : EuclideanSpace ℝ (Fin d) => inner ℝ θ' v) (innerSL ℝ v) θ := by
    intro v
    have := (innerSL ℝ v).hasFDerivAt (x := θ)
    convert this using 1
    funext θ'
    simp [real_inner_comm]
  have hGd : HasFDerivAt G (∑ b, Real.exp (inner ℝ θ (x s b)) • innerSL ℝ (x s b)) θ :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hlin (x s b)).exp)
  have hL := (hlin (x s a)).sub (hGd.log (hGpos θ).ne')
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hL.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
  · simpa using congrFun hfun y
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, inner_sub_left, sum_inner, real_inner_smul_left,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    innerSL_apply_apply, smul_eq_mul, softmaxPolicy, linearPref, Finset.mul_sum, hG]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
