-- Prove2me | solution 1 for SubstitutePricing.Unified.eq_25_26
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:33:00.824894+00:00
-- url     : https://prove2.me/submissions/c234580f-b690-42f5-864c-919247281a75

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

open SubstitutePricing.Unified
open scoped BigOperators

private theorem den_pos (M : Model) (x : Fin M.n → ℕ) (r : ℝ) :
    0 < M.den x (M.const r) := by
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)) (Real.exp_pos _)

private theorem exp_deriv (M : Model) (i : Fin M.n) (r : ℝ) :
    HasDerivAt (fun u => Real.exp ((M.a i - u) / M.μ))
      (-(Real.exp ((M.a i - r) / M.μ)) / M.μ) r := by
  convert! (((hasDerivAt_const r (M.a i)).sub (hasDerivAt_id r)).div_const M.μ).exp using 1 <;> simp <;> ring

private theorem den_deriv (M : Model) (x : Fin M.n → ℕ) (r : ℝ) :
    HasDerivAt (fun u => M.den x (M.const u))
      (-(∑ i ∈ M.S x, Real.exp ((M.a i - r) / M.μ)) / M.μ) r := by
  convert! (HasDerivAt.fun_sum (fun i (_ : i ∈ M.S x) => exp_deriv M i r)).add_const (Real.exp (M.u0 / M.μ)) using 1
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

private theorem prob_deriv (M : Model) (x : Fin M.n → ℕ) (i : Fin M.n)
    (hi : i ∈ M.S x) (r : ℝ) :
    HasDerivAt (fun u => M.P x (M.const u) i)
      (-M.P x (M.const r) i * M.P0 x (M.const r) / M.μ) r := by
  have h := (exp_deriv M i r).div (den_deriv M x r) (den_pos M x r).ne'
  convert! h using 1
  · ext u
    simp [Model.P, hi, Model.const]
  · simp only [Model.P, if_pos hi, Model.P0, Model.den, Model.const]
    field_simp
    <;> ring

theorem solution (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ) (hx : (M.S x).Nonempty)
    (δ : Fin M.n → ℝ) (r : ℝ) (hr : HasDerivAt (M.xiS x δ) 0 r) :
    M.P0 x (M.const r) = 1 / (M.xiS x δ r / (M.lam * M.μ) + 1) ∧
    M.xiS x δ r = M.lam * M.μ * (1 / M.P0 x (M.const r) - 1) ∧
    0 < M.xiS x δ r ∧
    0 < M.P0 x (M.const r) ∧ M.P0 x (M.const r) < 1 := by
  classical
  have hp : 0 < M.P0 x (M.const r) := div_pos (Real.exp_pos _) (den_pos M x r)
  have hsum : 0 < ∑ i ∈ M.S x, Real.exp ((M.a i - r) / M.μ) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hx
  have hp1 : M.P0 x (M.const r) < 1 := by
    rw [Model.P0, div_lt_one (den_pos M x r)]
    change Real.exp (M.u0 / M.μ) < _ + Real.exp (M.u0 / M.μ)
    simp only [Model.const]
    linarith
  have hs : ∑ i ∈ M.S x, M.P x (M.const r) i = 1 - M.P0 x (M.const r) := by
    simp only [Model.P, Model.P0]
    rw [Finset.sum_congr rfl (fun i hi => if_pos hi), ← Finset.sum_div]
    unfold Model.den
    field_simp
    <;> ring
  have hd := HasDerivAt.fun_sum (fun i (hi : i ∈ M.S x) =>
    ((prob_deriv M x i hi r).const_mul M.lam).mul ((hasDerivAt_id r).sub_const (δ i)))
  have hz : M.lam * (1 - M.P0 x (M.const r)) -
      M.P0 x (M.const r) / M.μ * M.xiS x δ r = 0 := by
    have hh : (∑ i ∈ M.S x,
      (M.lam * (-M.P x (M.const r) i * M.P0 x (M.const r) / M.μ) * (r - δ i) +
      M.lam * M.P x (M.const r) i * 1)) = 0 := by
      exact hd.unique hr
    rw [← hs, Model.xiS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hm := hM.mu_pos
  have hl := hM.lam_pos
  have he : M.P0 x (M.const r) * M.xiS x δ r =
      M.lam * M.μ * (1 - M.P0 x (M.const r)) := by
    have hh := congrArg (fun z : ℝ => z * M.μ) hz
    field_simp [hm.ne'] at hh
    nlinarith
  have hxi : 0 < M.xiS x δ r := by
    have hright : 0 < M.lam * M.μ * (1 - M.P0 x (M.const r)) :=
      mul_pos (mul_pos hl hm) (sub_pos.mpr hp1)
    nlinarith
  refine ⟨?_, ?_, hxi, hp, hp1⟩
  · have hdpos : 0 < M.xiS x δ r / (M.lam * M.μ) + 1 :=
      add_pos (div_pos hxi (mul_pos hl hm)) zero_lt_one
    apply (eq_div_iff hdpos.ne').mpr
    field_simp [hl.ne', hm.ne']
    nlinarith [he]
  · field_simp [hp.ne']
    nlinarith [he]

#print axioms solution
