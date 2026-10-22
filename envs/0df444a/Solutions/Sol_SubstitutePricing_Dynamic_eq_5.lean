-- Prove2me | solution 1 for SubstitutePricing.Dynamic.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:19.356236+00:00
-- url     : https://prove2.me/submissions/66e28f16-19d9-49aa-a875-e7d16db52637

import Mathlib
import Definitions.Def_SubstitutePricing_Dynamic_Model
set_option autoImplicit false
open SubstitutePricing.Dynamic

theorem solution (M : Model) (hM : M.Assumptions)
    (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.obj V x r = M.xi V x r + V x := by
  have hD : 0 < M.den x r := by
    unfold Model.den
    have : 0 ≤ ∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ) :=
      Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
    have := Real.exp_pos (M.u0 / M.μ)
    linarith
  have hsum : ∑ i ∈ M.S x, M.P x r i + M.P0 x r = 1 := by
    have h1 : ∑ i ∈ M.S x, M.P x r i = (∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ)) / M.den x r := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Model.P, hi]
    rw [h1]
    unfold Model.P0
    rw [← add_div]
    exact div_self hD.ne'
  have hxi : M.xi V x r = M.lam * (∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i)))) := by
    unfold Model.xi ChoiceCDLP.MNL.mnlObjective
    have hden : (∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ)) + Real.exp (M.u0 / M.μ) = M.den x r := rfl
    rw [hden, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Model.P, hi, if_true]
    ring
  rw [hxi]
  unfold Model.obj
  have e1 : ∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i)))
      = ∑ i ∈ M.S x, r i * M.P x r i + ∑ i ∈ M.S x, M.P x r i * V (M.sell x i)
        - (∑ i ∈ M.S x, M.P x r i) * V x := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e1]
  have : M.P0 x r = 1 - ∑ i ∈ M.S x, M.P x r i := by linarith
  rw [this]
  ring
