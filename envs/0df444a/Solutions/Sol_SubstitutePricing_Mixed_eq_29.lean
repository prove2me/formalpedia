-- Prove2me | solution 1 for SubstitutePricing.Mixed.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:55.278039+00:00
-- url     : https://prove2.me/submissions/a60c9de3-5703-4b85-a5a1-8fc50ac912ba

import Mathlib
import Definitions.Def_SubstitutePricing_Mixed_Model

set_option autoImplicit false
open SubstitutePricing.Mixed

theorem solution (M : Model) (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ)
    (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.objM V x r = M.xiM V x r + V x := by
  have he0pos : 0 < Real.exp (M.u0 / M.μ) := Real.exp_pos _
  have hdenpos : 0 < M.den x (M.mix r) := by
    unfold Model.den
    have h2 : 0 ≤ ∑ j ∈ M.S x, Real.exp ((M.a j - M.mix r j) / M.μ) :=
      Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    linarith
  have hsumP : ∑ i ∈ M.S x, M.P x (M.mix r) i + M.P0 x (M.mix r) = 1 := by
    have h1 : ∑ i ∈ M.S x, M.P x (M.mix r) i =
        (∑ j ∈ M.S x, Real.exp ((M.a j - M.mix r j) / M.μ)) / M.den x (M.mix r) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      unfold Model.P; rw [if_pos hi]
    rw [h1]; unfold Model.P0
    rw [← add_div]
    have : M.den x (M.mix r) =
        (∑ j ∈ M.S x, Real.exp ((M.a j - M.mix r j) / M.μ)) + Real.exp (M.u0 / M.μ) := rfl
    rw [← this]; exact div_self hdenpos.ne'
  have hxi : M.xiM V x r = ∑ i ∈ M.S x, M.lam * M.P x (M.mix r) i *
      (M.mix r i - (V x - V (M.sell x i))) := by
    unfold Model.xiM Model.xiD
    rw [← Finset.sum_inter_add_sum_sdiff (M.S x) M.dyn]
    unfold Model.S1 Model.S2
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have : i ∈ M.dyn := (Finset.mem_inter.mp hi).2
      simp only [Model.mix, if_pos this]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have : i ∉ M.dyn := (Finset.mem_sdiff.mp hi).2
      simp only [Model.mix, if_neg this]
  have hexp : ∀ i, M.lam * M.P x (M.mix r) i * (M.mix r i - (V x - V (M.sell x i))) =
      M.lam * (M.mix r i * M.P x (M.mix r) i) - M.lam * V x * M.P x (M.mix r) i
        + M.lam * (M.P x (M.mix r) i * V (M.sell x i)) := by
    intro i; ring
  rw [hxi]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold Model.objM Model.obj
  have : M.lam * M.P0 x (M.mix r) * V x = M.lam * V x - M.lam * V x * ∑ i ∈ M.S x, M.P x (M.mix r) i := by
    have := hsumP
    have h0 : M.P0 x (M.mix r) = 1 - ∑ i ∈ M.S x, M.P x (M.mix r) i := by linarith
    rw [h0]; ring
  linear_combination this
