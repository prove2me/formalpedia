-- Prove2me | solution 1 for PriceQualityService.NestedLogit.ec7_optimal_quality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:32:22.480691+00:00
-- url     : https://prove2.me/submissions/d321825f-24d8-4697-ae5f-fefac048b5d0

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Optimum

set_option autoImplicit false

open PriceQualityService.NestedLogit

lemma pqn_sum_nest (f : Nest → ℝ) : ∑ x : Nest, f x = f Nest.s + f Nest.l := by
  have huniv : (Finset.univ : Finset Nest) = {Nest.s, Nest.l} := rfl
  rw [huniv, Finset.sum_pair (by decide)]

lemma pqn_net_dagger (M : Model) (hc : ∀ x i, 0 < M.c x i) (q : Vec M) (x : Nest) (i : Fin (M.m x)) :
    netUtility M q x i + M.c x i * (q x i - qDagger M x i) ^ 2 = netUtility M (qDagger M) x i := by
  have := (hc x i).ne'
  unfold netUtility qDagger
  field_simp
  ring

theorem solution (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i)
    (r : ℝ) (q : Vec M) :
    fixedPointRHS M q r ≤ fixedPointRHS M (qDagger M) r ∧
      (fixedPointRHS M q r = fixedPointRHS M (qDagger M) r → q = qDagger M) := by
  have hμ0 : 0 < M.μ₁ := by linarith
  have hμ' : 0 < 1 / M.μ₁ := by positivity
  have hterm : ∀ x (j : Fin (M.m x)),
      Real.exp (netUtility M q x j - r - M.μ₁) ≤ Real.exp (netUtility M (qDagger M) x j - r - M.μ₁) := by
    intro x j
    apply Real.exp_le_exp.mpr
    have := pqn_net_dagger M hc q x j
    have := mul_nonneg (hc x j).le (sq_nonneg (q x j - qDagger M x j))
    linarith
  have hsum : ∀ x, (∑ j, Real.exp (netUtility M q x j - r - M.μ₁)) ≤
      ∑ j, Real.exp (netUtility M (qDagger M) x j - r - M.μ₁) :=
    fun x => Finset.sum_le_sum (fun j _ => hterm x j)
  have hnn : ∀ (q' : Vec M) x, 0 ≤ ∑ j, Real.exp (netUtility M q' x j - r - M.μ₁) :=
    fun q' x => Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  have hxle : ∀ x, M.μ₁ * (∑ j, Real.exp (netUtility M q x j - r - M.μ₁)) ^ (1 / M.μ₁) ≤
      M.μ₁ * (∑ j, Real.exp (netUtility M (qDagger M) x j - r - M.μ₁)) ^ (1 / M.μ₁) :=
    fun x => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hnn q x) (hsum x) hμ'.le) hμ0.le
  refine ⟨Finset.sum_le_sum (fun x _ => hxle x), ?_⟩
  intro heq
  by_contra hne
  have hex : ∃ x i, q x i ≠ qDagger M x i := by
    by_contra hall
    push_neg at hall
    exact hne (funext fun x => funext fun i => hall x i)
  obtain ⟨x0, i0, hi0⟩ := hex
  have hlt0 : (∑ j, Real.exp (netUtility M q x0 j - r - M.μ₁)) <
      ∑ j, Real.exp (netUtility M (qDagger M) x0 j - r - M.μ₁) := by
    apply Finset.sum_lt_sum (fun j _ => hterm x0 j)
    refine ⟨i0, Finset.mem_univ _, Real.exp_lt_exp.mpr ?_⟩
    have := pqn_net_dagger M hc q x0 i0
    have : 0 < M.c x0 i0 * (q x0 i0 - qDagger M x0 i0) ^ 2 :=
      mul_pos (hc x0 i0) (by positivity [sub_ne_zero.mpr hi0])
    linarith
  have hxlt : M.μ₁ * (∑ j, Real.exp (netUtility M q x0 j - r - M.μ₁)) ^ (1 / M.μ₁) <
      M.μ₁ * (∑ j, Real.exp (netUtility M (qDagger M) x0 j - r - M.μ₁)) ^ (1 / M.μ₁) :=
    mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (hnn q x0) hlt0 hμ') hμ0
  have : fixedPointRHS M q r < fixedPointRHS M (qDagger M) r :=
    Finset.sum_lt_sum (fun x _ => hxle x) ⟨x0, Finset.mem_univ _, hxlt⟩
  linarith
