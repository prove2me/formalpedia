-- Prove2me | solution 1 for PriceQualityService.NestedLogit.ec6_markup_problem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:39:11.647913+00:00
-- url     : https://prove2.me/submissions/340b3532-ff0b-4a07-b871-45a36c7dfbc8

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_MarkupProblem

set_option autoImplicit false

open PriceQualityService.NestedLogit

lemma pqn_sum_nest (f : Nest → ℝ) : ∑ x : Nest, f x = f Nest.s + f Nest.l := by
  have huniv : (Finset.univ : Finset Nest) = {Nest.s, Nest.l} := rfl
  rw [huniv, Finset.sum_pair (by decide)]

/-- weight of a nest as a function of its markup -/
noncomputable def pqnW (M : Model) (q : Vec M) (x : Nest) (r : ℝ) : ℝ :=
  (∑ j, Real.exp (netUtility M q x j)) ^ (1 / M.μ₁) * Real.exp (-(r / M.μ₁))

lemma pqn_attr_pow (M : Model) (hμ : 1 ≤ M.μ₁) (ρ : Nest → ℝ) (q : Vec M) (x : Nest) :
    markupNestAttraction M ρ q x ^ (1 / M.μ₁) = pqnW M q x (ρ x) := by
  have hμ0 : 0 < M.μ₁ := by linarith
  unfold markupNestAttraction pqnW
  have h1 : ∑ j, Real.exp (netUtility M q x j - ρ x) =
      Real.exp (-ρ x) * ∑ j, Real.exp (netUtility M q x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, Real.mul_rpow (Real.exp_pos _).le (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)),
    ← Real.exp_mul]
  have h2 : (-ρ x) * (1 / M.μ₁) = -(ρ x / M.μ₁) := by field_simp
  rw [h2]; ring

lemma pqnW_nonneg (M : Model) (q : Vec M) (x : Nest) (r : ℝ) : 0 ≤ pqnW M q x r :=
  mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)) _)
    (Real.exp_pos _).le

lemma pqn_profit_formula (M : Model) (hμ : 1 ≤ M.μ₁) (ρ : Nest → ℝ) (q : Vec M) :
    markupProfit M ρ q =
      (ρ Nest.s * pqnW M q Nest.s (ρ Nest.s) + ρ Nest.l * pqnW M q Nest.l (ρ Nest.l)) /
        (1 + pqnW M q Nest.s (ρ Nest.s) + pqnW M q Nest.l (ρ Nest.l)) := by
  unfold markupProfit markupNestProb
  rw [pqn_sum_nest]
  simp only [pqn_attr_pow M hμ]
  ring

lemma pqn_foc (μ c1 R W t0 : ℝ) (hμ : 0 < μ) (hc1 : 0 < c1) (φ : ℝ → ℝ)
    (hφ : ∀ t, φ t = (t * (c1 * Real.exp (-(t / μ))) + R) / (1 + c1 * Real.exp (-(t / μ)) + W))
    (hW : 0 ≤ W) (hmax : IsLocalMax φ t0) : t0 - μ = φ t0 := by
  have hφ' : φ = fun t => (t * (c1 * Real.exp (-(t / μ))) + R) / (1 + c1 * Real.exp (-(t / μ)) + W) :=
    funext hφ
  set w : ℝ := c1 * Real.exp (-(t0 / μ)) with hw
  have hwpos : 0 < w := mul_pos hc1 (Real.exp_pos _)
  have hD : 0 < 1 + w + W := by linarith
  have hwd : HasDerivAt (fun t : ℝ => c1 * Real.exp (-(t / μ))) (w * (-(1 / μ))) t0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(t / μ)) (-(1 / μ)) t0 := by
      have := ((hasDerivAt_id' t0).div_const μ).neg
      exact this
    have h2 := (h1.exp).const_mul c1
    have e : w * (-(1 / μ)) = c1 * (Real.exp (-(t0 / μ)) * -(1 / μ)) := by rw [hw]; ring
    rw [e]
    exact h2
  have hN : HasDerivAt (fun t : ℝ => t * (c1 * Real.exp (-(t / μ))) + R)
      (1 * w + t0 * (w * (-(1 / μ)))) t0 := by
    have := ((hasDerivAt_id t0).mul hwd).add_const R
    simpa using this
  have hDd : HasDerivAt (fun t : ℝ => 1 + c1 * Real.exp (-(t / μ)) + W) (w * (-(1 / μ))) t0 := by
    have := (hwd.const_add 1).add_const W
    simpa using this
  have hq := hN.div hDd hD.ne'
  rw [hφ'] at hmax ⊢
  have h0 := hmax.hasDerivAt_eq_zero hq
  have hD2 : (1 + c1 * Real.exp (-(t0 / μ)) + W) ^ 2 ≠ 0 := by
    rw [← hw]; exact pow_ne_zero 2 hD.ne'
  have hnum : (1 * w + t0 * (w * (-(1 / μ)))) * (1 + w + W) -
      (t0 * w + R) * (w * (-(1 / μ))) = 0 := by
    rw [← hw] at h0 hD2
    rcases div_eq_zero_iff.mp h0 with h | h
    · simpa using h
    · exact absurd h hD2
  simp only
  rw [← hw]
  have : (t0 - μ) * (1 + w + W) = t0 * w + R := by
    have hwne : w ≠ 0 := hwpos.ne'
    have hμne : μ ≠ 0 := hμ.ne'
    have h3 : w * ((μ - t0) * (1 + w + W) + (t0 * w + R)) = 0 := by
      have e : w * ((μ - t0) * (1 + w + W) + (t0 * w + R)) = μ *
          ((1 * w + t0 * (w * (-(1 / μ)))) * (1 + w + W) - (t0 * w + R) * (w * (-(1 / μ)))) := by
        field_simp
        ring
      rw [e, hnum, mul_zero]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hwne
    · linarith
  rw [eq_div_iff hD.ne']
  exact this

theorem solution (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i) (q : Vec M) :
    (∀ (p : Vec M) (ρ : Nest → ℝ), (∀ (x : Nest) (i : Fin (M.m x)), markup M p q x i = ρ x) →
        profit M p q = markupProfit M ρ q) ∧
      (∀ ρ : Nest → ℝ, (∀ ρ' : Nest → ℝ, markupProfit M ρ' q ≤ markupProfit M ρ q) →
        ∀ x : Nest, 0 < M.m x → ρ x - M.μ₁ = markupProfit M ρ q) := by
  have hμ0 : 0 < M.μ₁ := by linarith
  refine ⟨?_, ?_⟩
  · intro p ρ h
    have hnat : ∀ y, nestAttraction M p q y = markupNestAttraction M ρ q y := by
      intro y
      unfold nestAttraction markupNestAttraction
      refine Finset.sum_congr rfl (fun j _ => ?_)
      unfold attraction netUtility
      have := h y j
      unfold markup at this
      congr 1
      linarith
    have hnp : ∀ y, nestProb M p q y = markupNestProb M ρ q y := by
      intro y
      simp only [nestProb, markupNestProb, hnat]
    unfold profit markupProfit
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [h x, choiceProb, condProb, hnp x]
    set E := nestAttraction M p q x with hE
    have hsum : ∑ i, attraction M p q x i = E := rfl
    have e1 : ∑ i : Fin (M.m x), ρ x * (markupNestProb M ρ q x * (attraction M p q x i / E)) =
        ρ x * markupNestProb M ρ q x * ((∑ i, attraction M p q x i) / E) := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, hsum]
    by_cases hE0 : E = 0
    · have : markupNestProb M ρ q x = 0 := by
        rw [← hnp x]
        unfold nestProb
        rw [← hE, hE0, Real.zero_rpow (by positivity)]
        simp
      rw [this]; simp
    · rw [div_self hE0, mul_one]
  · intro ρ hmax x hx
    have hprof : ∀ ρ', markupProfit M ρ' q =
        (ρ' Nest.s * pqnW M q Nest.s (ρ' Nest.s) + ρ' Nest.l * pqnW M q Nest.l (ρ' Nest.l)) /
          (1 + pqnW M q Nest.s (ρ' Nest.s) + pqnW M q Nest.l (ρ' Nest.l)) :=
      fun ρ' => pqn_profit_formula M hμ ρ' q
    have hSpos : ∀ y, 0 < M.m y → 0 < (∑ j, Real.exp (netUtility M q y j)) ^ (1 / M.μ₁) := by
      intro y hy
      apply Real.rpow_pos_of_pos
      exact Finset.sum_pos (fun j _ => Real.exp_pos _) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hy⟩⟩)
    cases x
    · -- nest s
      have key := pqn_foc M.μ₁ ((∑ j, Real.exp (netUtility M q Nest.s j)) ^ (1 / M.μ₁))
        (ρ Nest.l * pqnW M q Nest.l (ρ Nest.l)) (pqnW M q Nest.l (ρ Nest.l)) (ρ Nest.s) hμ0
        (hSpos _ hx) (fun t => markupProfit M (Function.update ρ Nest.s t) q) ?_
        (pqnW_nonneg M q _ _) ?_
      · simpa using key
      · intro t
        rw [hprof]
        simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
          Function.update_of_ne]
        unfold pqnW
        ring
      · exact Filter.Eventually.of_forall (fun t => by
          simpa using hmax (Function.update ρ Nest.s t))
    · -- nest l
      have key := pqn_foc M.μ₁ ((∑ j, Real.exp (netUtility M q Nest.l j)) ^ (1 / M.μ₁))
        (ρ Nest.s * pqnW M q Nest.s (ρ Nest.s)) (pqnW M q Nest.s (ρ Nest.s)) (ρ Nest.l) hμ0
        (hSpos _ hx) (fun t => markupProfit M (Function.update ρ Nest.l t) q) ?_
        (pqnW_nonneg M q _ _) ?_
      · simpa using key
      · intro t
        rw [hprof]
        simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
          Function.update_of_ne]
        unfold pqnW
        ring
      · exact Filter.Eventually.of_forall (fun t => by
          simpa using hmax (Function.update ρ Nest.l t))
