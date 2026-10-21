-- Prove2me | solution 1 for PriceQualityService.NestedLogit.ec5_equal_markup
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:45:30.604193+00:00
-- url     : https://prove2.me/submissions/0fd7789e-063e-412e-b77a-d34efcc3f38c

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Model

set_option autoImplicit false

open PriceQualityService.NestedLogit

lemma pqn_sum_nest (f : Nest → ℝ) : ∑ x : Nest, f x = f Nest.s + f Nest.l := by
  have huniv : (Finset.univ : Finset Nest) = {Nest.s, Nest.l} := rfl
  rw [huniv, Finset.sum_pair (by decide)]

lemma pqn_sum_update {n : ℕ} (F : Fin n → ℝ → ℝ) (v : Fin n → ℝ) (i0 : Fin n) (τ : ℝ) :
    ∑ i, F i (Function.update v i0 τ i) = F i0 τ + ∑ i ∈ Finset.univ.erase i0, F i (v i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
  congr 1
  · simp
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- aggregated profit term of a nest -/
noncomputable def pqnT (M : Model) (p q : Vec M) (x : Nest) : ℝ :=
  nestAttraction M p q x ^ (1 / M.μ₁) *
    ((∑ i, markup M p q x i * attraction M p q x i) / nestAttraction M p q x)

lemma pqn_profit_eq (M : Model) (p q : Vec M) :
    profit M p q = (pqnT M p q Nest.s + pqnT M p q Nest.l) /
      (1 + nestAttraction M p q Nest.s ^ (1 / M.μ₁) + nestAttraction M p q Nest.l ^ (1 / M.μ₁)) := by
  unfold profit
  rw [pqn_sum_nest]
  have hx : ∀ x, ∑ i, markup M p q x i * choiceProb M p q x i =
      pqnT M p q x / (1 + nestAttraction M p q Nest.s ^ (1 / M.μ₁) +
        nestAttraction M p q Nest.l ^ (1 / M.μ₁)) := by
    intro x
    unfold choiceProb nestProb condProb pqnT
    rw [Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hx, hx]; ring

lemma pqn_foc2 (θ β κ CE CN C1 C2 τ0 : ℝ) (hθ : 0 < θ) (hCE : 0 ≤ CE) (hC2 : 0 ≤ C2)
    (φ : ℝ → ℝ)
    (hφ : ∀ τ, φ τ = ((Real.exp (β - τ) + CE) ^ θ *
        (((τ - κ) * Real.exp (β - τ) + CN) / (Real.exp (β - τ) + CE)) + C1) /
        (1 + (Real.exp (β - τ) + CE) ^ θ + C2))
    (hmax : IsLocalMax φ τ0) :
    τ0 - κ = 1 + θ * φ τ0 +
      (1 - θ) * (((τ0 - κ) * Real.exp (β - τ0) + CN) / (Real.exp (β - τ0) + CE)) := by
  have hφ' : φ = fun τ => ((Real.exp (β - τ) + CE) ^ θ *
        (((τ - κ) * Real.exp (β - τ) + CN) / (Real.exp (β - τ) + CE)) + C1) /
        (1 + (Real.exp (β - τ) + CE) ^ θ + C2) := funext hφ
  have hgpos : 0 < Real.exp (β - τ0) := Real.exp_pos _
  have hE0 : 0 < Real.exp (β - τ0) + CE := by linarith
  have hg : HasDerivAt (fun τ : ℝ => Real.exp (β - τ)) (-Real.exp (β - τ0)) τ0 := by
    have := ((hasDerivAt_id' τ0).const_sub β).exp
    simpa using this
  have hE : HasDerivAt (fun τ : ℝ => Real.exp (β - τ) + CE) (-Real.exp (β - τ0)) τ0 :=
    hg.add_const CE
  have hN : HasDerivAt (fun τ : ℝ => (τ - κ) * Real.exp (β - τ) + CN)
      (1 * Real.exp (β - τ0) + (τ0 - κ) * (-Real.exp (β - τ0))) τ0 :=
    (((hasDerivAt_id' τ0).sub_const κ).mul hg).add_const CN
  have hP := hE.rpow_const (p := θ) (Or.inl hE0.ne')
  have hQ := hN.div hE hE0.ne'
  have hT := (hP.mul hQ).add_const C1
  have hD := (hP.const_add 1).add_const C2
  have hP0 : 0 < (Real.exp (β - τ0) + CE) ^ θ := Real.rpow_pos_of_pos hE0 θ
  have hDpos : 0 < 1 + (Real.exp (β - τ0) + CE) ^ θ + C2 := by linarith
  have hΛ := hT.div hD hDpos.ne'
  rw [hφ'] at hmax ⊢
  have h0 := hmax.hasDerivAt_eq_zero hΛ
  simp only [Pi.mul_apply, Pi.div_apply] at h0 ⊢
  rw [Real.rpow_sub_one hE0.ne'] at h0
  generalize Real.exp (β - τ0) = g0 at *
  generalize (g0 + CE) ^ θ = P0 at *
  generalize hE0def : g0 + CE = E0 at *
  have hnum := (div_eq_zero_iff.mp h0).resolve_right (pow_ne_zero 2 hDpos.ne')
  have hform : ((-g0 * θ * (P0 / E0) * (((τ0 - κ) * g0 + CN) / E0) +
            P0 * (((1 * g0 + (τ0 - κ) * -g0) * E0 - ((τ0 - κ) * g0 + CN) * -g0) / E0 ^ 2)) *
          (1 + P0 + C2) -
        (P0 * (((τ0 - κ) * g0 + CN) / E0) + C1) * (-g0 * θ * (P0 / E0))) =
      (g0 * P0 * (1 + P0 + C2) / E0) *
        (1 - (τ0 - κ) + (1 - θ) * (((τ0 - κ) * g0 + CN) / E0) +
          θ * ((P0 * (((τ0 - κ) * g0 + CN) / E0) + C1) / (1 + P0 + C2))) := by
    have := hDpos.ne'
    have := hE0.ne'
    field_simp
    ring
  rw [hform] at hnum
  have hne : g0 * P0 * (1 + P0 + C2) / E0 ≠ 0 := by positivity
  have hX := (mul_eq_zero.mp hnum).resolve_left hne
  linarith

theorem solution (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i)
    (p q : Vec M) (hmax : ∀ p' : Vec M, profit M p' q ≤ profit M p q) :
    (∀ (x : Nest) (i : Fin (M.m x)),
        markup M p q x i = 1 + profit M p q / M.μ₁ + (1 - 1 / M.μ₁) * nestAvgMarkup M p q x) ∧
      (∀ (x : Nest) (i j : Fin (M.m x)), markup M p q x i = markup M p q x j) := by
  have hμ0 : 0 < M.μ₁ := by linarith
  have hθ : 0 < 1 / M.μ₁ := by positivity
  have key : ∀ (x : Nest) (i : Fin (M.m x)),
      markup M p q x i = 1 + profit M p q / M.μ₁ + (1 - 1 / M.μ₁) * nestAvgMarkup M p q x := by
    intro x i
    obtain ⟨pτ, hpτdef⟩ : ∃ pτ : ℝ → Vec M,
        pτ = fun τ => Function.update p x (Function.update (p x) i τ) := ⟨_, rfl⟩
    have hpτ_self : pτ (p x i) = p := by
      rw [hpτdef]; simp
    have hother : ∀ τ y, y ≠ x → pτ τ y = p y := fun τ y hy => by
      rw [hpτdef]; simp [Function.update_of_ne hy]
    have hxτ : ∀ τ, pτ τ x = Function.update (p x) i τ := fun τ => by
      rw [hpτdef]; simp
    obtain ⟨CE, hCE⟩ : ∃ CE : ℝ, CE = ∑ i' ∈ Finset.univ.erase i, attraction M p q x i' := ⟨_, rfl⟩
    obtain ⟨CN, hCN⟩ : ∃ CN : ℝ,
        CN = ∑ i' ∈ Finset.univ.erase i, markup M p q x i' * attraction M p q x i' := ⟨_, rfl⟩
    have hCE0 : 0 ≤ CE := by
      rw [hCE]; exact Finset.sum_nonneg (fun i' _ => (Real.exp_pos _).le)
    obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = M.α x i * q x i + M.t x * M.s x i := ⟨_, rfl⟩
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = M.c x i * q x i ^ 2 + M.t x * (M.a x i - M.b x i * q x i) :=
      ⟨_, rfl⟩
    have hE : ∀ τ, nestAttraction M (pτ τ) q x = Real.exp (β - τ) + CE := by
      intro τ
      have h1 : ∀ i', attraction M (pτ τ) q x i' =
          (fun (i'' : Fin (M.m x)) (u : ℝ) => Real.exp (M.α x i'' * q x i'' - u + M.t x * M.s x i''))
            i' (Function.update (p x) i τ i') := by
        intro i'
        simp only [attraction, hxτ]
      unfold nestAttraction
      rw [Finset.sum_congr rfl (fun i' _ => h1 i'),
        pqn_sum_update (fun (i'' : Fin (M.m x)) (u : ℝ) =>
          Real.exp (M.α x i'' * q x i'' - u + M.t x * M.s x i'')) (p x) i τ, hCE]
      congr 1
      rw [hβ]; congr 1; ring
    have hN : ∀ τ, ∑ i', markup M (pτ τ) q x i' * attraction M (pτ τ) q x i' =
        (τ - κ) * Real.exp (β - τ) + CN := by
      intro τ
      have h1 : ∀ i', markup M (pτ τ) q x i' * attraction M (pτ τ) q x i' =
          (fun (i'' : Fin (M.m x)) (u : ℝ) =>
            (u - (M.c x i'' * q x i'' ^ 2 + M.t x * (M.a x i'' - M.b x i'' * q x i''))) *
              Real.exp (M.α x i'' * q x i'' - u + M.t x * M.s x i''))
            i' (Function.update (p x) i τ i') := by
        intro i'
        simp only [markup, attraction, hxτ]
        ring
      rw [Finset.sum_congr rfl (fun i' _ => h1 i'),
        pqn_sum_update (fun (i'' : Fin (M.m x)) (u : ℝ) =>
          (u - (M.c x i'' * q x i'' ^ 2 + M.t x * (M.a x i'' - M.b x i'' * q x i''))) *
            Real.exp (M.α x i'' * q x i'' - u + M.t x * M.s x i'')) (p x) i τ, hCN]
      congr 1
      · rw [hβ, hκ]; congr 1; ring
      · refine Finset.sum_congr rfl (fun i' _ => ?_)
        simp only [markup, attraction]
        ring
    have hT : ∀ τ, pqnT M (pτ τ) q x = (Real.exp (β - τ) + CE) ^ (1 / M.μ₁) *
        (((τ - κ) * Real.exp (β - τ) + CN) / (Real.exp (β - τ) + CE)) := by
      intro τ
      unfold pqnT
      rw [hE, hN]
    have hoth : ∀ τ y, y ≠ x → nestAttraction M (pτ τ) q y = nestAttraction M p q y ∧
        pqnT M (pτ τ) q y = pqnT M p q y := by
      intro τ y hy
      constructor
      · simp only [nestAttraction, attraction, hother τ y hy]
      · simp only [pqnT, nestAttraction, markup, attraction, hother τ y hy]
    have hform : ∃ C1 C2 : ℝ, 0 ≤ C2 ∧ ∀ τ, profit M (pτ τ) q =
        ((Real.exp (β - τ) + CE) ^ (1 / M.μ₁) *
          (((τ - κ) * Real.exp (β - τ) + CN) / (Real.exp (β - τ) + CE)) + C1) /
        (1 + (Real.exp (β - τ) + CE) ^ (1 / M.μ₁) + C2) := by
      cases x
      · refine ⟨pqnT M p q Nest.l, nestAttraction M p q Nest.l ^ (1 / M.μ₁),
          Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)) _, fun τ => ?_⟩
        rw [pqn_profit_eq, hE τ, hT τ, (hoth τ Nest.l (by decide)).1, (hoth τ Nest.l (by decide)).2]
      · refine ⟨pqnT M p q Nest.s, nestAttraction M p q Nest.s ^ (1 / M.μ₁),
          Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)) _, fun τ => ?_⟩
        rw [pqn_profit_eq, hE τ, hT τ, (hoth τ Nest.s (by decide)).1, (hoth τ Nest.s (by decide)).2]
        ring
    obtain ⟨C1, C2, hC2, hφ⟩ := hform
    have hloc : IsLocalMax (fun τ => profit M (pτ τ) q) (p x i) :=
      Filter.Eventually.of_forall (fun τ => by
        simp only
        rw [hpτ_self]
        exact hmax _)
    have hfoc := pqn_foc2 (1 / M.μ₁) β κ CE CN C1 C2 (p x i) hθ hCE0 hC2
      (fun τ => profit M (pτ τ) q) hφ hloc
    rw [hpτ_self] at hfoc
    have hE0 := hE (p x i)
    have hN0 := hN (p x i)
    rw [hpτ_self] at hE0 hN0
    have havg : nestAvgMarkup M p q x =
        (((p x i - κ) * Real.exp (β - p x i) + CN) / (Real.exp (β - p x i) + CE)) := by
      rw [← hE0, ← hN0]
      unfold nestAvgMarkup condProb
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun i' _ => by ring)
    have hmk : markup M p q x i = p x i - κ := by
      rw [hκ]; unfold markup; ring
    rw [hmk, havg]
    have : profit M p q / M.μ₁ = 1 / M.μ₁ * profit M p q := by ring
    rw [this]
    linarith
  exact ⟨key, fun x i j => by rw [key x i, key x j]⟩
