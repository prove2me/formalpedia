-- Prove2me | solution 1 for Sendov.rubinstein_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:32.089161+00:00
-- url     : https://prove2.me/submissions/c3462d5d-2425-4fb0-ade8-aad143ada4c6

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_eval_prod_at
import Theorems.Thm_Sendov_eval_deriv_prod_at
import Theorems.Thm_Sendov_boundary_reciprocal
import Theorems.Thm_Sendov_all_q_eq_one
import Theorems.Thm_Sendov_exists_crit_multiset
import Theorems.Thm_Sendov_exists_root_multiset
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1)
      ∨ p = C p.leadingCoeff * (X ^ n - 1) := by
  by_cases hex : ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1
  · exact Or.inl hex
  refine Or.inr ?_
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - 1‖ := by
    intro w hw
    by_contra hlt
    exact hex ⟨w, hw, not_le.1 hlt⟩
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hn0 : (n : ℂ) ≠ 0 := by
    intro h
    have h1 : n = 0 := by exact_mod_cast h
    omega
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp1
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => X - C u)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- the repeated-root case is already excluded
  have hp'1 : (derivative p).eval 1 ≠ 0 := fun h => hex ⟨1, h, by simp⟩
  -- `p'` and `p''` from `p = c (X-1) Q`
  have hd1 : derivative p = C p.leadingCoeff
      * ((z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (z.map (fun w => X - C w)).prod) := by
    conv_lhs => rw [hpz]
    rw [derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul]
  have hd2 : derivative (derivative p) = C p.leadingCoeff
      * (2 * derivative (z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (derivative (z.map (fun w => X - C w)).prod)) := by
    rw [hd1, derivative_C_mul, derivative_add, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul]
    ring
  have hA : (derivative p).eval 1 = p.leadingCoeff * (z.map (fun w => (1 : ℂ) - w)).prod := by
    rw [hd1]
    simp [eval_prod_at]
  have hB : (derivative (derivative p)).eval 1
      = p.leadingCoeff * (2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))) := by
    rw [hd2]
    simp [eval_deriv_prod_at]
  -- `p'` and `p''` from `p' = n c R`
  have hmapq : (q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => (1 : ℂ) - u)
      = q.map (fun v => v⁻¹) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun v _ => by simp
  have hC : (derivative p).eval 1
      = (n : ℂ) * p.leadingCoeff * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq', eval_mul, eval_C, eval_prod_at, hmapq]
  have hD : (derivative (derivative p)).eval 1
      = (n : ℂ) * p.leadingCoeff * sumEraseProd (q.map (fun v => v⁻¹)) := by
    rw [hpq', derivative_C_mul, eval_mul, eval_C, eval_deriv_prod_at, hmapq]
  -- the two relations, after cancelling the leading coefficient
  have hI : (z.map (fun w => (1 : ℂ) - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hA.symm.trans hC
    linear_combination h
  have hII : 2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))
      = (n : ℂ) * sumEraseProd (q.map (fun v => v⁻¹)) := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hB.symm.trans hD
    linear_combination h
  -- no `zⱼ` equals `1`
  have hZ0 : (z.map (fun w => (1 : ℂ) - w)).prod ≠ 0 := by
    intro h
    exact hp'1 (by rw [hA, h, mul_zero])
  have hZne : ∀ u ∈ z.map (fun w => (1 : ℂ) - w), u ≠ 0 := by
    intro u hu hu0
    exact hZ0 (Multiset.prod_eq_zero (hu0 ▸ hu))
  have hzne : ∀ w ∈ z, w ≠ 1 := by
    intro w hw hw1
    exact hZne ((1 : ℂ) - w) (Multiset.mem_map_of_mem _ hw) (by rw [hw1]; ring)
  have hQne : ∀ u ∈ q.map (fun v => v⁻¹), u ≠ 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hu
    exact inv_ne_zero (hq0 v hv)
  -- `(BR)`
  have hBRraw := boundary_reciprocal (n := n) hn0 hZne hQne hI hII
  have hQiinv : ((q.map (fun v => v⁻¹)).map (fun u => u⁻¹)).sum = q.sum := by
    rw [Multiset.map_map]
    simp
  have hZsinv : (z.map (fun w => (1 : ℂ) - w)).map (fun u => u⁻¹)
      = z.map (fun w => ((1 : ℂ) - w)⁻¹) := by
    rw [Multiset.map_map]
    rfl
  rw [hQiinv, hZsinv] at hBRraw
  -- every `qⱼ` is `1`, so every critical point is `0`
  have hqone := all_q_eq_one hqcard hzcard hq1 hz1 hzne hBRraw
  have hderivX : derivative p = C ((n : ℂ) * p.leadingCoeff) * X ^ (n - 1) := by
    rw [hpq]
    congr 1
    have hmap : q.map (fun v => X - C ((1 : ℂ) - v⁻¹))
        = Multiset.replicate q.card (X : ℂ[X]) := by
      rw [← Multiset.map_const']
      exact Multiset.map_congr rfl fun v hv => by rw [hqone v hv]; simp
    rw [hmap, Multiset.prod_replicate, hqcard]
  -- hence `p - c Xⁿ` is constant
  have hdz : derivative (p - C p.leadingCoeff * X ^ n) = 0 := by
    rw [derivative_sub, hderivX, derivative_C_mul, derivative_X_pow, map_mul]
    ring
  have hdeg0 : (p - C p.leadingCoeff * X ^ n).natDegree = 0 := derivative_eq_zero.1 hdz
  obtain ⟨d, hd⟩ := natDegree_eq_zero.1 hdeg0
  have hdval : d = -p.leadingCoeff := by
    have h := congrArg (Polynomial.eval (1 : ℂ)) hd
    simpa [hp1] using h
  have hCd : (C d : ℂ[X]) = -C p.leadingCoeff := by rw [hdval, map_neg]
  linear_combination -hd + hCd
end Sendov
