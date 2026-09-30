-- Prove2me | solution 1 for RandomGradFree.Accelerated.psi_bound_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:58:22.926258+00:00
-- url     : https://prove2.me/submissions/c73074a7-4535-4ae8-828b-46712a767457

import Definitions.Def_RandomGradFree_Accelerated_psi
import Definitions.Def_RandomGradFree_Accelerated_C
import Mathlib.Tactic
open RandomGradFree.Accelerated
open scoped BigOperators

theorem solution (n : ℕ) (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (γ : ℕ → ℝ) (L₁ : ℝ) (hL₁ : 0 < L₁)
    (hαlow : ∀ j, Real.sqrt (γ 0 / L₁) / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) :
    psi α k ≤ 1 / (1 + k / (8 * ((n : ℝ) + 4)) * Real.sqrt (γ 0 / L₁)) ^ 2 := by
  let a : ℝ := Real.sqrt (γ 0/L₁)/(4*((n:ℝ)+4))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (hαlow 0).trans (hα 0).2
  have hbase : 1-a ≤ 1/(1+a/2)^2 := by
    apply (le_div_iff₀ (by positivity : 0 < (1+a/2)^2)).mpr
    have hh : (1-a)*(1+a/2)^2=1-a^2*(3+a)/4 := by ring
    rw [hh]
    have hp : 0 ≤ a^2*(3+a)/4 := by positivity
    linarith
  have hprod : psi α k ≤ (1-a)^k := by
    unfold psi
    calc
      (∏ i ∈ Finset.range k, (1-α i)) ≤ ∏ i ∈ Finset.range k, (1-a) :=
        Finset.prod_le_prod (fun i hi => sub_nonneg.mpr (hα i).2) (fun i hi => by linarith [hαlow i])
      _ = _ := by simp
  have hber := one_add_mul_le_pow (a := a/2) (by linarith : -2 ≤ a/2) k
  have hden : 0 < 1+(k:ℝ)*(a/2) := by positivity
  have hquad : psi α k ≤ 1/(1+(k:ℝ)*(a/2))^2 := by
    calc
      psi α k ≤ (1-a)^k := hprod
      _ ≤ (1/(1+a/2)^2)^k := pow_le_pow_left₀ (by linarith) hbase k
      _ = 1/((1+a/2)^k)^2 := by rw [div_pow,one_pow,pow_right_comm]
      _ ≤ 1/(1+(k:ℝ)*(a/2))^2 := by gcongr
  convert hquad using 1
  congr 2
  dsimp [a]
  field_simp
  ring
