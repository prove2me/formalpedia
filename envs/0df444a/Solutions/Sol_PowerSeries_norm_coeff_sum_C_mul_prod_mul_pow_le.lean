-- Prove2me | solution 1 for PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/27694737-407a-57bb-862c-a7d12c3c94c5

import Mathlib
import Theorems.Thm_PowerSeries_norm_coeff_mul_mul_pow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

section c1s_helpers

variable {L : Type*} [NontriviallyNormedField L]

theorem c1s_bdd_C {ρ : ℝ} (x : L) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.C x)‖ * ρ ^ n ≤ ‖x‖ := by
  rw [PowerSeries.coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem c1s_bdd_one (ρ : ℝ) (n : ℕ) :
    ‖PowerSeries.coeff n (1 : PowerSeries L)‖ * ρ ^ n ≤ 1 := by
  simpa using c1s_bdd_C (ρ := ρ) (1 : L) n

theorem c1s_bdd_add [IsUltrametricDist L] (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 ≤ ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (n : ℕ) : ‖PowerSeries.coeff n (F + G)‖ * ρ ^ n ≤ max M M' := by
  rw [map_add]
  calc ‖PowerSeries.coeff n F + PowerSeries.coeff n G‖ * ρ ^ n
        ≤ max ‖PowerSeries.coeff n F‖ ‖PowerSeries.coeff n G‖ * ρ ^ n :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (pow_nonneg hρ n)
    _ = max (‖PowerSeries.coeff n F‖ * ρ ^ n) (‖PowerSeries.coeff n G‖ * ρ ^ n) :=
          max_mul_of_nonneg _ _ (pow_nonneg hρ n)
    _ ≤ max M M' := max_le_max (hF n) (hG n)

theorem c1s_bdd_prod [CompleteSpace L] [IsUltrametricDist L] {κ : Type*} (u : Finset κ)
    (G : κ → PowerSeries L) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hG : ∀ j ∈ u, ∀ n, ‖PowerSeries.coeff n (G j)‖ * ρ ^ n ≤ 1) (n : ℕ) :
    ‖PowerSeries.coeff n (∏ j ∈ u, G j)‖ * ρ ^ n ≤ 1 := by
  classical
  induction u using Finset.induction_on generalizing n with
  | empty => simpa using c1s_bdd_one (L := L) ρ n
  | insert b u hb ih =>
    rw [Finset.prod_insert hb]
    have h := PowerSeries.norm_coeff_mul_mul_pow_le (G b) (∏ j ∈ u, G j) hρ
      (hG b (Finset.mem_insert_self b u)) (fun m => ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)) m) n
    simpa using h

theorem c1s_bdd_C_mul_prod [CompleteSpace L] [IsUltrametricDist L] {κ : Type*} (u : Finset κ)
    (x : L) (G : κ → PowerSeries L) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hG : ∀ j ∈ u, ∀ n, ‖PowerSeries.coeff n (G j)‖ * ρ ^ n ≤ 1) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.C x * ∏ j ∈ u, G j)‖ * ρ ^ n ≤ ‖x‖ := by
  have h := PowerSeries.norm_coeff_mul_mul_pow_le (PowerSeries.C x) (∏ j ∈ u, G j) hρ
    (c1s_bdd_C x) (c1s_bdd_prod u G hρ hG) n
  simpa using h

end c1s_helpers

theorem solution
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    {ι : Type*} (s : Finset ι) (c : ι → L) {κ : Type*} [Fintype κ] (F : ι → κ → PowerSeries L)
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hF : ∀ i ∈ s, ∀ j n, ‖PowerSeries.coeff n (F i j)‖ * ρ ^ n ≤ 1) (hc : ∀ i ∈ s, ‖c i‖ ≤ B)
    (n : ℕ) :
    ‖PowerSeries.coeff n (∑ i ∈ s, PowerSeries.C (c i) * ∏ j, F i j)‖ * ρ ^ n ≤ B := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa using hB
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, ← max_self B]
    exact c1s_bdd_add _ _ hρ
      (fun m => (c1s_bdd_C_mul_prod Finset.univ (c b) (F b) hρ
        (fun j _ => hF b (Finset.mem_insert_self b s) j) m).trans (hc b (Finset.mem_insert_self b s)))
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) (fun i hi => hc i (Finset.mem_insert_of_mem hi))) n

#print axioms solution

end S_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le
end P2MW
export P2MW.S_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le (solution)
