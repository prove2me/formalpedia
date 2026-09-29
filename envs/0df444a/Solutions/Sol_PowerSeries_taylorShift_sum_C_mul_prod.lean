-- Prove2me | solution 1 for PowerSeries.taylorShift_sum_C_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/44e2d559-5ede-52d2-8686-75eca017d234

import Mathlib
import Theorems.Thm_PowerSeries_norm_coeff_mul_mul_pow_le
import Theorems.Thm_PowerSeries_taylorShift_add
import Theorems.Thm_PowerSeries_taylorShift_mul
import Theorems.Thm_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_taylorShift_sum_C_mul_prod

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

theorem c1s_shift_C [CompleteSpace L] [IsUltrametricDist L] (x a : L) :
    (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) (PowerSeries.C x) * ((n + k).choose n : L) * a ^ k)
      = PowerSeries.C x := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases n with _ | n
  · rw [if_pos rfl, tsum_eq_single 0]
    · simp
    · intro k hk
      simp [PowerSeries.coeff_C, hk]
  · rw [if_neg (Nat.succ_ne_zero n)]
    have h0 : ∀ k : ℕ, PowerSeries.coeff (n + 1 + k) (PowerSeries.C x) * ((n + 1 + k).choose (n + 1) : L)
        * a ^ k = 0 := by
      intro k
      rw [PowerSeries.coeff_C, if_neg (by omega), zero_mul, zero_mul]
    simp only [h0, tsum_zero]

theorem c1s_shift_zero [CompleteSpace L] [IsUltrametricDist L] (a : L) :
    (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) (0 : PowerSeries L) * ((n + k).choose n : L) * a ^ k) = 0 := by
  ext n
  simp [PowerSeries.coeff_mk]

theorem c1s_shift_one [CompleteSpace L] [IsUltrametricDist L] (a : L) :
    (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) (1 : PowerSeries L) * ((n + k).choose n : L) * a ^ k) = 1 := by
  simpa using c1s_shift_C (1 : L) a

theorem c1s_shift_prod [CompleteSpace L] [IsUltrametricDist L] {κ : Type*} (u : Finset κ)
    (G : κ → PowerSeries L) {ρ : ℝ} (hρ : 0 < ρ)
    (hG : ∀ j ∈ u, ∀ n, ‖PowerSeries.coeff n (G j)‖ * ρ ^ n ≤ 1) (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (∏ j ∈ u, G j) * ((n + k).choose n : L) * a ^ k)
      = ∏ j ∈ u, (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (G j) * ((n + k).choose n : L) * a ^ k) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using c1s_shift_one (L := L) a
  | insert b u hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb,
      PowerSeries.taylorShift_mul (G b) (∏ j ∈ u, G j) hρ (hG b (Finset.mem_insert_self b u))
        (c1s_bdd_prod u G hρ.le (fun j hj => hG j (Finset.mem_insert_of_mem hj))) a ha,
      ih (fun j hj => hG j (Finset.mem_insert_of_mem hj))]

end c1s_helpers

theorem solution
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    {ι : Type*} (s : Finset ι) (c : ι → L) {κ : Type*} [Fintype κ] (F : ι → κ → PowerSeries L)
    {ρ : ℝ} (hρ : 0 < ρ) (hF : ∀ i ∈ s, ∀ j n, ‖PowerSeries.coeff n (F i j)‖ * ρ ^ n ≤ 1)
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (∑ i ∈ s, PowerSeries.C (c i) * ∏ j, F i j) * ((n + k).choose n : L) * a ^ k)
      = ∑ i ∈ s, PowerSeries.C (c i) * ∏ j, (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F i j) * ((n + k).choose n : L) * a ^ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using c1s_shift_zero (L := L) a
  | insert b s hb ih =>
    have hFb : ∀ j ∈ (Finset.univ : Finset κ), ∀ n, ‖PowerSeries.coeff n (F b j)‖ * ρ ^ n ≤ 1 :=
      fun j _ => hF b (Finset.mem_insert_self b s) j
    have hFs : ∀ i ∈ s, ∀ j n, ‖PowerSeries.coeff n (F i j)‖ * ρ ^ n ≤ 1 :=
      fun i hi => hF i (Finset.mem_insert_of_mem hi)

    have hrest := PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le s c F hρ.le
      (Finset.sum_nonneg fun i _ => norm_nonneg (c i)) hFs
      (fun i hi => Finset.single_le_sum (fun i _ => norm_nonneg (c i)) hi)
    rw [Finset.sum_insert hb, Finset.sum_insert hb,
      PowerSeries.taylorShift_add (PowerSeries.C (c b) * ∏ j, F b j) (∑ i ∈ s, PowerSeries.C (c i) * ∏ j, F i j)
        hρ (c1s_bdd_C_mul_prod Finset.univ (c b) (F b) hρ.le hFb) hrest a ha,
      PowerSeries.taylorShift_mul (PowerSeries.C (c b)) (∏ j, F b j) hρ (c1s_bdd_C (c b))
        (c1s_bdd_prod Finset.univ (F b) hρ.le hFb) a ha,
      c1s_shift_C, c1s_shift_prod Finset.univ (F b) hρ hFb a ha, ih hFs]

#print axioms solution

end S_PowerSeries_taylorShift_sum_C_mul_prod
end P2MW
export P2MW.S_PowerSeries_taylorShift_sum_C_mul_prod (solution)
