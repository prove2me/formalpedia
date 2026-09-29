-- Prove2me | solution 1 for PowerSeries.norm_tsum_coeff_mul_pow_le_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6c9e7236-f435-52ff-a48a-479f68d73013

import Mathlib
import Theorems.Thm_PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le
import Theorems.Thm_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt
import Theorems.Thm_PowerSeries_coeff_zero_taylorShift
import Theorems.Thm_PowerSeries_taylorShift_mul
import Theorems.Thm_PowerSeries_taylorShift_X_sub_C
import Theorems.Thm_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "subst mk coeff_C order coeff_of_lt_order order_mul map C coeff order_eq_nat X order_X coeff_X summable_and_norm_tsum_coeff_mul_pow_le tsum_coeff_mul_mul_pow_eq_of_norm_lt coeff_zero_taylorShift taylorShift_mul taylorShift_X_sub_C exists_eq_X_sub_C_mul_of_tsum_eq_zero"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

theorem l1_M_nonneg (F : PowerSeries L) {ρ M : ℝ}
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) : 0 ≤ M := by
  have := hF 0
  simp only [pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

theorem l1_coeff_X_sub_C (w : L) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X - PowerSeries.C w)
      = (if n = 1 then 1 else 0) - (if n = 0 then w else 0) := by
  rw [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]

theorem l1_bound_X_sub_C (w : L) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.X - PowerSeries.C w)‖ * ρ ^ n ≤ max ρ ‖w‖ := by
  rw [l1_coeff_X_sub_C]
  rcases n with _ | n
  · simp
  · rcases n with _ | n
    · simp
    · rw [if_neg (by omega), if_neg (by omega)]
      simp only [sub_zero, norm_zero, zero_mul]
      exact le_max_of_le_left hρ

theorem l1_tsum_X_sub_C (w z : L) :
    ∑' n, PowerSeries.coeff n (PowerSeries.X - PowerSeries.C w) * z ^ n = z - w := by
  rw [tsum_eq_sum (s := {0, 1}) (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [l1_coeff_X_sub_C, if_neg hn.2, if_neg hn.1]
    simp)]
  rw [Finset.sum_pair (by norm_num)]
  simp [l1_coeff_X_sub_C]
  ring

open Classical in

theorem l1_order_C_add_X_mul (c : L) (P : PowerSeries L) :
    ((PowerSeries.C c + PowerSeries.X) * P).order = (if c = 0 then 1 else 0) + P.order := by
  rw [PowerSeries.order_mul]
  congr 1
  split_ifs with hc
  · rw [hc, map_zero, zero_add, PowerSeries.order_X]
  · rw [← Nat.cast_zero, PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    simpa using hc

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod.PowerSeries in
open Classical in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (S : Multiset L) (hS1 : ∀ w ∈ S, ‖w‖ < ρ)
    (hS : ∀ w ∈ S, (S.count w : ℕ∞)
      ≤ (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * w ^ k).order)
    (z : L) (hz : ‖z‖ < ρ) :
    ‖∑' n, PowerSeries.coeff n F * z ^ n‖ ≤ M * (S.map fun w => ‖z - w‖ / ρ).prod := by
  induction S using Multiset.induction_on generalizing F M with
  | empty =>
    simpa using (summable_and_norm_tsum_coeff_mul_pow_le F hρ hF z hz).2
  | cons w S ih =>

    have hw : ‖w‖ < ρ := hS1 w (Multiset.mem_cons_self w S)
    have hord : (1 : ℕ∞) ≤ (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * w ^ k).order := by
      have h := hS w (Multiset.mem_cons_self w S)
      rw [Multiset.count_cons_self] at h
      exact le_trans (by exact_mod_cast Nat.le_add_left 1 _) h
    have hFw : ∑' k, PowerSeries.coeff k F * w ^ k = 0 := by
      rw [← coeff_zero_taylorShift F w]
      exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_one) hord)

    obtain ⟨H, hFH, hH⟩ := exists_eq_X_sub_C_mul_of_tsum_eq_zero F hρ hF w hw hFw
    have hH' : ∀ n, ‖PowerSeries.coeff n H‖ * ρ ^ n ≤ M / ρ := by
      intro n
      rw [le_div_iff₀ hρ, mul_assoc, ← pow_succ]
      exact hH n

    have hlin := fun (w' : L) (hw' : ‖w'‖ < ρ) =>
      taylorShift_mul (PowerSeries.X - PowerSeries.C w) H hρ (l1_bound_X_sub_C w hρ.le) hH' w' hw'
    have hS' : ∀ w' ∈ S, (S.count w' : ℕ∞) ≤ (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) H * ((n + k).choose n : L) * w' ^ k).order := by
      intro w' hw'S
      have hw' : ‖w'‖ < ρ := hS1 w' (Multiset.mem_cons_of_mem hw'S)
      have h := hS w' (Multiset.mem_cons_of_mem hw'S)
      rw [hFH, hlin w' hw', taylorShift_X_sub_C, l1_order_C_add_X_mul] at h
      by_cases hww : w' = w
      · subst hww
        rw [Multiset.count_cons_self, sub_self, if_pos rfl] at h
        push_cast at h
        rw [add_comm] at h
        exact (WithTop.add_le_add_iff_left WithTop.one_ne_top).mp h
      · rw [Multiset.count_cons_of_ne hww, if_neg (sub_ne_zero.mpr hww : w' - w ≠ 0), zero_add] at h
        exact h
    have hS1' : ∀ w' ∈ S, ‖w'‖ < ρ := fun w' hw' => hS1 w' (Multiset.mem_cons_of_mem hw')
    have hIH := ih H hH' hS1' hS'

    have hev : ∑' n, PowerSeries.coeff n F * z ^ n = (z - w) * ∑' n, PowerSeries.coeff n H * z ^ n := by
      rw [hFH, tsum_coeff_mul_mul_pow_eq_of_norm_lt _ _ hρ (l1_bound_X_sub_C w hρ.le) hH' z hz,
        l1_tsum_X_sub_C]
    rw [hev, norm_mul, Multiset.map_cons, Multiset.prod_cons]
    have hM : 0 ≤ M := l1_M_nonneg F hF
    calc ‖z - w‖ * ‖∑' n, PowerSeries.coeff n H * z ^ n‖
        ≤ ‖z - w‖ * (M / ρ * (S.map fun w => ‖z - w‖ / ρ).prod) := by gcongr
      _ = M * (‖z - w‖ / ρ * (S.map fun w => ‖z - w‖ / ρ).prod) := by
          field_simp

#print axioms solution

end S_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod
end P2MW
export P2MW.S_PowerSeries_norm_tsum_coeff_mul_pow_le_mul_prod (solution)
