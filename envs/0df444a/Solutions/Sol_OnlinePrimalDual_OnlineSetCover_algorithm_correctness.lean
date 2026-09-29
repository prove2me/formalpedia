-- Prove2me | solution 1 for OnlinePrimalDual.OnlineSetCover.algorithm_correctness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:22:00.366423+00:00
-- url     : https://prove2.me/submissions/6db0ce5e-2f8b-4d95-b74f-1347b3ce9dcb

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential

namespace OnlinePrimalDual.OnlineSetCover

theorem opd_main {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α β : ℝ) (hα_pos : 0 < α) (hβ_nonneg : 0 ≤ β)
    (w : T → ℝ) (hw_nonneg : ∀ t, 0 ≤ w t) (C : Finset T)
    (hE : 1 ≤ Fintype.card E)
    (hfrac : ∑ t : T, w t * inst.c t ≤ β * α)
    (hΦ_bound : potential inst w C α < (Fintype.card E : ℝ) ^ 2) :
    (∀ e : E, 1 ≤ elementWeight inst w e → coveredBy inst C e) ∧
    (∑ t ∈ C, inst.c t ≤ α * Real.log (Fintype.card E : ℝ) * (3 * β + 2)) := by
  classical
  set n : ℝ := (Fintype.card E : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hE
  have hn0 : 0 < n := by linarith
  set X : ℝ := (1 / (2 * α)) *
      ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0) - 3 * w t * inst.c t * Real.log n)
    with hX
  set S1 : ℝ := ∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e),
      n ^ (2 * elementWeight inst w e) with hS1
  have hΦ : potential inst w C α = S1 + n * Real.exp X := by
    simp only [potential, hS1, hX, hn]
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun e _ => Real.rpow_nonneg hn0.le _
  have hexp : 0 < n * Real.exp X := mul_pos hn0 (Real.exp_pos X)
  rw [hΦ] at hΦ_bound
  refine ⟨fun e he => ?_, ?_⟩
  · by_contra hcov
    have hmem : e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e) := by simp [hcov]
    have h1 : n ^ (2 * elementWeight inst w e) ≤ S1 :=
      Finset.single_le_sum (f := fun e => n ^ (2 * elementWeight inst w e))
        (fun e _ => Real.rpow_nonneg hn0.le _) hmem
    have h2 : n ^ (2 : ℝ) ≤ n ^ (2 * elementWeight inst w e) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [Real.rpow_two] at h2
    linarith
  · have h1 : n * Real.exp X < n ^ 2 := by linarith
    have h2 : Real.exp X < n := by
      rw [pow_two] at h1
      exact lt_of_mul_lt_mul_left h1 hn0.le
    have h3 : X < Real.log n := by
      rw [← Real.exp_lt_exp, Real.exp_log hn0]; exact h2
    have hsumC : ∑ t : T, inst.c t * (if t ∈ C then (1 : ℝ) else 0) = ∑ t ∈ C, inst.c t := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hsplit : ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0)
        - 3 * w t * inst.c t * Real.log n) =
        ∑ t ∈ C, inst.c t - 3 * Real.log n * ∑ t : T, w t * inst.c t := by
      rw [Finset.sum_sub_distrib, hsumC, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by ring
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    have h4 : ∑ t ∈ C, inst.c t - 3 * Real.log n * ∑ t : T, w t * inst.c t < 2 * α * Real.log n := by
      have h5 : X * (2 * α) = ∑ t ∈ C, inst.c t - 3 * Real.log n * ∑ t : T, w t * inst.c t := by
        rw [hX, hsplit]; field_simp
      have h6 : X * (2 * α) < Real.log n * (2 * α) := mul_lt_mul_of_pos_right h3 (by linarith)
      linarith
    have h7 : 3 * Real.log n * ∑ t : T, w t * inst.c t ≤ 3 * Real.log n * (β * α) :=
      mul_le_mul_of_nonneg_left hfrac (by linarith)
    nlinarith

end OnlinePrimalDual.OnlineSetCover

open OnlinePrimalDual.OnlineSetCover

theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α β : ℝ) (hα_pos : 0 < α) (hβ_nonneg : 0 ≤ β)
    (w : T → ℝ) (hw_nonneg : ∀ t, 0 ≤ w t) (C : Finset T)
    (hE : 1 ≤ Fintype.card E)
    (hfrac : ∑ t : T, w t * inst.c t ≤ β * α)
    (hΦ_bound : potential inst w C α < (Fintype.card E : ℝ) ^ 2) :
    (∀ e : E, 1 ≤ elementWeight inst w e → coveredBy inst C e) ∧
    (∑ t ∈ C, inst.c t ≤ α * Real.log (Fintype.card E : ℝ) * (3 * β + 2)) := by
  exact opd_main inst α β hα_pos hβ_nonneg w hw_nonneg C hE hfrac hΦ_bound
