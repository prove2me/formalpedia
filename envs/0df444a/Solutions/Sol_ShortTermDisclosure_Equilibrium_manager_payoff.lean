-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.manager_payoff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:54:01.229684+00:00
-- url     : https://prove2.me/submissions/6eddfb16-582c-4d31-8dcd-ac0ae4f60f2a

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

open ShortTermDisclosure.Equilibrium in
theorem solution (muhi t v : ℝ) (hm : 0 < muhi)
    (ht0 : 0 ≤ t) (ht1 : t ≤ muhi) :
    managerValue muhi t v =
      (1 - t / muhi) * condMeanAbove muhi t + (t / muhi) * v ∧
    (t < muhi → condMeanAbove muhi t = (t + muhi) / 2) := by
  set f : ℝ → ℝ := fun mu => if t ≤ mu then mu else v with hf
  have hMV : managerValue muhi t v = (∫ mu in (0:ℝ)..muhi, f mu) / muhi := rfl
  have hI1 : IntervalIntegrable f MeasureTheory.volume 0 t := by
    apply (intervalIntegrable_const (c := v)).congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le ht0] at hx
    simp [hf, not_le.mpr hx.2]
  have hI2 : IntervalIntegrable f MeasureTheory.volume t muhi := by
    apply (intervalIntegral.intervalIntegrable_id).congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le ht1] at hx
    simp [hf, hx.1.le]
  have e1 : (∫ mu in (0:ℝ)..t, f mu) = t * v := by
    rw [intervalIntegral.integral_congr_Ioo_of_le ht0 (g := fun _ => v)]
    · simp
    · intro x hx
      simp [hf, not_le.mpr hx.2]
  have e2 : (∫ mu in t..muhi, f mu) = (muhi ^ 2 - t ^ 2) / 2 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le ht1 (g := fun x => x)]
    · simp [integral_id]
    · intro x hx
      simp [hf, hx.1.le]
  have hMV' : managerValue muhi t v = ((muhi ^ 2 - t ^ 2) / 2 + t * v) / muhi := by
    rw [hMV, ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, e1, e2]
    ring
  have hC : t < muhi → condMeanAbove muhi t = (t + muhi) / 2 := by
    intro hlt
    unfold condMeanAbove
    rw [if_pos hlt, integral_id]
    have : muhi - t ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨?_, hC⟩
  rw [hMV']
  rcases lt_or_eq_of_le ht1 with hlt | heq
  · rw [hC hlt]
    field_simp
    ring
  · subst heq
    unfold condMeanAbove
    rw [if_neg (lt_irrefl _)]
    field_simp
    ring
