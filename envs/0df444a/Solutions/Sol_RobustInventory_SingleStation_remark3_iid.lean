-- Prove2me | solution 1 for RobustInventory.SingleStation.remark3_iid
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:23:40.258317+00:00
-- url     : https://prove2.me/submissions/68d47057-70be-4fed-ad36-fbff623098bb

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation

namespace RobustInventory.SingleStation.D4825110

open Finset RobustInventory.SingleStation

theorem gamma_le (M : Model) (hΓ01 : M.Γ 0 ≤ 1) : ∀ k : ℕ, M.Γ k ≤ (k : ℝ) + 1 := by
  intro k
  induction k with
  | zero => simpa using hΓ01
  | succ n ih =>
    have := M.hΓstep n
    push_cast
    linarith

theorem gamma_nonneg (M : Model) : ∀ k : ℕ, 0 ≤ M.Γ k := by
  intro k
  induction k with
  | zero => exact M.hΓ0
  | succ n ih => exact le_trans ih (M.hΓmono n)

theorem A_eq (M : Model) (wh : ℝ) (hwhat : ∀ k, M.what k = wh) (hΓ01 : M.Γ 0 ≤ 1) (k : ℕ) :
    M.A k = wh * M.Γ k := by
  have hwh : 0 ≤ wh := by rw [← hwhat 0]; exact M.hwhat 0
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hG := gamma_le M hΓ01 k
  have hG0 := gamma_nonneg M k
  unfold Model.A
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => M.Γ k / ((k : ℝ) + 1), ⟨?_, ?_⟩, ?_⟩
    · intro i _
      refine ⟨div_nonneg hG0 hk.le, ?_⟩
      rw [div_le_one hk]; exact hG
    · simp only [sum_const, card_range, nsmul_eq_mul]
      push_cast
      rw [mul_div_cancel₀ _ hk.ne']
    · simp only [hwhat, sum_const, card_range, nsmul_eq_mul]
      push_cast
      field_simp
  · rintro v ⟨z, ⟨_, hsum⟩, rfl⟩
    simp only [hwhat]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hsum hwh

end RobustInventory.SingleStation.D4825110

open RobustInventory.SingleStation in
theorem solution (M : Model) (wb wh : ℝ) (hwbar : ∀ k, M.wbar k = wb)
    (hwhat : ∀ k, M.what k = wh) (hΓ01 : M.Γ 0 ≤ 1) :
    (∀ k, M.A k = wh * M.Γ k) ∧
    M.wmod 0 = wb + (M.p - M.h) / (M.p + M.h) * wh * M.Γ 0 ∧
    (∀ k, M.wmod (k + 1) = wb + (M.p - M.h) / (M.p + M.h) * wh * (M.Γ (k + 1) - M.Γ k)) := by
  have hA := RobustInventory.SingleStation.D4825110.A_eq M wh hwhat hΓ01
  refine ⟨hA, ?_, ?_⟩
  · simp only [Model.wmod, Model.Aprev, hwbar, hA]
    ring
  · intro k
    simp only [Model.wmod, Model.Aprev, hwbar, hA]
    ring
