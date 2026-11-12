-- Prove2me | solution 1 for PGDMap20261031.step_two_updates
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T14:29:05.404214+00:00
-- url     : https://prove2.me/submissions/a9e2b253-ee98-4292-b0c0-6a5a8ee24e13

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Stepsize

open PGDMap20261031

private lemma crossing_two (q h : ℝ) (hq : 0 ≤ q) (hh : 1 < h ∧ h < 2) :
    branchA 2 h q = branchB 2 h q ↔ q * h ^ 2 + 2 * (1 - q) * h - 3 = 0 := by
  have hhpos : 0 < h := by linarith [hh.1]
  have hb : 1 ≤ base h q := by unfold base; nlinarith
  have hbpos : 0 < base h q := by linarith
  have ht : 0 < h - 1 := by linarith [hh.1]
  have htlt : h - 1 < 1 := by linarith [hh.2]
  have ht4 : (h - 1) ^ 4 < 1 := pow_lt_one₀ ht.le htlt (by norm_num)
  have hb4 : 1 ≤ (base h q) ^ 4 := one_le_pow₀ hb
  have hdb : 0 < (base h q) ^ 4 - (1 - h) ^ 4 := by
    nlinarith [show (1 - h) ^ 4 = (h - 1) ^ 4 by ring]
  by_cases hqzero : q = 0
  · subst q
    have hda : 0 < h * (4 - h) := by nlinarith [hh.1, hh.2]
    simp only [branchA, branchB, base, if_pos rfl]
    norm_num
    rw [div_eq_div_iff (ne_of_gt hda) (by simpa [base] using ne_of_gt hdb)]
    have hid : 2 * (1 - (1 - h) ^ 4) - 2 * (1 - h) ^ 2 * (h * (4 - h)) =
        -2 * h ^ 2 * (2 * h - 3) := by ring
    constructor
    · intro heq
      have hzero : h ^ 2 * (2 * h - 3) = 0 := by nlinarith only [heq, hid]
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hhpos.ne')
    · intro hroot
      nlinarith only [hroot, hid]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqzero)
    have hpow : (base h q) ^ 2 ≤ (base h q) ^ 4 := pow_le_pow_right₀ hb (by norm_num)
    have hda : 0 < (base h q) ^ 4 - 1 - h ^ 2 * q := by
      have hinner : 0 < 2 - h + h * q := by nlinarith [hh.2]
      have hprod := mul_pos (mul_pos hhpos hqpos) hinner
      dsimp [base] at hpow ⊢
      nlinarith only [hpow, hprod]
    simp only [branchA, branchB, if_neg hqzero]
    norm_num
    rw [div_eq_div_iff (ne_of_gt hda) (ne_of_gt hdb)]
    let P := q * h ^ 2 + 2 * (1 - q) * h - 3
    have hid : 2 * q * ((base h q) ^ 4 - (1 - h) ^ 4) -
        2 * (1 + q) * (1 - h) ^ 2 * ((base h q) ^ 4 - 1 - h ^ 2 * q) =
        (-2 * h ^ 2 * q * (1 + q) * (base h q) ^ 2) * P := by
      dsimp [base, P]
      ring
    have hfactor : -2 * h ^ 2 * q * (1 + q) * (base h q) ^ 2 ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (pow_ne_zero 2 hhpos.ne')) hqzero) (by linarith)) (pow_ne_zero 2 hbpos.ne')
    constructor
    · intro heq
      have hzero : (-2 * h ^ 2 * q * (1 + q) * (base h q) ^ 2) * P = 0 := by
        linarith only [heq, hid]
      exact (mul_eq_zero.mp hzero).resolve_left hfactor
    · intro hroot
      have : P = 0 := hroot
      rw [this, mul_zero] at hid
      linarith only [hid]

theorem solution : TwoUpdateFormulaClaim := by
  intro q hq
  let H : ℝ := if q = 0 then 3 / 2 else (q - 1 + Real.sqrt (q ^ 2 + q + 1)) / q
  have hH : 1 < H ∧ H < 2 := by
    by_cases hz : q = 0
    · norm_num [H, hz]
    · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
      have hs := Real.sqrt_nonneg (q ^ 2 + q + 1)
      have hsq := Real.sq_sqrt (by nlinarith [sq_nonneg q] : 0 ≤ q ^ 2 + q + 1)
      dsimp [H]
      rw [if_neg hz]
      constructor
      · apply (lt_div_iff₀ hqp).2
        nlinarith
      · apply (div_lt_iff₀ hqp).2
        nlinarith
  have hHP : q * H ^ 2 + 2 * (1 - q) * H - 3 = 0 := by
    by_cases hz : q = 0
    · norm_num [H, hz]
    · have hsq := Real.sq_sqrt (by nlinarith [sq_nonneg q] : 0 ≤ q ^ 2 + q + 1)
      dsimp [H]
      rw [if_neg hz]
      generalize hs : Real.sqrt (q ^ 2 + q + 1) = s at hsq ⊢
      field_simp [hz]
      nlinarith only [hsq]
  have huniq (h : ℝ) (hh : 1 < h ∧ h < 2)
      (hp : q * h ^ 2 + 2 * (1 - q) * h - 3 = 0) : h = H := by
    have hfactor : 0 < q * (h + H) + 2 * (1 - q) := by
      have := mul_nonneg hq (by linarith [hh.1, hH.1] : 0 ≤ h + H - 2)
      nlinarith
    have heq : (h - H) * (q * (h + H) + 2 * (1 - q)) = 0 := by
      nlinarith only [hp, hHP]
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hfactor.ne')
  have hset : {h : ℝ | 1 < h ∧ h < 2 ∧ branchA 2 h q = branchB 2 h q} = {H} := by
    ext h
    constructor
    · rintro ⟨hlo, hhi, heq⟩
      exact huniq h ⟨hlo, hhi⟩ ((crossing_two q h hq ⟨hlo, hhi⟩).mp heq)
    · intro heq
      have : h = H := heq
      subst h
      exact ⟨hH.1, hH.2, (crossing_two q H hq hH).mpr hHP⟩
  change sInf {h : ℝ | 1 < h ∧ h < 2 ∧ branchA 2 h q = branchB 2 h q} = H
  rw [hset, csInf_singleton]
