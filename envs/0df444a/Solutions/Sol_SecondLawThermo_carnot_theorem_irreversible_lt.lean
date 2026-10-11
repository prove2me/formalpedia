-- Prove2me | solution 1 for SecondLawThermo.carnot_theorem_irreversible_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:38:38.717983+00:00
-- url     : https://prove2.me/submissions/9250486f-e96d-40c5-919d-a184286d4c90

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

private theorem work_two_reservoirs {Θ : Type*} [LinearOrder Θ]
    (c : SecondLawThermo.Cycle Θ) (h k : Θ) (hkh : k < h)
    (hbetween : OperatesBetween c h k) :
    work c = c h + c k := by
  classical
  have hne : h ≠ k := ne_of_gt hkh
  have hc : c = Finsupp.single h (c h) + Finsupp.single k (c k) := by
    ext t
    by_cases hth : t = h
    · subst t
      simp [hne]
    · by_cases htk : t = k
      · subst t
        simp [hne]
      · simp [hth, htk, hbetween t hth htk]
  rw [hc]
  simp [work, Finsupp.sum_single_add_single, ne_of_gt hkh]

theorem solution {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (SecondLawThermo.Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCl : ClausiusStatement 𝒞) (h k : Θ) (hkh : k < h)
    (e : SecondLawThermo.Cycle Θ) (he : IsCarnotEngine 𝒞 e h k) (c : SecondLawThermo.Cycle Θ) (hc : c ∈ 𝒞)
    (hirr : -c ∉ 𝒞) (hcb : OperatesBetween c h k) (hqH : 0 < c h) :
    efficiency c h < efficiency e h := by
  classical
  rcases he with ⟨hrev, hbetween, hhot, hcold, hwork⟩
  rcases hrev with ⟨hemem, hnegmem⟩
  have hehot : 0 < e h := hhot
  have hecold : e k < 0 := hcold
  have hework : 0 < work e := hwork
  by_cases hcwork_pos : 0 < work c
  · let d : SecondLawThermo.Cycle Θ := (work e) • c + (work c) • (-e)
    have hdmem : d ∈ 𝒞 := by
      apply h𝒞.add_mem
      · exact h𝒞.smul_mem (work e) c hework.le hc
      · exact h𝒞.smul_mem (work c) (-e) hcwork_pos.le hnegmem
    have hdbetween : OperatesBetween d h k := by
      intro t hth htk
      simp [d, hcb t hth htk, hbetween t hth htk]
    have hwc : work c = c h + c k := work_two_reservoirs c h k hkh hcb
    have hwe : work e = e h + e k := work_two_reservoirs e h k hkh hbetween
    have hdwork : work d = 0 := by
      rw [work_two_reservoirs d h k hkh hdbetween]
      calc
        d h + d k = work e * (c h + c k) + work c * (-(e h + e k)) := by
          simp [d]
          ring
        _ = work e * work c + work c * (-work e) := by rw [← hwc, ← hwe]
        _ = 0 := by ring
    have hdcold := hCl h k hkh d hdmem hdbetween hdwork
    have hdcold' : work e * c k - work c * e k ≤ 0 := by
      simpa [d] using hdcold
    have hcross : c h * (-e k) ≤ e h * (-c k) := by
      rw [hwc, hwe] at hdcold'
      nlinarith
    have hratio : (-e k) / e h ≤ (-c k) / c h := by
      rw [div_le_div_iff₀ hehot hqH]
      simpa [mul_comm] using hcross
    have hratio_strict : (-e k) / e h < (-c k) / c h := by
      by_contra hn
      have hrev : (-c k) / c h ≤ (-e k) / e h := by
        simpa using le_of_not_gt hn
      have heq : (-e k) / e h = (-c k) / c h := le_antisymm hratio hrev
      have hcross_eq : c h * (-e k) = e h * (-c k) := by
        field_simp [ne_of_gt hehot, ne_of_gt hqH] at heq
        nlinarith
      have hdval : d k = work e * c k - work c * e k := by
        simp [d]
        ring
      have hdkzero : d k = 0 := by
        rw [hdval, hwc, hwe]
        nlinarith
      have hwd : work d = d h + d k := work_two_reservoirs d h k hkh hdbetween
      have hdhzero : d h = 0 := by
        rw [hwd] at hdwork
        rw [hdkzero] at hdwork
        linarith
      have hdzero : d = 0 := by
        ext t
        by_cases hth : t = h
        · subst t
          simpa using hdhzero
        · by_cases htk : t = k
          · subst t
            simpa using hdkzero
          · simp [d, hcb t hth htk, hbetween t hth htk]
      let scale : ℝ := work c / work e
      have hscale_pos : 0 < scale := div_pos hcwork_pos hework
      have hscale_mul : work e * scale = work c := by
        dsimp [scale]
        field_simp [ne_of_gt hework]
      have hscaled_cycle : -c = scale • (-e) := by
        ext t
        have hdt : work e * c t - work c * e t = 0 := by
          have hz := congrArg (fun x : SecondLawThermo.Cycle Θ => x t) hdzero
          have hz' : work e * c t + work c * (-e t) = 0 := by
            change work e * c t + work c * (-e t) = 0 at hz
            exact hz
          nlinarith [hz']
        have hmul : work e * c t = work e * (scale * e t) := by
          calc
            work e * c t = work c * e t := by nlinarith [hdt]
            _ = (work e * scale) * e t := by rw [hscale_mul]
            _ = work e * (scale * e t) := by ring
        have hpoint : c t = scale * e t :=
          mul_left_cancel₀ (ne_of_gt hework) hmul
        change -(c t) = scale * (-(e t))
        rw [hpoint]
        ring
      have hnegc : -c ∈ 𝒞 := by
        rw [hscaled_cycle]
        exact h𝒞.smul_mem scale (-e) hscale_pos.le hnegmem
      exact (hirr hnegc).elim
    have heff_e : efficiency e h = 1 - ((-e k) / e h) := by
      unfold efficiency
      rw [hwe]
      field_simp [ne_of_gt hehot]
      ring
    have heff_c : efficiency c h = 1 - ((-c k) / c h) := by
      unfold efficiency
      rw [hwc]
      field_simp [ne_of_gt hqH]
      ring
    rw [heff_e, heff_c]
    linarith
  · have hcwork : work c ≤ 0 := le_of_not_gt hcwork_pos
    have hc_eff : efficiency c h ≤ 0 := by
      unfold efficiency
      exact div_nonpos_of_nonpos_of_nonneg hcwork hqH.le
    have he_eff : 0 < efficiency e h := by
      unfold efficiency
      exact div_pos hework hehot
    exact lt_of_le_of_lt hc_eff he_eff
