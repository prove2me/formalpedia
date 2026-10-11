-- Prove2me | solution 1 for SecondLawThermo.carnot_theorem_efficiency_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:26:35.899738+00:00
-- url     : https://prove2.me/submissions/821c6d92-561f-44b2-8870-c0f181b71b0a

import Definitions.Def_SecondLawThermo_Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
    (hcb : OperatesBetween c h k) (hqH : 0 < c h) :
    efficiency c h ≤ efficiency e h := by
  classical
  rcases he with ⟨hrev, hbetween, hhot, hcold, hwork⟩
  rcases hrev with ⟨hemem, hnegmem⟩
  have hehot : 0 < e h := hhot
  have hecold : e k < 0 := hcold
  have hework : 0 < work e := hwork
  by_cases hcwork_nonpos : work c ≤ 0
  · have hc_eff : efficiency c h ≤ 0 := by
      unfold efficiency
      exact div_nonpos_of_nonpos_of_nonneg hcwork_nonpos hqH.le
    have he_eff : 0 < efficiency e h := by
      unfold efficiency
      exact div_pos hework hehot
    exact le_trans hc_eff he_eff.le
  · have hcwork_pos : 0 < work c := lt_of_not_ge hcwork_nonpos
    let d : SecondLawThermo.Cycle Θ := (work e) • c + (work c) • (-e)
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
    linarith [hratio]
