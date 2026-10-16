-- Prove2me | solution 1 for SecondLawThermo.same_reservoir_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:44:22.68304+00:00
-- url     : https://prove2.me/submissions/abd6f6f5-34ec-4a63-b486-f00bde8ec6dc

import Definitions.Def_SecondLawThermo_Defs
import Mathlib
import Theorems.Thm_SecondLawThermo_work_two_reservoirs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

theorem solution {Θ : Type*} [LinearOrder Θ]
    (𝒞 : Set (SecondLawThermo.Cycle Θ)) (h𝒞 : SecondLawThermo.IsCycleCone 𝒞)
    (hCl : SecondLawThermo.ClausiusStatement 𝒞) (h k : Θ) (hkh : k < h)
    (e e' : SecondLawThermo.Cycle Θ)
    (he : SecondLawThermo.IsCarnotEngine 𝒞 e h k) (he' : SecondLawThermo.IsCarnotEngine 𝒞 e' h k) :
    (-e k) / e h = (-e' k) / e' h := by
  classical
  rcases he with ⟨⟨hemem, hnegmem⟩, hbetween, hhot, hcold, hwork⟩
  rcases he' with ⟨⟨hemem', hnegmem'⟩, hbetween', hhot', hcold', hwork'⟩
  let d : SecondLawThermo.Cycle Θ := (work e') • e + (work e) • (-e')
  let d' : SecondLawThermo.Cycle Θ := (work e') • (-e) + (work e) • e'
  have hdmem : d ∈ 𝒞 := by
    apply h𝒞.add_mem
    · exact h𝒞.smul_mem (work e') e hwork'.le hemem
    · exact h𝒞.smul_mem (work e) (-e') hwork.le hnegmem'
  have hd'mem : d' ∈ 𝒞 := by
    apply h𝒞.add_mem
    · exact h𝒞.smul_mem (work e') (-e) hwork'.le hnegmem
    · exact h𝒞.smul_mem (work e) e' hwork.le hemem'
  have hdbetween : OperatesBetween d h k := by
    intro t hth htk
    simp [d, hbetween t hth htk, hbetween' t hth htk]
  have hd'between : OperatesBetween d' h k := by
    intro t hth htk
    simp [d', hbetween t hth htk, hbetween' t hth htk]
  have hwe : work e = e h + e k := SecondLawThermo.work_two_reservoirs e h k hkh hbetween
  have hwe' : work e' = e' h + e' k := SecondLawThermo.work_two_reservoirs e' h k hkh hbetween'
  have hdwork : work d = 0 := by
    rw [SecondLawThermo.work_two_reservoirs d h k hkh hdbetween]
    calc
      d h + d k = work e' * (e h + e k) + work e * (-(e' h + e' k)) := by
        simp [d]
        ring
      _ = work e' * work e + work e * (-work e') := by rw [← hwe, ← hwe']
      _ = 0 := by ring
  have hd'work : work d' = 0 := by
    rw [SecondLawThermo.work_two_reservoirs d' h k hkh hd'between]
    calc
      d' h + d' k = work e' * (-(e h + e k)) + work e * (e' h + e' k) := by
        simp [d']
        ring
      _ = work e' * (-work e) + work e * work e' := by rw [← hwe, ← hwe']
      _ = 0 := by ring
  have hdcold := hCl h k hkh d hdmem hdbetween hdwork
  have hd'cold := hCl h k hkh d' hd'mem hd'between hd'work
  have hcross₁ : e h * (-e' k) ≤ e' h * (-e k) := by
    have hineq : work e' * e k - work e * e' k ≤ 0 := by
      simpa [d] using hdcold
    rw [hwe, hwe'] at hineq
    nlinarith
  have hcross₂ : e' h * (-e k) ≤ e h * (-e' k) := by
    have hineq : -(work e') * e k + work e * e' k ≤ 0 := by
      simpa [d'] using hd'cold
    rw [hwe, hwe'] at hineq
    nlinarith
  have hcross : e h * (-e' k) = e' h * (-e k) := le_antisymm hcross₁ hcross₂
  field_simp [ne_of_gt hhot, ne_of_gt hhot']
  nlinarith
