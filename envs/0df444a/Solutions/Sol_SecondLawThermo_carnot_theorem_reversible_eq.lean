-- Prove2me | solution 1 for SecondLawThermo.carnot_theorem_reversible_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:30:40.691268+00:00
-- url     : https://prove2.me/submissions/5413c758-3378-45ad-ad9e-3c9f70dd6618

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
    (e e' : SecondLawThermo.Cycle Θ) (he : IsCarnotEngine 𝒞 e h k) (he' : IsCarnotEngine 𝒞 e' h k) :
    efficiency e h = efficiency e' h := by
  classical
  rcases he with ⟨hrev, hbetween, hhot, hcold, hwork⟩
  rcases he' with ⟨hrev', hbetween', hhot', hcold', hwork'⟩
  rcases hrev with ⟨hemem, hnegmem⟩
  rcases hrev' with ⟨hemem', hnegmem'⟩
  have hehot : 0 < e h := hhot
  have he'hot : 0 < e' h := hhot'
  have hework : 0 < work e := hwork
  have he'work : 0 < work e' := hwork'
  let d : SecondLawThermo.Cycle Θ := (work e') • e + (work e) • (-e')
  let d' : SecondLawThermo.Cycle Θ := (work e') • (-e) + (work e) • e'
  have hdmem : d ∈ 𝒞 := by
    apply h𝒞.add_mem
    · exact h𝒞.smul_mem (work e') e he'work.le hemem
    · exact h𝒞.smul_mem (work e) (-e') hework.le hnegmem'
  have hd'mem : d' ∈ 𝒞 := by
    apply h𝒞.add_mem
    · exact h𝒞.smul_mem (work e') (-e) he'work.le hnegmem
    · exact h𝒞.smul_mem (work e) e' hework.le hemem'
  have hdbetween : OperatesBetween d h k := by
    intro t hth htk
    simp [d, hbetween t hth htk, hbetween' t hth htk]
  have hd'between : OperatesBetween d' h k := by
    intro t hth htk
    simp [d', hbetween t hth htk, hbetween' t hth htk]
  have hwe : work e = e h + e k := work_two_reservoirs e h k hkh hbetween
  have hwe' : work e' = e' h + e' k := work_two_reservoirs e' h k hkh hbetween'
  have hdwork : work d = 0 := by
    rw [work_two_reservoirs d h k hkh hdbetween]
    calc
      d h + d k = work e' * (e h + e k) + work e * (-(e' h + e' k)) := by
        simp [d]
        ring
      _ = work e' * work e + work e * (-work e') := by rw [← hwe, ← hwe']
      _ = 0 := by ring
  have hd'work : work d' = 0 := by
    rw [work_two_reservoirs d' h k hkh hd'between]
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
  have hratio : (-e k) / e h = (-e' k) / e' h := by
    field_simp [ne_of_gt hehot, ne_of_gt he'hot]
    nlinarith
  have heff : efficiency e h = 1 - ((-e k) / e h) := by
    unfold efficiency
    rw [hwe]
    field_simp [ne_of_gt hehot]
    ring
  have heff' : efficiency e' h = 1 - ((-e' k) / e' h) := by
    unfold efficiency
    rw [hwe']
    field_simp [ne_of_gt he'hot]
    ring
  rw [heff, heff', hratio]
