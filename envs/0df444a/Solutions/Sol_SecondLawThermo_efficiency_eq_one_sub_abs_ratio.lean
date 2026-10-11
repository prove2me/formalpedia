-- Prove2me | solution 1 for SecondLawThermo.efficiency_eq_one_sub_abs_ratio
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:56:06.670318+00:00
-- url     : https://prove2.me/submissions/d68739c2-3b32-4734-9cc2-ac52c0721c1a

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

open SecondLawThermo
local notation "Cycle" => SecondLawThermo.Cycle

namespace CarnotAux

variable {Θ : Type*}

@[simp] theorem work_add (c d : Cycle Θ) : work (c + d) = work c + work d := by
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem work_single (h : Θ) (r : ℝ) : work (Finsupp.single h r) = r := by
  simp [work]

@[simp] theorem work_smul (r : ℝ) (c : Cycle Θ) : work (r • c) = r * work c := by
  unfold work
  rw [Finsupp.sum_smul_index (fun _ => rfl)]
  simp [Finsupp.sum, Finset.mul_sum]

@[simp] theorem work_neg (c : Cycle Θ) : work (-c) = -work c := by
  simpa using work_smul (-1) c

theorem between_eq (c : Cycle Θ) (h k : Θ) (hhk : h ≠ k)
    (hc : OperatesBetween c h k) :
    c = Finsupp.single h (c h) + Finsupp.single k (c k) := by
  classical
  ext t
  by_cases hth : t = h
  · subst t; simp [hhk, Ne.symm hhk]
  by_cases htk : t = k
  · subst t; simp [hhk, Ne.symm hhk]
  simp [hc t hth htk, Finsupp.single_apply, hth, htk, Ne.symm hth, Ne.symm htk]

theorem work_between (c : Cycle Θ) (h k : Θ) (hhk : h ≠ k)
    (hc : OperatesBetween c h k) : work c = c h + c k := by
  calc
    work c = work (Finsupp.single h (c h) + Finsupp.single k (c k)) :=
      congrArg work (between_eq c h k hhk hc)
    _ = c h + c k := by simp

theorem between_add {c d : Cycle Θ} {h k : Θ}
    (hc : OperatesBetween c h k) (hd : OperatesBetween d h k) :
    OperatesBetween (c + d) h k := by
  intro t hth htk
  simp [hc t hth htk, hd t hth htk]

theorem between_smul (r : ℝ) {c : Cycle Θ} {h k : Θ}
    (hc : OperatesBetween c h k) : OperatesBetween (r • c) h k := by
  intro t hth htk
  simp [hc t hth htk]

theorem between_neg {c : Cycle Θ} {h k : Θ}
    (hc : OperatesBetween c h k) : OperatesBetween (-c) h k := by
  intro t hth htk
  simp [hc t hth htk]

theorem between_ext {c d : Cycle Θ} {h k : Θ}
    (hc : OperatesBetween c h k) (hd : OperatesBetween d h k)
    (hh : c h = d h) (hk : c k = d k) : c = d := by
  ext t
  by_cases hth : t = h
  · simpa [hth] using hh
  by_cases htk : t = k
  · simpa [htk] using hk
  rw [hc t hth htk, hd t hth htk]

end CarnotAux

theorem solution {Θ : Type*} (c : Cycle Θ) (h k : Θ) (hhk : h ≠ k)
    (hc : OperatesBetween c h k) (hqH : 0 < c h) (hqC : c k < 0) :
    efficiency c h = 1 - |c k| / |c h| := by
  rw [efficiency, CarnotAux.work_between c h k hhk hc,
    abs_of_pos hqH, abs_of_neg hqC]
  field_simp
  ring
