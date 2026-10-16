-- Prove2me | solution 1 for SecondLawThermo.work_two_reservoirs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:40:32.700687+00:00
-- url     : https://prove2.me/submissions/a9e96dc5-17f9-4637-bc63-8ebf105e9ffb

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

theorem solution {Θ : Type*} [LinearOrder Θ]
    (c : SecondLawThermo.Cycle Θ) (h k : Θ) (hkh : k < h)
    (hbetween : SecondLawThermo.OperatesBetween c h k) :
    SecondLawThermo.work c = c h + c k := by
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
