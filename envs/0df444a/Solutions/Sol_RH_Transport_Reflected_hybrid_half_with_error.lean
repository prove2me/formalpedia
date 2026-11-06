-- Prove2me | solution 1 for RH.Transport.Reflected.hybrid_half_with_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:39.455199+00:00
-- url     : https://prove2.me/submissions/fd81fbe9-336a-4a21-80a3-18b0dea53efb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_ReflectedExponent

set_option autoImplicit false
open RH RH.Transport RH.Transport.Reflected
noncomputable section
namespace RH.Transport.Reflected
theorem _root_.solution {v za ε : ℝ} (hv : -ε ≤ v) (hε : 0 ≤ ε)
    (hu : hybridSaving v za ≠ za) : v / 2 - ε / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      have hzv := min_le_left za ((v + za) / 3)
      rw [min_eq_right hz] at hzv
      linarith
end RH.Transport.Reflected
