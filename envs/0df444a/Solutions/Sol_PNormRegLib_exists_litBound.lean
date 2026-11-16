-- Prove2me | solution 1 for PNormRegLib.exists_litBound
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:13:23.122404+00:00
-- url     : https://prove2.me/submissions/027bff42-7ba5-47d3-bb60-6c621b7781b7

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound

open PNormReg PNormRegLib

namespace PNormRegLibLitAux

/-- The absolute value of the literal of a `pset`, and `0` for other instructions. -/
def litOf : Instr → ℤ
  | .core (.pset _ c) => |c|
  | _ => 0

lemma litOf_nonneg (a : Instr) : 0 ≤ litOf a := by
  unfold litOf; split <;> simp

end PNormRegLibLitAux

open PNormRegLibLitAux in
theorem solution (P : PNormReg.Program) : ∃ L : ℤ, 1 ≤ L ∧ LitBound P L := by
  induction P with
  | nil => exact ⟨1, le_rfl, fun q c h => by simp at h⟩
  | cons a P ih =>
    obtain ⟨L, hL1, hL⟩ := ih
    refine ⟨L + litOf a, by linarith [litOf_nonneg a], ?_⟩
    intro q c hc
    rcases List.mem_cons.mp hc with h | h
    · subst h; simp [litOf]; linarith
    · linarith [hL q c h, litOf_nonneg a]
