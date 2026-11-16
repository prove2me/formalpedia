-- Prove2me | solution 1 for PNormRegLib.run_mem_outside
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:16:00.526063+00:00
-- url     : https://prove2.me/submissions/9ac0888f-4e69-4550-972c-db9bf3033697

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_PNormRegLib_AddressBound
import Theorems.Thm_PNormRegLib_step_eq_exec
import Theorems.Thm_PNormRegLib_bounded_run

open PNormReg PNormRegLib

theorem solution (P : Program) (ω : ℕ → Bool) (X : ℤ) (s : State) (hs : PBounded X s)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (y : ℤ) (hy : X * 2 ^ t < |y|) :
    (run P s ω t).core.mem y = s.core.mem y ∧
      (run P s ω t).integerMemory y = s.integerMemory y := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    have hpow : X * 2 ^ t ≤ X * 2 ^ (t + 1) := by
      rw [pow_succ]; nlinarith [one_le_pow₀ (M₀ := ℤ) (a := 2) (n := t) (by norm_num)]
    obtain ⟨ih1, ih2⟩ := ih (lt_of_le_of_lt hpow hy)
    have hb := bounded_run P ω X s hs hlit hX t
    set u := run P s ω t with hu
    have e : run P s ω (t + 1) = step P ω u := by
      simp only [hu, run, Function.iterate_succ_apply']
    rw [e, ← ih1, ← ih2]
    have hne : ∀ q, u.core.ptrs q ≠ y := by
      intro q hq; have := hb.1 q; rw [hq] at this; linarith
    by_cases hh : u.halted = true
    · simp [step, hh]
    · simp only [Bool.not_eq_true] at hh
      cases h : P[u.core.pc]? with
      | none => simp [step, hh, h]
      | some ins =>
        rw [step_eq_exec P ω u ins hh h]
        cases ins with
        | core i =>
          cases i with
          | store q i => simp [exec, coreExec, Function.update_apply, Ne.symm (hne q)]
          | jle i t => simp only [exec, coreExec]; split_ifs <;> simp
          | pjle q q' t => simp only [exec, coreExec]; split_ifs <;> simp
          | _ => simp [exec, coreExec]
        | integerStore a b => simp [exec, Function.update_apply, Ne.symm (hne a)]
        | _ => simp [exec]
