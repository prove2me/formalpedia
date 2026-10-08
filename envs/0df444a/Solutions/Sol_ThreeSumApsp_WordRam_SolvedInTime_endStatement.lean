-- Prove2me | solution 1 for ThreeSumApsp.WordRam.SolvedInTime.endStatement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T08:24:06.096093+00:00
-- url     : https://prove2.me/submissions/bd94dae3-f16d-4d78-be0c-726628063020

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/























/-! ## Configurations and single steps -/





/-! ## Runs -/













/-- Within no steps there is no verdict. -/
theorem exec_zero (c : Cfg W) : exec P 0 c.pc c.mem = none := by rw [exec]

private theorem exec_succ (t : ℕ) (c : Cfg W) : exec P (t + 1) c.pc c.mem =
    match step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => exec P t next.pc next.mem := by
  rw [exec, step]
  cases P.getD c.pc .reject <;> rfl

/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : Cfg W} {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : Cfg W} (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by rw [exec_succ, h]



/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (ht : t ≤ t') : exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : step P c with
    | inr v => rwa [exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/















/-! ## Straight-line code -/



















/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}





















end known

/-! ## Branches and verdicts -/









/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

























end framing

end ThreeSumApsp.WordRam


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam

/-- For a rational `r = p/q ≥ 0`: `(n^r)^q = n^p`. -/
theorem rpow_pow_den {r : ℚ} (hr0 : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr0))
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hmul : (r : ℝ) * (r.den : ℝ) = ((r.num.toNat : ℕ) : ℝ) := by
    rw [Rat.cast_def, hnum]
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hmul, Real.rpow_natCast]

/-- A function with `T(n) ≤ C n^r` from `n = 2` on is `O(n^r)` in the sense of the end statement. -/
theorem bigO_of_le_rpow {C : ℝ} {r : ℚ} (hr0 : 0 ≤ r) {T : ℕ → ℕ}
    (hT : ∀ n : ℕ, 2 ≤ n → (T n : ℝ) ≤ C * (n : ℝ) ^ (r : ℝ)) : EndStatement.BigO T r := by
  refine ⟨⌈|C| ^ r.den⌉₊, fun n hn => ?_⟩
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hreal : (T n : ℝ) ^ r.den ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
    calc (T n : ℝ) ^ r.den
        ≤ (|C| * (n : ℝ) ^ (r : ℝ)) ^ r.den :=
          pow_le_pow_left₀ (Nat.cast_nonneg _)
            ((hT n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hrpow)) _
      _ = |C| ^ r.den * (n : ℝ) ^ r.num.toNat := by rw [mul_pow, rpow_pow_den hr0]
      _ ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact_mod_cast hreal



/-- The rounded bound is `O(n^r)` in the sense of the end statement. -/
theorem bigO_stepBound (C : ℝ) {r : ℚ} (hr0 : 0 ≤ r) : EndStatement.BigO (stepBound C r) r := by
  refine bigO_of_le_rpow (C := 2 * |C| + 1) hr0 fun n hn => ?_
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by exact_mod_cast hr0)
  have habs : C * ((n : ℝ) ^ (r : ℝ) + 1) ≤ |C| * ((n : ℝ) ^ (r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hceil : (stepBound C r n : ℝ) < |C| * ((n : ℝ) ^ (r : ℝ) + 1) + 1 :=
    (Nat.cast_le.2 (Nat.ceil_le_ceil habs)).trans_lt (Nat.ceil_lt_add_one (by positivity))
  -- `|C| (X + 1) + 1 ≤ (2 |C| + 1) X` for `X ≥ 1`
  nlinarith [mul_nonneg (abs_nonneg C) (sub_nonneg.2 hone)]



end ThreeSumApsp.WordRam


open ThreeSumApsp ThreeSumApsp.WordRam in
theorem solution {Q : EndStatement.Problem} {a : ℝ} (h : SolvedInTime Q a 0)
    {r : ℚ} (hr : (r : ℝ) = a) (hr0 : 0 ≤ r) : Q.SolvedInTime r := by
  subst hr
  intro κ
  obtain ⟨P, b, C, hsolves⟩ := h κ
  refine ⟨P, b, stepBound C r, bigO_stepBound C hr0, fun n x hx W hW => ?_⟩
  obtain ⟨t, ht, verdict, c, hrun, hanswer⟩ := hsolves n x hx W hW
  have ht' : t ≤ stepBound C r n := by
    simp only [pow_zero, mul_one] at ht
    exact_mod_cast ht.trans (Nat.le_ceil _)
  exact ⟨verdict, c, WordRam.exec_mono (c := ⟨0, _⟩) hrun ht', hanswer⟩
