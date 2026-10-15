-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Compiler.compileProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:30:33.715137+00:00
-- url     : https://prove2.me/submissions/2145fb86-1d65-4aa4-b3d9-687722d07d15

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_effects_argsCode
import Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_effects_newFrame
import Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_rel_startMem
import Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_steps_setVar
import Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_steps_start
import Theorems.Thm_ThreeSum1960614_Machine_Light_Exec_bounded
import Theorems.Thm_ThreeSum1960614_Machine_Light_Exec_mem_outside

local instance platformRadixNonzero_3185c94b1a (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace List
end List
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.List
end ThreeSum1960614.Machine.List
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

variable {W : ℕ} {P : List _root_.EndStatement.Instr}

/-! ## Words -/





/-- The word of a number in the range of words, read as a signed number, is that number. -/
theorem toInt_wd {v : ℤ} (h : _root_.ThreeSumApsp.WordRam.InRange W v) : (_root_.ThreeSumApsp.WordRam.wd W v).toInt = v := by
  obtain ⟨hlo, hhi⟩ := h
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith

/-- Every word is the word of its signed value. -/
theorem wd_toInt (w : BitVec W) : _root_.ThreeSumApsp.WordRam.wd W w.toInt = w := BitVec.ofInt_toInt

section

private theorem private_541561795d_wd_add (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a + _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a + b) := (BitVec.ofInt_add a b).symm
end


section

private theorem private_8987e813d5_wd_mul (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a * _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a * b) := (BitVec.ofInt_mul a b).symm
end


section

private theorem private_8745cc2b10_wd_sub (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a - _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a - b) := by
  rw [sub_eq_add_neg a b, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
end


section

private theorem private_6b248825b2_wd_one : (1 : BitVec W) = _root_.ThreeSumApsp.WordRam.wd W 1 := BitVec.eq_of_toNat_eq rfl
end


/-- Numbers of absolute value at most B are in the range of words if 2 B < 2^W. -/
theorem inRange_of_abs_le {v B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : _root_.ThreeSumApsp.WordRam.InRange W v := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith





/-! ## Configurations and single steps -/





/-! ## Runs -/



theorem Steps.refl (c : _root_.ThreeSumApsp.WordRam.Cfg W) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 0 c c := rfl

section


private theorem Steps.private_ba3d5eb361_one {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} (h : _root_.ThreeSumApsp.WordRam.step P c = .inl c') : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 c c' := ⟨c', h, rfl⟩
end


/-- One run after the other. -/
theorem Steps.trans {n k : ℕ} {c c₁ c₂ : _root_.ThreeSumApsp.WordRam.Cfg W} (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c c₁) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P k c₁ c₂) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P (n + k) c c₂ := by
  induction n generalizing c with
  | zero => obtain rfl := h₁; simpa using h₂
  | succ n ih =>
    obtain ⟨c', hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨c', hs, ih hr⟩

/-- A run, with its last position written differently. -/
theorem Steps.cast_pos {n p p' : ℕ} {c : _root_.ThreeSumApsp.WordRam.Cfg W} {m : ℤ → BitVec W} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c ⟨p, m⟩)
    (hp : p = p') : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c ⟨p', m⟩ := hp ▸ h

/-- A run, with its number of steps written differently. -/
theorem Steps.cast_count {n n' : ℕ} {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c c') (hn : n = n') :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n' c c' := hn ▸ h

/-- Within no steps there is no verdict. -/
theorem exec_zero (c : _root_.ThreeSumApsp.WordRam.Cfg W) : _root_.EndStatement.exec P 0 c.pc c.mem = none := by rw [_root_.EndStatement.exec]

section

private theorem private_c654e189a0_exec_succ (t : ℕ) (c : _root_.ThreeSumApsp.WordRam.Cfg W) : _root_.EndStatement.exec P (t + 1) c.pc c.mem =
    match _root_.ThreeSumApsp.WordRam.step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => _root_.EndStatement.exec P t next.pc next.mem := by
  rw [_root_.EndStatement.exec, _root_.ThreeSumApsp.WordRam.step]
  cases P.getD c.pc _root_.EndStatement.Instr.reject <;> rfl
end


/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : _root_.ThreeSumApsp.WordRam.Cfg W} {v : Bool} (h : _root_.ThreeSumApsp.WordRam.step P c = .inr v) (t : ℕ) :
    _root_.EndStatement.exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_c654e189a0_exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} (h : _root_.ThreeSumApsp.WordRam.step P c = .inl c') (t : ℕ) :
    _root_.EndStatement.exec P (t + 1) c.pc c.mem = _root_.EndStatement.exec P t c'.pc c'.mem := by rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_c654e189a0_exec_succ, h]

/-- A run that reaches a verdict. -/
theorem exec_of_steps {n : ℕ} {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} {v : Bool} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c c')
    (hv : _root_.ThreeSumApsp.WordRam.step P c' = .inr v) : _root_.EndStatement.exec P (n + 1) c.pc c.mem = some (v, c'.mem) := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h
    exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_succ_of_verdict hv 0
  | succ n ih =>
    obtain ⟨c₁, hs, hr⟩ := h
    rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_succ_of_step hs]
    exact ih hr

/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : _root_.ThreeSumApsp.WordRam.Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : _root_.EndStatement.exec P t c.pc c.mem = some r) (ht : t ≤ t') : _root_.EndStatement.exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : _root_.ThreeSumApsp.WordRam.step P c with
    | inr v => rwa [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/



/-- The whole program, from position 0 on. -/
theorem codeAt_self (l : List _root_.EndStatement.Instr) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt l 0 l := List.prefix_refl l

/-- The first part of a piece of code. -/
theorem CodeAt.left {pos : ℕ} {l₁ l₂ : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (l₁ ++ l₂)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos l₁ :=
  (List.prefix_append l₁ l₂).trans h

/-- The second part of a piece of code follows the first. -/
theorem CodeAt.right {pos : ℕ} {l₁ l₂ : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (l₁ ++ l₂)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]

/-- The first instruction of a piece of code is the one that the machine finds at its position. -/
theorem CodeAt.head {pos : ℕ} {i : _root_.EndStatement.Instr} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: l)) :
    P.getD pos _root_.EndStatement.Instr.reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by rw [← hr]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- A piece of code without its first instruction. -/
theorem CodeAt.tail {pos : ℕ} {i : _root_.EndStatement.Instr} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: l)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P (pos + 1) l :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt.right (l₁ := [i]) h

/-- A piece of code, with its position written differently. -/
theorem CodeAt.cast_pos {pos pos' : ℕ} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos l) (hp : pos = pos') :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos' l := hp ▸ h

/-! ## Straight-line code -/







@[simp] theorem effects_nil (m : ℤ → BitVec W) : _root_.ThreeSumApsp.WordRam.effects [] m = m := rfl

@[simp] theorem effects_cons (i : _root_.EndStatement.Instr) (l : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (i :: l) m = _root_.ThreeSumApsp.WordRam.effects l (_root_.ThreeSumApsp.WordRam.effect i m) := rfl

theorem effects_append (l₁ l₂ : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (l₁ ++ l₂) m = _root_.ThreeSumApsp.WordRam.effects l₂ (_root_.ThreeSumApsp.WordRam.effects l₁ m) := by
  simp [_root_.ThreeSumApsp.WordRam.effects, List.foldl_append]

section

private theorem private_1baa6e787a_step_straight {c : _root_.ThreeSumApsp.WordRam.Cfg W} {i : _root_.EndStatement.Instr} (h : P.getD c.pc _root_.EndStatement.Instr.reject = i)
    (hi : _root_.ThreeSumApsp.WordRam.Straight i) : _root_.ThreeSumApsp.WordRam.step P c = .inl ⟨c.pc + 1, _root_.ThreeSumApsp.WordRam.effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    funext x
    simp [Function.update_apply]
  cases i <;> simp only [_root_.ThreeSumApsp.WordRam.Straight] at hi <;> simp only [_root_.ThreeSumApsp.WordRam.step, h, _root_.ThreeSumApsp.WordRam.effect, write, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_6b248825b2_wd_one]
end


section

/-- One instruction that only changes the memory. -/
private theorem private_264a1a74c7_steps_instr {rest : List _root_.EndStatement.Instr} {pos : ℕ} {i : _root_.EndStatement.Instr}
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: rest)) (hi : _root_.ThreeSumApsp.WordRam.Straight i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, _root_.ThreeSumApsp.WordRam.effect i m⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps.private_ba3d5eb361_one (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_1baa6e787a_step_straight hcode.head hi)
end


/-- A list of instructions that only change the memory. -/
theorem steps_straight (l : List _root_.EndStatement.Instr) (pc : ℕ) (m : ℤ → BitVec W) (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pc l)
    (hl : ∀ i ∈ l, _root_.ThreeSumApsp.WordRam.Straight i) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P l.length ⟨pc, m⟩ ⟨pc + l.length, _root_.ThreeSumApsp.WordRam.effects l m⟩ := by
  induction l generalizing pc m with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 hl
    exact ⟨_, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_1baa6e787a_step_straight hcode.head hi,
      (ih (pc + 1) (_root_.ThreeSumApsp.WordRam.effect i m) hcode.tail hl).cast_pos (by rw [List.length_cons]; omega)⟩

/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

/-- The only constant. -/
theorem effect_one (i : ℤ) : _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.one i) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W 1) := rfl

/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.add i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a + b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_541561795d_wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.sub i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8745cc2b10_wd_sub]

/-- The product of two known numbers. -/
theorem effect_mul (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.mul i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a * b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8987e813d5_wd_mul]

/-- Loading from the address a that the cell j holds. -/
theorem effect_load (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.load i j) m = Function.update m i (m a) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd ha]

/-- Storing at the address a that the cell i holds. -/
theorem effect_store (j : ℤ) (hi : m i = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.store i j) m = Function.update m a (m j) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hi, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd ha]

theorem steps_add {rest : List _root_.EndStatement.Instr} {pos : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.add i j k :: rest))
    (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a + b))⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add i hj hk ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_264a1a74c7_steps_instr hcode trivial m

theorem steps_sub {rest : List _root_.EndStatement.Instr} {pos : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.sub i j k :: rest))
    (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b))⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub i hj hk ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_264a1a74c7_steps_instr hcode trivial m

theorem steps_load {rest : List _root_.EndStatement.Instr} {pos : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.load i j :: rest))
    (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (m a)⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_load i hj ha ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_264a1a74c7_steps_instr hcode trivial m

theorem steps_store {rest : List _root_.EndStatement.Instr} {pos : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.store i j :: rest))
    (hi : m i = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m a (m j)⟩ :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_store j hi ha ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_264a1a74c7_steps_instr hcode trivial m

end known

/-! ## Branches and verdicts -/

/-- A branch on a cell that holds the number v: to l if v is negative, else to the next position. -/
theorem steps_bltz {rest : List _root_.EndStatement.Instr} {pos l : ℕ} {c v : ℤ} {m : ℤ → BitVec W}
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.bltz c l :: rest)) (hc : m c = _root_.ThreeSumApsp.WordRam.wd W v) (hv : _root_.ThreeSumApsp.WordRam.InRange W v) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps.private_ba3d5eb361_one ?_
  simp only [_root_.ThreeSumApsp.WordRam.step, hcode.head, hc, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd hv]

/-- A run that ends with a branch on the sign of v, where v is negative if and only if p fails. -/
theorem Steps.branch {n l pos pos' : ℕ} {c : _root_.ThreeSumApsp.WordRam.Cfg W} {m : ℤ → BitVec W} {v : ℤ} {p : Prop}
    (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c ⟨if v < 0 then l else pos, m⟩) (hv : p ↔ ¬ v < 0) (hpos : pos = pos') :
    (p → _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c ⟨pos', m⟩) ∧ (¬ p → _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c ⟨l, m⟩) := by
  subst hpos
  by_cases hp : p
  · exact ⟨fun _ => by rwa [if_neg (hv.1 hp)] at h, fun h' => absurd hp h'⟩
  · exact ⟨fun h' => absurd h' hp, fun _ => by rwa [if_pos (not_not.1 (mt hv.2 hp))] at h⟩

theorem step_accept {c : _root_.ThreeSumApsp.WordRam.Cfg W} (h : P.getD c.pc _root_.EndStatement.Instr.reject = _root_.EndStatement.Instr.accept) : _root_.ThreeSumApsp.WordRam.step P c = .inr true := by
  simp only [_root_.ThreeSumApsp.WordRam.step, h]

theorem step_reject {c : _root_.ThreeSumApsp.WordRam.Cfg W} (h : P.getD c.pc _root_.EndStatement.Instr.reject = _root_.EndStatement.Instr.reject) : _root_.ThreeSumApsp.WordRam.step P c = .inr false := by
  simp only [_root_.ThreeSumApsp.WordRam.step, h]

/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}



theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m := Set.eqOn_refl m sᶜ

theorem AgreeOutside.trans (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₂) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₂ m₃) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁

theorem AgreeOutside.mono (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (hst : s ⊆ t) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside t m m' :=
  Set.EqOn.mono (Set.compl_subset_compl.2 hst) h

/-- A change inside s, then a change inside t. -/
theorem AgreeOutside.trans_union (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₂) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside t m₂ m₃) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (s ∪ t) m₁ m₃ :=
  (h₁.mono Set.subset_union_left).trans (h₂.mono Set.subset_union_right)

/-- A cell outside s is unchanged. -/
theorem AgreeOutside.cell (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha

/-- A cell outside s still holds v. -/
theorem AgreeOutside.read (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v :=
  (h ha).trans hv

/-- Writing a cell of s. -/
theorem AgreeOutside.update (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (Function.update m' a v) :=
  fun x hx => (Function.update_of_ne (fun e : x = a => hx (e ▸ ha)) _ _).trans (h hx)



theorem WritesIn.mono {i : _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (hst : s ⊆ t) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn t i := by
  cases i <;> first | exact hst h | exact h

section

private theorem private_e74ef30073_agreeOutside_effect {i : _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (_root_.ThreeSumApsp.WordRam.effect i m) := by
  cases i <;>
    first | exact (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m).update h _ | exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m | exact h.elim
end


/-- Code without stores changes only the cells that its instructions name as their targets. -/
theorem agreeOutside_effects {l : List _root_.EndStatement.Instr} (h : ∀ i ∈ l, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (_root_.ThreeSumApsp.WordRam.effects l m) := by
  induction l generalizing m with
  | nil => exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_e74ef30073_agreeOutside_effect hi m).trans (ih hl _)

end framing

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List
open _root_.List


variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]

















/-! ## Blocks one after the other -/

















/-! ## Sums -/













section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]





end









/-! ## A running minimum -/





/-! ## Counting -/

















/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]







end Sorted

end List

namespace ThreeSumApsp
open _root_.ThreeSumApsp


variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/







/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  _root_.ThreeSum1960614.Machine.List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/





end ThreeSumApsp

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler from the light language to the word RAM: cells, and the code of statements

This file holds the definitions: the cells, the code of expressions, tests, statements, calls and
returns, the length of each piece of code, and the one condition on the text of a program (its
width).  The code of a whole program, `compileProgram`, puts these pieces together.

**Cells.**  A memory cell a of the light language is the cell a ≥ 0 of the machine.  Everything else
lives in negative cells.  A whole program takes two arguments from the cells -1 and -2 (`cARG1`,
`cARG2`) and puts its result into the cell -3 (`cRESULT`); the cell -4 is not used.  Odd cells from
-5 down hold the registers of the compiled code, the temporaries T₀, T₁, … for the evaluation of
expressions, and a pool of numbers: the cell `cPool n` holds the number n, for all n up to the
largest position to return to.  Even cells hold the call stack: stack cell j is the cell -2 j
(`cStack`).  The outermost frame of a whole program begins at stack cell `mainFrame` = 4, so the
code of its statements writes no stack cell before the cell -8 and leaves the cells -1, …, -4
alone.  The lemmas about pieces of code ask less: only that a frame begins after stack cell 0.

**Numbers.**  The constants of the program text are built from their binary digits where they are
needed.  The numbers that the compiled code itself needs, offsets in a frame and positions to return
to, come from the pool: the length of the code that builds a number from its digits depends on the
number, and a position to return to depends on the lengths.

**Frames.**  With F local variables per procedure, the frame of a running procedure is given by a
number q: local variable x is the cell -2 (q + x), the position to return to is in the
cell -2 (q - 1), and the register FP holds -2 q.  A call moves q to q + F + 1.

**Jumps.**  The machine only has "branch if negative" to a fixed position.  An unconditional jump
tests a register that holds -1.  A return loads the position r to return to into the register RR and
jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, …, which
arrives at position r after 2 (r + 1) steps: a constant for a fixed program.

**Calls.**  The caller evaluates the arguments into temporaries, computes the address of the new
frame, fills its local variables (arguments first, then zeros), stores the position to return to,
moves FP and jumps to the procedure.  The procedure ends with its return sequence: result into RET,
position into RR, FP back to the caller's frame, jump to the dispatcher.  Back in the caller, RET is
stored into the variable that receives the result.

**Lengths.**  A jump forward needs the length of code that is not yet written, so the lengths are
defined on the text (`Expr.size`, `Cond.size`, `Stmt.size`) and then shown to be the lengths of the
code (`length_compileExpr`, `length_compileCond`, `length_compileStmt`).
-/

@[expose] public section

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## Cells

The names of the registers are written in capitals, as in the comments on the code. -/


















/-! ## Expressions and tests -/















/-! ## Statements -/

























/-! ## Lengths -/

section

private theorem private_2e2c0c0be3_length_digitsCode (c : ℤ) (L : List ℕ) : (_root_.Light.Compiler.digitsCode c L).length = _root_.Light.Compiler.digitsLen L := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [_root_.Light.Compiler.digitsCode, _root_.Light.Compiler.digitsLen, List.length_append, ih, List.length_singleton]
    split_ifs <;> rfl
end


/-- The code of an expression has the length defined on the text. -/
theorem length_compileExpr (e : _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) : (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k).length = e.size := by
  induction e generalizing k with
  | const n => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_2e2c0c0be3_length_digitsCode _ _
  | var x => rfl
  | op o a b iha ihb => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.Light.Expr.size, iha, ihb]
  | load a ih => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.Light.Expr.size, ih]

/-- The code of a test has the length defined on the text. -/
theorem length_compileCond (c : _root_.ThreeSum1960614.Machine.Light.Cond) (l : ℕ) : (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c l).length = c.size := by
  cases c <;> simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond, _root_.ThreeSum1960614.Machine.Light.Cond.size, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr]

/-- The code for the arguments of a call has the length defined on the text. -/
theorem length_argsCode (es : List _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) : (_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode es k).length = _root_.ThreeSum1960614.Machine.Light.Compiler.argsSize es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode, _root_.ThreeSum1960614.Machine.Light.Compiler.argsSize, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr, ih]





section

/-- A call up to its jump has the length defined on the text. -/
private theorem private_d68abacb3f_length_callCode (G : _root_.Light.Compiler.CodeLayout) (p : ℕ) (args : List _root_.ThreeSum1960614.Machine.Light.Expr) (ret : ℕ) :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.callCode G p args ret).length = _root_.ThreeSum1960614.Machine.Light.Compiler.callSize G.F args := by
  simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.callCode, _root_.ThreeSum1960614.Machine.Light.Compiler.callSize, _root_.ThreeSum1960614.Machine.Light.Compiler.length_argsCode, _root_.Light.Compiler.length_newFrame]
end




/-- The code of a statement has the length defined on the text. -/
theorem length_compileStmt (G : _root_.Light.Compiler.CodeLayout) (s : _root_.ThreeSum1960614.Machine.Light.Stmt) (pos : ℕ) :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G s pos).length = s.size G.F := by
  induction s generalizing pos with
  | skip => rfl
  | set x e => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr]
  | store a e => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr]
  | seq s t ihs iht => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, ihs, iht]
  | ite c s t ihs iht => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, ihs, iht, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileCond]
  | «while» c s ih => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, ih, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileCond]
  | call p args x => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.private_d68abacb3f_length_callCode]

end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/













section width

variable {F x p : ℕ} {o : _root_.Light.Op} {a b e : _root_.ThreeSum1960614.Machine.Light.Expr} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s t : _root_.ThreeSum1960614.Machine.Light.Stmt} {args : List _root_.ThreeSum1960614.Machine.Light.Expr}



theorem Expr.vars_op_le_iff : (_root_.ThreeSum1960614.Machine.Light.Expr.op o a b).vars ≤ F ↔ a.vars ≤ F ∧ b.vars ≤ F := max_le_iff

theorem Expr.width_le_iff : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := max_le_iff

theorem Cond.width_lt_le_iff : (_root_.ThreeSum1960614.Machine.Light.Cond.lt a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Cond.width_eq_le_iff : (_root_.ThreeSum1960614.Machine.Light.Cond.eq a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Stmt.width_set_le_iff : (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e).width ≤ F ↔ x < F ∧ e.width ≤ F := max_le_iff

theorem Stmt.width_store_le_iff : (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e).width ≤ F ↔ a.width ≤ F ∧ e.width ≤ F :=
  max_le_iff

theorem Stmt.width_seq_le_iff : (_root_.ThreeSum1960614.Machine.Light.Stmt.seq s t).width ≤ F ↔ s.width ≤ F ∧ t.width ≤ F := max_le_iff

theorem Stmt.width_ite_le_iff :
    (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F ∧ t.width ≤ F := by
  simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.width, max_le_iff]

theorem Stmt.width_while_le_iff : (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F :=
  max_le_iff

theorem Stmt.width_call_le_iff :
    (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x).width ≤ F ↔ x < F ∧ args.length ≤ F ∧ ∀ e ∈ args, e.width ≤ F := by
  simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.width, max_le_iff, _root_.Light.maxOf_le_iff, Nat.succ_le_iff]

end width

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Runs stay within their limits

Facts about the semantics of the light language; none of them mentions the compiler.  A state is
bounded if every variable and every cell holds a number of absolute value at most `lim.word`.

* The value of a safe expression in a bounded state is such a number (`Expr.abs_val_le`).
* A run that starts in a bounded state ends in one (`Exec.bounded`): induction on the run.  An
  assignment and a store write the value of a safe expression; a call starts in a frame that holds
  the values of safe expressions and zeros (`bounded_callFrame`, a case of `bounded_frame`).
* A run does not change the cells from `lim.space` on (`Exec.mem_outside`).

The compiler's proof needs the first two because a word of the machine stands for a number only as
long as the number is in the range of words, and the third because its end theorem speaks of all
cells of the memory, also of those that the run may not touch.
-/

public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



/-- The value of a safe expression in a bounded state fits in a word. -/
theorem Expr.abs_val_le {σ : _root_.ThreeSum1960614.Machine.Light.State} (hσ : σ.Bounded lim) :
    ∀ e : _root_.ThreeSum1960614.Machine.Light.Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | _root_.ThreeSum1960614.Machine.Light.Expr.const n, h => by
    rw [_root_.ThreeSum1960614.Machine.Light.Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | _root_.ThreeSum1960614.Machine.Light.Expr.var x, _ => hσ.1 x
  | _root_.ThreeSum1960614.Machine.Light.Expr.op _ _ _, h => h.2.2
  | _root_.ThreeSum1960614.Machine.Light.Expr.load _, _ => hσ.2 _

/-- A frame that holds words, over a memory that holds words, is a bounded state. -/
theorem bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : _root_.ThreeSum1960614.Machine.Light.State.Bounded lim ⟨_root_.Light.frame args, μ⟩ :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSumApsp.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩

/-- The state in which a procedure starts is bounded, if the state of the caller is bounded and the
arguments of the call are safe. -/
theorem bounded_callFrame {σ : _root_.ThreeSum1960614.Machine.Light.State} (hσ : σ.Bounded lim) (args : List _root_.ThreeSum1960614.Machine.Light.Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : _root_.ThreeSum1960614.Machine.Light.State.Bounded lim ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ := by
  refine _root_.ThreeSum1960614.Machine.Light.bounded_frame (fun v hv => ?_) hσ.2
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  exact _root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ e (ha e he)





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## The numbers that never change -/



/-- A number within the limit on words is in the range of words. -/
theorem Fits.inRange {W : ℕ} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {N Q : ℕ} (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : _root_.ThreeSumApsp.WordRam.InRange W v :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.inRange_of_abs_le (by have := hfit.word; have := (abs_nonneg v).trans h; omega) h



/-! ## Sets of cells -/















/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/













variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {F : ℕ}

/-- What an expression may change is scratch. -/
theorem temps_subset_scratch {k : ℕ} : _root_.Light.Compiler.Temps k F ⊆ _root_.Light.Compiler.Scratch F := by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))

/-- A statement may change scratch cells. -/
theorem scratch_subset_writable {q : ℕ} : _root_.Light.Compiler.Scratch Z.F ⊆ _root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q :=
  (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left



/-- A statement in a later frame may change less. -/
theorem writable_subset_writable {q q' : ℕ} (h : q ≤ q') : _root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q' ⊆ _root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q :=
  Set.union_subset_union_left _ (Set.union_subset_union_right _ (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))))

/-- A statement may change the memory cells within the limits. -/
theorem mem_writable_of_addr {q : ℕ} {a : ℤ} (h : Z.lim.Addr a) : a ∈ _root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q :=
  Set.mem_union_right _ h

/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : _root_.Light.Compiler.cStack q - ((2 * x : ℕ) : ℤ) = _root_.Light.Compiler.cStack (q + x) := by
  simp only [_root_.Light.Compiler.cStack]
  push_cast
  ring

/-- Back from the frame q + x to the frame q. -/
theorem cStack_add (q x : ℕ) : _root_.Light.Compiler.cStack (q + x) + ((2 * x : ℕ) : ℤ) = _root_.Light.Compiler.cStack q := by
  simp only [_root_.Light.Compiler.cStack]
  push_cast
  ring

/-- The stack cell before the cell q + 1. -/
theorem cStack_succ_add (q : ℕ) : _root_.Light.Compiler.cStack (q + 1) + ((2 : ℕ) : ℤ) = _root_.Light.Compiler.cStack q := _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_add q 1

/-- The addresses of the stack fit in a word. -/
theorem Sizes.inRange_stack (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : _root_.ThreeSumApsp.WordRam.InRange W (_root_.Light.Compiler.cStack j) := by
  have hjQ : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [_root_.Light.Compiler.cStack] <;> linarith [Z.fits.stack]

/-- The addresses of the memory fit in a word. -/
theorem Sizes.inRange_addr (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) {a : ℤ} (h : Z.lim.Addr a) : _root_.ThreeSumApsp.WordRam.InRange W a := by
  constructor <;> linarith [Z.fits.space, h.1, h.2]

/-- The number -1, on which every jump branches, fits in a word. -/
theorem Sizes.inRange_neg_one (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) : _root_.ThreeSumApsp.WordRam.InRange W (-1) := by
  have hN : (2 : ℤ) ≤ Z.disp := by
    exact_mod_cast (Nat.le_mul_of_pos_right 2 Z.F.succ_pos).trans Z.offsets_le
  constructor <;> linarith [Z.fits.pool_lt]

/-! ## The relation between a state of the light language and a memory of the machine -/



section Rel

variable {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {q q' : ℕ} {m m' : ℤ → BitVec W}

/-- After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
as soon as FP, the local variables and the memory cells are right. -/
theorem Rel.of_agreeOutside {s : Set ℤ} (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m')
    (hs : s ⊆ (_root_.Light.Compiler.Constants Z.disp)ᶜ) (hfp : m' _root_.Light.Compiler.cFP = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack q'))
    (hloc : ∀ x < Z.F, m' (_root_.Light.Compiler.cStack (q' + x)) = _root_.ThreeSumApsp.WordRam.wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (σ'.mem a)) : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ' q' m' := by
  have keep {a : ℤ} (ha : a ∈ _root_.Light.Compiler.Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact {
    one := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.one
    zero := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.zero
    neg := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.neg
    pool := fun n hn => (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans (R.pool n hn)
    fp := hfp
    loc := hloc
    mem := hmem }

/-- A memory that differs only in scratch cells represents the same state. -/
theorem Rel.same (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch Z.F) m m') : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m' :=
  R.of_agreeOutside A (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) R.fp)
    (fun x hx => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.loc x hx)) fun a ha => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.mem a ha)





/-- Writing a memory cell. -/
theorem Rel.setMem (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (hq : 1 ≤ q) {a : ℤ} (ha : Z.lim.Addr a) (v : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z { σ with mem := Function.update σ.mem a.toNat v } q (Function.update m a (_root_.ThreeSumApsp.WordRam.wd W v)) := by
  -- the address is not negative, so it is no register and no stack cell of the frame
  have hnonneg : 0 ≤ a := ha.1
  refine R.of_agreeOutside ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl {a} m).update rfl _) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
    (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact R.fp))) (fun x hx => by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact R.loc x hx))) fun b hb => ?_
  obtain rfl | hab := eq_or_ne b a.toNat
  · simp [Int.toNat_of_nonneg hnonneg]
  · rw [Function.update_of_ne (by omega)]
    exact (R.mem b hb).trans (by simp [hab])

/-- Reading a memory cell. -/
theorem Rel.read (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = _root_.ThreeSumApsp.WordRam.wd W (σ.mem a.toNat) := by
  have := R.mem a.toNat (by have := ha.1; have := ha.2; omega)
  rwa [Int.toNat_of_nonneg ha.1] at this

/-- The cell to which FP points is local variable 0. -/
theorem Rel.loc_zero (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (hF : 0 < Z.F) : m (_root_.Light.Compiler.cStack q) = _root_.ThreeSumApsp.WordRam.wd W (σ.loc 0) :=
  R.loc 0 hF

end Rel



/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}

/-- A memory that differs only in scratch cells represents the same state in the same frame. -/
theorem Framed.same (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch Z.F) m m') : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m' :=
  ⟨I.rel.same A, I.low, I.high⟩

/-- An unconditional jump. -/
theorem steps_jump {l : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG l :: rest))
    (hneg : m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1)) (hr : _root_.ThreeSumApsp.WordRam.InRange W (-1)) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by
  simpa using _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_bltz hcode hneg hr



end code

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The dispatcher

The machine has no indirect jump.  A return loads the position r to return to into the register RR
and jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, ….  It
arrives at position r after 2 (r + 1) steps and changes no cell but RR (`steps_dispatcher`).

The proof runs one pair of instructions (`steps_dispatcher_pair`) and then counts down: from the
j-th pair on, with k in RR, the machine arrives at position j + k (`steps_dispatcher_from`).
-/

public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

variable {W : ℕ} {code : List _root_.EndStatement.Instr} {disp n : ℕ}

section

/-- The dispatcher for one more position. -/
private theorem private_8e7a3f2766_dispatcher_succ (n : ℕ) :
    _root_.Light.Compiler.dispatcher (n + 1) = _root_.Light.Compiler.dispatcher n ++ [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cRR _root_.Light.Compiler.cRR _root_.Light.Compiler.cONE, _root_.EndStatement.Instr.bltz _root_.Light.Compiler.cRR n] := by
  simp [_root_.Light.Compiler.dispatcher, List.range_succ, List.flatMap_append]
end


/-- Two instructions for each position. -/
theorem length_dispatcher (n : ℕ) : (_root_.Light.Compiler.dispatcher n).length = 2 * n := by
  simp [_root_.Light.Compiler.dispatcher, List.length_flatMap, Nat.mul_comm]

section

/-- A shorter dispatcher is the beginning of a longer one. -/
private theorem private_943ef8d15a_dispatcher_prefix {j n : ℕ} (h : j ≤ n) : _root_.Light.Compiler.dispatcher j <+: _root_.Light.Compiler.dispatcher n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (_root_.ThreeSum1960614.Machine.Light.Compiler.private_8e7a3f2766_dispatcher_succ n ▸ List.prefix_append _ _)
end


section

/-- The two instructions for the position j. -/
private theorem private_30c28e35c2_codeAt_dispatcher {j : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code disp (_root_.Light.Compiler.dispatcher n)) (hj : j < n) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (disp + 2 * j) [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cRR _root_.Light.Compiler.cRR _root_.Light.Compiler.cONE, _root_.EndStatement.Instr.bltz _root_.Light.Compiler.cRR j] := by
  have upToPairCode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code disp (_root_.Light.Compiler.dispatcher j ++ [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cRR _root_.Light.Compiler.cRR _root_.Light.Compiler.cONE, _root_.EndStatement.Instr.bltz _root_.Light.Compiler.cRR j]) :=
    _root_.ThreeSum1960614.Machine.Light.Compiler.private_8e7a3f2766_dispatcher_succ j ▸ (_root_.ThreeSum1960614.Machine.Light.Compiler.private_943ef8d15a_dispatcher_prefix hj).trans hcode
  exact upToPairCode.right.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.length_dispatcher])
end


section

/-- The two instructions for the position j, when RR holds v: RR goes down by one, and the machine
goes to j if that is negative and to the next pair if not. -/
private theorem private_cafb737738_steps_dispatcher_pair {j : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code disp (_root_.Light.Compiler.dispatcher n))
    (hj : j < n) (m : ℤ → BitVec W) (hone : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1) {v : ℤ} (hv : _root_.ThreeSumApsp.WordRam.InRange W (v - 1)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code 2 ⟨disp + 2 * j, Function.update m _root_.Light.Compiler.cRR (_root_.ThreeSumApsp.WordRam.wd W v)⟩
      ⟨if v - 1 < 0 then j else disp + 2 * (j + 1), Function.update m _root_.Light.Compiler.cRR (_root_.ThreeSumApsp.WordRam.wd W (v - 1))⟩ := by
  have pairCode := _root_.ThreeSum1960614.Machine.Light.Compiler.private_30c28e35c2_codeAt_dispatcher hcode hj
  -- RR := RR - 1
  have run₁ := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_sub pairCode (Function.update_self _root_.Light.Compiler.cRR (_root_.ThreeSumApsp.WordRam.wd W v) m)
    (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact hone)))
  rw [Function.update_idem] at run₁
  -- if RR < 0 go to j
  exact run₁.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_bltz pairCode.tail (Function.update_self _ _ _) hv)
end


section

/-- The dispatcher from its j-th pair of instructions on, when RR holds k: it arrives at position
j + k.  The positions fit in a word (hn). -/
private theorem private_397f9a608f_steps_dispatcher_from (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code disp (_root_.Light.Compiler.dispatcher n))
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1) (k j : ℕ)
    (hjk : j + k < n) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code (2 * (k + 1)) ⟨disp + 2 * j, Function.update m _root_.Light.Compiler.cRR (_root_.ThreeSumApsp.WordRam.wd W k)⟩
      ⟨j + k, Function.update m _root_.Light.Compiler.cRR (_root_.ThreeSumApsp.WordRam.wd W (-1))⟩ := by
  induction k generalizing j with
  | zero =>
    simpa using _root_.ThreeSum1960614.Machine.Light.Compiler.private_cafb737738_steps_dispatcher_pair hcode (show j < n by omega) m hone (v := 0)
      (by constructor <;> omega)
  | succ k ih =>
    have run := _root_.ThreeSum1960614.Machine.Light.Compiler.private_cafb737738_steps_dispatcher_pair hcode (show j < n by omega) m hone (v := k + 1)
      (by constructor <;> omega)
    rw [if_neg (by omega), add_sub_cancel_right] at run
    rw [Nat.cast_succ]
    -- 2 + 2 (k + 1) steps lead to the position j + 1 + k
    exact ((run.trans (ih (j + 1) (by omega))).cast_count (by ring)).cast_pos (by ring)
end


/-- From the beginning of the dispatcher, with the position r in RR, the machine arrives at position
r after 2 (r + 1) steps; RR then holds -1, and no other cell has changed.  The positions fit in a
word (hn). -/
theorem steps_dispatcher {r : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code disp (_root_.Light.Compiler.dispatcher n)) (hr : r < n)
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1)
    (hRR : m _root_.Light.Compiler.cRR = _root_.ThreeSumApsp.WordRam.wd W r) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code (2 * (r + 1)) ⟨disp, m⟩ ⟨r, Function.update m _root_.Light.Compiler.cRR (_root_.ThreeSumApsp.WordRam.wd W (-1))⟩ := by
  have := _root_.ThreeSum1960614.Machine.Light.Compiler.private_397f9a608f_steps_dispatcher_from hcode hn m hone r 0 (by omega)
  rwa [Nat.mul_zero, Nat.add_zero, Nat.zero_add, ← hRR, Function.update_eq_self] at this

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler is correct on expressions

The code of an expression e, compiled for the temporary T_k, only changes the memory
(`straight_compileExpr`).  Run in a memory that represents the state σ, it leaves the value of e in
T_k and changes nothing but ADDR and the temporaries from T_k on.  That is `effects_compileExpr`,
for an expression that needs no more temporaries than there are from T_k on, and
`effects_compileExpr_of_width`, the form that the other files use, for an expression of width at
most F.

The proof is an induction on e; in each case the instructions are run one after the other.  A
constant is built from its binary digits (`effects_digitsCode`).  For an operation, the value of the
left side waits in T_k while the right side is evaluated into T_{k+1}, which does not touch T_k.
-/

public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


variable {W : ℕ} {F : ℕ}

section


/-- Every expression uses at least one temporary. -/
private theorem _root_.ThreeSum1960614.Machine.Light.Expr.private_12b548b970_height_pos (e : _root_.ThreeSum1960614.Machine.Light.Expr) : 0 < e.height := by
  induction e with
  | const n => simp [_root_.ThreeSum1960614.Machine.Light.Expr.height]
  | var x => simp [_root_.ThreeSum1960614.Machine.Light.Expr.height]
  | op o a b iha _ => exact lt_of_lt_of_le iha (le_max_left _ _)
  | load a ih => exact ih
end


section

/-- The temporary that receives the value of an expression is one of those that its code may
change. -/
private theorem private_ea85bee431_cT_mem_temps_of_height (e : _root_.ThreeSum1960614.Machine.Light.Expr) {k : ℕ} (hT : k + e.height ≤ 2 * F + 1) :
    _root_.Light.Compiler.cT k ∈ _root_.Light.Compiler.Temps k F := by
  have := e.private_12b548b970_height_pos
  ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end


/-! ## Constants -/

section

private theorem private_ffae133e3a_straight_digitsCode (c : ℤ) : ∀ L : List ℕ, ∀ i ∈ _root_.Light.Compiler.digitsCode c L, _root_.ThreeSumApsp.WordRam.Straight i
  | [] => by simp [_root_.Light.Compiler.digitsCode, _root_.ThreeSumApsp.WordRam.Straight]
  | d :: L => by
    have := private_ffae133e3a_straight_digitsCode c L
    by_cases hd : d = 0 <;> simpa [_root_.Light.Compiler.digitsCode, hd, _root_.ThreeSumApsp.WordRam.Straight, or_imp, forall_and] using this
end


section

/-- The code for a constant: the cell c receives the number with the given binary digits, and
nothing else changes. -/
private theorem private_9b09e22f2f_effects_digitsCode {c : ℤ} (hc : _root_.Light.Compiler.cONE ≠ c) (L : List ℕ) (hL : ∀ d ∈ L, d < 2)
    (m : ℤ → BitVec W) (hone : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1) :
    _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.digitsCode c L) m c = _root_.ThreeSumApsp.WordRam.wd W (Nat.ofDigits 2 L : ℕ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside {c} m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.digitsCode c L) m) := by
  induction L with
  | nil =>
    -- c := c - c
    rw [_root_.Light.Compiler.digitsCode, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub c (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.wd_toInt (m c)).symm (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.wd_toInt (m c)).symm, sub_self]
    exact ⟨by simp, (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (Set.mem_singleton c) _⟩
  | cons d L ih =>
    obtain ⟨val, A⟩ := ih fun x hx => hL x (by simp [hx])
    -- c := c + c
    rw [_root_.Light.Compiler.digitsCode, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add c val val]
    have hd : d = 0 ∨ d = 1 := by have := hL d (by simp); omega
    obtain rfl | rfl := hd
    · refine ⟨?_, A.update (Set.mem_singleton c) _⟩
      rw [if_pos rfl, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil, Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
    · -- c := c + 1
      rw [if_neg one_ne_zero, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add c (Function.update_self _ _ _)
        ((Function.update_of_ne hc _ _).trans (A.read hc hone))]
      refine ⟨?_, (A.update (Set.mem_singleton c) _).update (Set.mem_singleton c) _⟩
      rw [Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
end


/-! ## Expressions -/

section

private theorem private_87cbd301cd_straight_instr (o : _root_.Light.Op) (i j k : ℤ) : _root_.ThreeSumApsp.WordRam.Straight (o.instr i j k) := by
  cases o <;> trivial
end


/-- The code of an expression only changes the memory. -/
theorem straight_compileExpr : ∀ (e : _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ), ∀ i ∈ _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k, _root_.ThreeSumApsp.WordRam.Straight i
  | _root_.ThreeSum1960614.Machine.Light.Expr.const _, _ => _root_.ThreeSum1960614.Machine.Light.Compiler.private_ffae133e3a_straight_digitsCode _ _
  | _root_.ThreeSum1960614.Machine.Light.Expr.var _, _ => by simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSumApsp.WordRam.Straight]
  | _root_.ThreeSum1960614.Machine.Light.Expr.op o a b, k => List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨straight_compileExpr a k, straight_compileExpr b (k + 1)⟩, by simp [_root_.ThreeSum1960614.Machine.Light.Compiler.private_87cbd301cd_straight_instr]⟩
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a, k => List.forall_mem_append.2 ⟨straight_compileExpr a k, by simp [_root_.ThreeSumApsp.WordRam.Straight]⟩

section

/-- The instruction of an operation, on cells that hold known numbers. -/
private theorem private_110484d29f_effect_instr (o : _root_.Light.Op) {m : ℤ → BitVec W} {j k a b : ℤ} (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a)
    (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) : _root_.ThreeSumApsp.WordRam.effect (o.instr i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (o.eval a b)) := by
  cases o
  exacts [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add i hj hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub i hj hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_mul i hj hk]
end


variable {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q : ℕ} {m : ℤ → BitVec W}

section

/-- The code of an expression leaves its value in T_k and changes nothing but ADDR and the
temporaries from T_k on. -/
private theorem private_4eead6d256_effects_compileExpr (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) (hvars : e.vars ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hT : k + e.height ≤ 2 * Z.F + 1) :
    _root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m (_root_.Light.Compiler.cT k) = _root_.ThreeSumApsp.WordRam.wd W (e.val σ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Temps k Z.F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m) := by
  induction e generalizing k m with
  | const n =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    obtain ⟨val, A⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_9b09e22f2f_effects_digitsCode (c := _root_.Light.Compiler.cT k) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (Nat.digits 2 n)
      (fun d hd => Nat.digits_lt_base (by norm_num) hd) m I.rel.one
    rw [Nat.ofDigits_digits] at val
    exact ⟨val, A.mono (Set.singleton_subset_iff.2 hk)⟩
  | var x =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    have hx : x < Z.F := hvars
    have hN := Z.offsets_le
    have hQ := I.high
    -- ADDR := FP - 2 x; T_k := the cell at ADDR
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cADDR I.rel.fp (I.rel.pool (2 * x) (by omega)), _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_sub,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_load (_root_.Light.Compiler.cT k) (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨?_, ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _).update hk _⟩
    rw [Function.update_self, Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), I.rel.loc x hx, _root_.ThreeSum1960614.Machine.Light.Expr.val]
  | op o a b iha ihb =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    have hha : a.height ≤ (_root_.ThreeSum1960614.Machine.Light.Expr.op o a b).height := le_max_left _ _
    have hhb : b.height + 1 ≤ (_root_.ThreeSum1960614.Machine.Light.Expr.op o a b).height := le_max_right _ _
    obtain ⟨hwa, hwb⟩ := _root_.ThreeSum1960614.Machine.Light.Expr.vars_op_le_iff.1 hvars
    obtain ⟨hsa, hsb, -⟩ := hs
    obtain ⟨va, Aa⟩ := iha I k hwa hsa (by omega)
    obtain ⟨vb, Ab⟩ := ihb (I.same (Aa.mono _root_.ThreeSum1960614.Machine.Light.Compiler.temps_subset_scratch)) (k + 1) hwb hsb (by omega)
    -- T_k := T_k o T_{k+1}
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.Light.Compiler.private_110484d29f_effect_instr o (_root_.Light.Compiler.cT k) (Ab.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) va) vb]
    exact ⟨Function.update_self _ _ _,
      (Aa.trans (Ab.mono (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))))).update hk _⟩
  | load a ih =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    obtain ⟨hsa, haddr⟩ := hs
    obtain ⟨va, Aa⟩ := ih I k hvars hsa hT
    -- the address is not negative, so it is neither ADDR nor a temporary
    have hnonneg : 0 ≤ a.val σ := haddr.1
    -- T_k := the cell at T_k
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_load (_root_.Light.Compiler.cT k) va (Z.inRange_addr haddr), Aa.cell (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), I.rel.read haddr]
    exact ⟨Function.update_self _ _ _, Aa.update hk _⟩
end


/-- The code of an expression of width at most F, when there are F temporaries from T_k on, leaves
its value in T_k and changes nothing but ADDR and the temporaries from T_k on. -/
theorem effects_compileExpr_of_width (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) (hw : e.width ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hk : k ≤ Z.F + 1) :
    _root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m (_root_.Light.Compiler.cT k) = _root_.ThreeSumApsp.WordRam.wd W (e.val σ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Temps k Z.F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m) :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.private_4eead6d256_effects_compileExpr I e k (_root_.ThreeSum1960614.Machine.Light.Expr.width_le_iff.1 hw).1 hs
    (by have := (_root_.ThreeSum1960614.Machine.Light.Expr.width_le_iff.1 hw).2; omega)

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler is correct on tests

The code of a test goes on to the next position if the test holds and jumps to a given position if
it does not, in at most as many steps as it has instructions, and it changes scratch cells only.
This behaviour is called `Decides`, and `decides_compileCond` proves it.

Both tests first evaluate a into T₀ and b into T₁ (`steps_pair`, which also serves the statement
that stores into the memory).  For a < b the code forms D = b - a - 1 and leaves if D < 0
(`decides_lt`).  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative (`decides_eq`).  No difference overflows, because words hold twice the largest value and
one more (`inRange_sub`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {code rest : List _root_.EndStatement.Instr} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : _root_.ThreeSum1960614.Machine.Light.Expr}

/-! ## Two expressions -/

/-- What follows the code of two expressions. -/
theorem codeAt_after_pair (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr a 0 ++ _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr b 1 ++ rest)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + (a.size + b.size)) rest :=
  hcode.right.cast_pos (by rw [List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr])

/-- The code of two expressions, one after the other, leaves their values in T₀ and T₁ and changes
scratch cells only. -/
theorem steps_pair (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m)
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr a 0 ++ _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr b 1 ++ rest)) (hwa : a.width ≤ Z.F)
    (hwb : b.width ≤ Z.F) (hsa : a.Safe Z.lim σ) (hsb : b.Safe Z.lim σ) :
    ∃ m', _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code (a.size + b.size) ⟨pos, m⟩ ⟨pos + (a.size + b.size), m'⟩ ∧
      m' (_root_.Light.Compiler.cT 0) = _root_.ThreeSumApsp.WordRam.wd W (a.val σ) ∧ m' (_root_.Light.Compiler.cT 1) = _root_.ThreeSumApsp.WordRam.wd W (b.val σ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch Z.F) m m' := by
  obtain ⟨va, Aa⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.effects_compileExpr_of_width I a 0 hwa hsa (by omega)
  have Aa' := Aa.mono _root_.ThreeSum1960614.Machine.Light.Compiler.temps_subset_scratch
  obtain ⟨vb, Ab⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.effects_compileExpr_of_width (I.same Aa') b 1 hwb hsb (by omega)
  have run := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_straight _ pos m hcode.left
    (List.forall_mem_append.2 ⟨_root_.ThreeSum1960614.Machine.Light.Compiler.straight_compileExpr a 0, _root_.ThreeSum1960614.Machine.Light.Compiler.straight_compileExpr b 1⟩)
  rw [List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append] at run
  exact ⟨_, run, Ab.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) va, vb, Aa'.trans (Ab.mono _root_.ThreeSum1960614.Machine.Light.Compiler.temps_subset_scratch)⟩

/-! ## Tests -/



/-- The test holds. -/
theorem Decides.of_holds {F size : ℕ} {p : Prop} (h : _root_.ThreeSum1960614.Machine.Light.Compiler.Decides code F pos size l m p) (hp : p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch F) m m' ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩ :=
  let ⟨m', n, le, A, run, _⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- The test fails. -/
theorem Decides.of_fails {F size : ℕ} {p : Prop} (h : _root_.ThreeSum1960614.Machine.Light.Compiler.Decides code F pos size l m p) (hp : ¬ p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch F) m m' ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code n ⟨pos, m⟩ ⟨l, m'⟩ :=
  let ⟨m', n, le, A, _, run⟩ := h
  ⟨m', n, le, A, run hp⟩

section

/-- No overflow: the difference of two values fits in a word, and so does one less. -/
private theorem private_9ce8b854f1_inRange_sub (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) {x y : ℤ} (hx : |x| ≤ Z.lim.word)
    (hy : |y| ≤ Z.lim.word) : _root_.ThreeSumApsp.WordRam.InRange W (x - y) ∧ _root_.ThreeSumApsp.WordRam.InRange W (x - y - 1) := by
  obtain ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩ := And.intro (abs_le.1 hx) (abs_le.1 hy)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Z.fits.word]
end


section

/-- The test a < b. -/
private theorem private_eede0bb54f_decides_lt (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond (_root_.ThreeSum1960614.Machine.Light.Cond.lt a b) l)) (hw : (_root_.ThreeSum1960614.Machine.Light.Cond.lt a b).width ≤ Z.F)
    (hs : (_root_.ThreeSum1960614.Machine.Light.Cond.lt a b).Safe Z.lim σ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Decides code Z.F pos (_root_.ThreeSum1960614.Machine.Light.Cond.lt a b).size l m (a.val σ < b.val σ) := by
  obtain ⟨hwa, hwb⟩ := _root_.ThreeSum1960614.Machine.Light.Cond.width_lt_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.steps_pair I hcode hwa hwb hsa hsb
  have restCode := _root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_after_pair hcode
  -- D := b - a
  have run₂ := run₁.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_sub restCode vb va)
  -- D := D - 1
  have run₃ := run₂.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_sub restCode.tail (Function.update_self _ _ _)
    (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact (I.rel.same A₁).one))))
  -- leave if D < 0
  have run₄ := run₃.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_bltz restCode.tail.tail (Function.update_self _ _ _)
    (_root_.ThreeSum1960614.Machine.Light.Compiler.private_9ce8b854f1_inRange_sub Z (_root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ b hsb) (_root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ a hsa)).2)
  exact ⟨_, _, by rw [_root_.ThreeSum1960614.Machine.Light.Cond.size], (A₁.update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _,
    run₄.branch (by omega) (by rw [_root_.ThreeSum1960614.Machine.Light.Cond.size]; omega)⟩
end


section

/-- The test a = b. -/
private theorem private_091a3183bf_decides_eq (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond (_root_.ThreeSum1960614.Machine.Light.Cond.eq a b) l)) (hw : (_root_.ThreeSum1960614.Machine.Light.Cond.eq a b).width ≤ Z.F)
    (hs : (_root_.ThreeSum1960614.Machine.Light.Cond.eq a b).Safe Z.lim σ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Decides code Z.F pos (_root_.ThreeSum1960614.Machine.Light.Cond.eq a b).size l m (a.val σ = b.val σ) := by
  obtain ⟨hwa, hwb⟩ := _root_.ThreeSum1960614.Machine.Light.Cond.width_eq_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  have ha := _root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ a hsa
  have hb := _root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ b hsb
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.steps_pair I hcode hwa hwb hsa hsb
  have restCode := _root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_after_pair hcode
  -- D := a - b
  have run₂ := run₁.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_sub restCode va vb)
  have A₂ := A₁.update (a := _root_.Light.Compiler.cD) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (_root_.ThreeSumApsp.WordRam.wd W (a.val σ - b.val σ))
  -- leave if D < 0
  have run₃ := run₂.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_bltz restCode.tail (Function.update_self _ _ _)
    (_root_.ThreeSum1960614.Machine.Light.Compiler.private_9ce8b854f1_inRange_sub Z ha hb).1)
  by_cases hlt : a.val σ - b.val σ < 0
  · rw [if_pos hlt] at run₃
    exact ⟨_, _, by rw [_root_.ThreeSum1960614.Machine.Light.Cond.size]; omega, A₂, fun h => absurd h (by omega), fun _ => run₃⟩
  rw [if_neg hlt] at run₃
  -- D := 0 - D
  have run₄ := run₃.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_sub restCode.tail.tail
    (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact (I.rel.same A₁).zero)))
    (Function.update_self _ _ _))
  rw [zero_sub, neg_sub] at run₄
  -- leave if D < 0
  have run₅ := run₄.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_bltz restCode.tail.tail.tail (Function.update_self _ _ _)
    (_root_.ThreeSum1960614.Machine.Light.Compiler.private_9ce8b854f1_inRange_sub Z hb ha).1)
  exact ⟨_, _, by rw [_root_.ThreeSum1960614.Machine.Light.Cond.size], A₂.update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _,
    run₅.branch (by omega) (by rw [_root_.ThreeSum1960614.Machine.Light.Cond.size]; omega)⟩
end


/-- The code of a test decides the test. -/
theorem decides_compileCond (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (hσ : σ.Bounded Z.lim) (c : _root_.ThreeSum1960614.Machine.Light.Cond)
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c l)) (hw : c.width ≤ Z.F) (hs : c.Safe Z.lim σ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Decides code Z.F pos c.size l m (c.Holds σ) := by
  cases c with
  | lt a b => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_eede0bb54f_decides_lt I hσ hcode hw hs
  | eq a b => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_091a3183bf_decides_eq I hσ hcode hw hs

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The code of a whole program

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the light
program P.  With dec = false it accepts at the end of the run; with dec = true it accepts if the
result of the procedure is positive and rejects if not.  It has five parts:

| position | part |
|---|---|
| 0 | `headCode`: the numbers 1, 0, -1, and a jump to the start-up code |
| `mainPos` | `mainCode`: the outermost statement `mainStmt p0`, then the verdict (`tailCode`) |
| `firstBody` | `bodiesCode`: the bodies of the procedures, each with its return sequence |
| `dispPos` | the dispatcher for the positions below `dispPos` |
| `3 * dispPos` | `startCode`: the pool, the outermost frame, and a jump back to `mainPos` |

The start-up code comes last so that no position in the rest of the code depends on its length.

The number `frameSize` of local variables of every frame is read off the text of P: it is the width
of the text.  The pool holds the numbers up to `dispPos`: every position to return to, and with them
the smaller numbers that the code needs (`two_mul_frameSize_add_le_dispPos`).

The facts proved here are about positions only: each part is where the table says
(`codeAt_headCode`, …, `codeAt_startCode`), and every body is at its entry (`codeAt_bodies`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## The number read off the text -/



/-- The outermost frame has room for the result and the two arguments. -/
theorem three_le_frameSize (P : _root_.ThreeSum1960614.Machine.Light.Program) : 3 ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P := le_max_left _ _

/-- Every body fits into a frame. -/
theorem width_le_frameSize {P : _root_.ThreeSum1960614.Machine.Light.Program} {b : _root_.ThreeSum1960614.Machine.Light.Stmt} (hb : b ∈ P) : b.width ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P :=
  (_root_.Light.maxOf_le_iff.1 le_rfl b hb).trans (le_max_right _ _)

/-! ## The parts of the code -/







































/-! ## Lengths and positions -/

section

private theorem private_61fdf1c7a3_le_endPos (F : ℕ) : ∀ (bs : List _root_.ThreeSum1960614.Machine.Light.Stmt) (pos : ℕ), pos ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.endPos F bs pos
  | [], _ => le_rfl
  | b :: bs, pos => le_trans (by omega) (private_61fdf1c7a3_le_endPos F bs (pos + b.size F + _root_.Light.Compiler.epilogueSize))
end


/-- The length of the outermost statement. -/
theorem size_mainStmt (p0 F : ℕ) : (_root_.ThreeSum1960614.Machine.Light.mainStmt p0).size F = 2 * F + 11 := by
  simp +arith [_root_.ThreeSum1960614.Machine.Light.mainStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.callSize, _root_.ThreeSum1960614.Machine.Light.Compiler.argsSize, _root_.ThreeSum1960614.Machine.Light.Expr.size]

/-- The outermost statement uses the local variables 0, 1, 2. -/
theorem width_mainStmt (p0 : ℕ) : (_root_.ThreeSum1960614.Machine.Light.mainStmt p0).width = 3 := rfl

section

private theorem private_5cb4f1262a_length_tailCode (dec : Bool) (pos : ℕ) :
    (_root_.Light.Compiler.tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl
end


/-- The dispatcher comes after four instructions, the 2 F + 11 instructions of the outermost
statement and at least two for the verdict.  So the pool also holds the distance 2 (F + 1) between
two frames and the number 2 · `mainFrame` from which the start-up code forms the first frame
pointer, and it reaches further down than the 2 F + 1 temporaries. -/
theorem two_mul_frameSize_add_le_dispPos (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) :
    2 * _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 17 ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec := by
  have : _root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec := _root_.ThreeSum1960614.Machine.Light.Compiler.private_61fdf1c7a3_le_endPos _ _ _
  have htail : 2 ≤ if dec then 5 else 2 := by split_ifs <;> omega
  simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody, _root_.ThreeSum1960614.Machine.Light.Compiler.tailPos, _root_.Light.Compiler.mainPos, _root_.ThreeSum1960614.Machine.Light.Compiler.size_mainStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.private_5cb4f1262a_length_tailCode] at this
  omega

section

private theorem private_2d601c1e00_length_bodiesCode (G : _root_.Light.Compiler.CodeLayout) :
    ∀ (bs : List _root_.ThreeSum1960614.Machine.Light.Stmt) (pos : ℕ), pos + (_root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode G bs pos).length = _root_.ThreeSum1960614.Machine.Light.Compiler.endPos G.F bs pos
  | [], _ => rfl
  | b :: bs, pos => by
    have ih := private_2d601c1e00_length_bodiesCode G bs (pos + b.size G.F + _root_.Light.Compiler.epilogueSize)
    simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode, _root_.ThreeSum1960614.Machine.Light.Compiler.endPos, List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt, _root_.Light.Compiler.length_epilogue]
    omega
end


section parts

variable (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool)

section

private theorem private_84d869635b_length_through_mainCode :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.headCode P dec ++ _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode P p0 dec).length = _root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec := by
  simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.headCode, _root_.Light.Compiler.headStraight, _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode, List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt,
    _root_.ThreeSum1960614.Machine.Light.Compiler.size_mainStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.private_5cb4f1262a_length_tailCode, _root_.ThreeSum1960614.Machine.Light.Compiler.firstBody, _root_.ThreeSum1960614.Machine.Light.Compiler.tailPos, _root_.Light.Compiler.mainPos, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout, List.length_cons,
    List.length_nil]
  omega
end


section

private theorem private_702e8e60fa_length_through_bodiesCode :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.headCode P dec ++ _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode P p0 dec ++
      _root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec)).length = _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec := by
  rw [List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.private_84d869635b_length_through_mainCode]
  exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_2d601c1e00_length_bodiesCode (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P _
end






section

private theorem private_751d1e40fb_codeAt_mainCode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) _root_.Light.Compiler.mainPos (_root_.ThreeSum1960614.Machine.Light.Compiler.mainCode P p0 dec) :=
  (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.codeAt_self _).left.left.left.right
end


/-- The outermost statement is at `mainPos`. -/
theorem codeAt_mainStmt :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) _root_.Light.Compiler.mainPos
      (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) (_root_.ThreeSum1960614.Machine.Light.mainStmt p0) _root_.Light.Compiler.mainPos) :=
  (_root_.ThreeSum1960614.Machine.Light.Compiler.private_751d1e40fb_codeAt_mainCode P p0 dec).left

/-- The code for the verdict follows the outermost statement. -/
theorem codeAt_tailCode :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.tailPos (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P))
      (_root_.Light.Compiler.tailCode dec (_root_.ThreeSum1960614.Machine.Light.Compiler.tailPos (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P))) :=
  (_root_.ThreeSum1960614.Machine.Light.Compiler.private_751d1e40fb_codeAt_mainCode P p0 dec).right.cast_pos (by
    simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.size_mainStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.tailPos, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout])

/-- The bodies begin at `firstBody`. -/
theorem codeAt_bodiesCode :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec)
      (_root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec)) :=
  (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.codeAt_self _).left.left.right.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_84d869635b_length_through_mainCode, Nat.zero_add])

/-- The dispatcher is at `dispPos`. -/
theorem codeAt_dispatcher_dispPos :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.Light.Compiler.dispatcher (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec)) :=
  (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.codeAt_self _).left.right.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_702e8e60fa_length_through_bodiesCode, Nat.zero_add])



end parts

/-- Every body is at its entry, followed by the return sequence, and ends at or before the position
after the bodies. -/
theorem codeAt_bodies {code : List _root_.EndStatement.Instr} (G : _root_.Light.Compiler.CodeLayout) :
    ∀ (bs : List _root_.ThreeSum1960614.Machine.Light.Stmt) (pos : ℕ), _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode G bs pos) →
      ∀ (p : ℕ) (b : _root_.ThreeSum1960614.Machine.Light.Stmt), bs[p]? = some b → ∃ e, (_root_.ThreeSum1960614.Machine.Light.Compiler.entries G.F bs pos)[p]? = some e ∧
        _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code e (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G b e ++ _root_.Light.Compiler.epilogue G) ∧
        e + b.size G.F + _root_.Light.Compiler.epilogueSize ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.endPos G.F bs pos
  | [], _, _, p, b, h => by simp at h
  | b₀ :: bs, pos, hc, 0, b, h => by
    obtain rfl : b₀ = b := by simpa using h
    exact ⟨pos, rfl, hc.left, _root_.ThreeSum1960614.Machine.Light.Compiler.private_61fdf1c7a3_le_endPos _ _ _⟩
  | b₀ :: bs, pos, hc, p + 1, b, h =>
    codeAt_bodies G bs _
      (hc.right.cast_pos (by
        rw [List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt, _root_.Light.Compiler.length_epilogue, Nat.add_assoc])) p b
      (by simpa using h)

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Pieces of a call: the arguments and the new frame

A call first evaluates its arguments into T₀, T₁, … (`effects_argsCode`).  Then it sets up the frame
of the procedure, F + 1 stack cells further on (`effects_newFrame`): NFP receives the new frame
pointer, the local variables of the new frame receive the arguments and zeros
(`effects_frameInit`), the stack cell before the new frame receives the position to return to, and
FP moves to the new frame.  After that the memory represents the state in which the procedure
starts.
-/

public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q : ℕ} {m : ℤ → BitVec W}

/-! ## The arguments -/

/-- The code of the arguments only changes the memory. -/
theorem straight_argsCode : ∀ (es : List _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ), ∀ i ∈ _root_.ThreeSum1960614.Machine.Light.Compiler.argsCode es k, _root_.ThreeSumApsp.WordRam.Straight i
  | [], _ => by simp [_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode]
  | e :: es, k => List.forall_mem_append.2 ⟨_root_.ThreeSum1960614.Machine.Light.Compiler.straight_compileExpr e k, straight_argsCode es (k + 1)⟩



/-! ## The new frame -/

section

/-- The code for one more local variable. -/
private theorem private_cef2144472_frameInit_succ (F' n : ℕ) : _root_.Light.Compiler.frameInit (F' + 1) n = _root_.Light.Compiler.frameInit F' n ++
    [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cNFP (_root_.Light.Compiler.cPool (2 * F')), _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR (if F' < n then _root_.Light.Compiler.cT F' else _root_.Light.Compiler.cZERO)] := by
  simp [_root_.Light.Compiler.frameInit, List.range_succ, List.flatMap_append]
end


section

private theorem private_3716eb0d3d_straight_frameInit (n : ℕ) : ∀ F' : ℕ, ∀ i ∈ _root_.Light.Compiler.frameInit F' n, _root_.ThreeSumApsp.WordRam.Straight i
  | 0 => by simp [_root_.Light.Compiler.frameInit]
  | F' + 1 => by
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_cef2144472_frameInit_succ]
    exact List.forall_mem_append.2 ⟨private_3716eb0d3d_straight_frameInit n F', by simp [_root_.ThreeSumApsp.WordRam.Straight]⟩
end




/-- The code of the new frame only changes the memory. -/
theorem straight_newFrame (F n ret : ℕ) : ∀ i ∈ _root_.Light.Compiler.newFrame F n ret, _root_.ThreeSumApsp.WordRam.Straight i :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨by simp [_root_.ThreeSumApsp.WordRam.Straight], _root_.ThreeSum1960614.Machine.Light.Compiler.private_3716eb0d3d_straight_frameInit n F⟩,
    by simp [_root_.ThreeSumApsp.WordRam.Straight]⟩



end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

section

private theorem private_39e5ba589c_effects_headStraight (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m =
      Function.update (Function.update (Function.update m _root_.Light.Compiler.cONE (_root_.ThreeSumApsp.WordRam.wd W 1)) _root_.Light.Compiler.cZERO (_root_.ThreeSumApsp.WordRam.wd W 0)) _root_.Light.Compiler.cNEG
        (_root_.ThreeSumApsp.WordRam.wd W (-1)) := by
  simp only [_root_.Light.Compiler.headStraight, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil]
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_one, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cZERO (by (repeat
                                                                                                                                                                        (first
                                                                                                                                                                          | rw [_root_.Function.update_self]
                                                                                                                                                                          | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))) (by (repeat
                                                                                                                                                                                       (first
                                                                                                                                                                                         | rw [_root_.Function.update_self]
                                                                                                                                                                                         | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))),
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cNEG (by (repeat
                                                                                                     (first
                                                                                                       | rw [_root_.Function.update_self]
                                                                                                       | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))) (by (repeat
                                                                                                                    (first
                                                                                                                      | rw [_root_.Function.update_self]
                                                                                                                      | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))])))]
  rfl
end




/-! ## The pool -/



section

private theorem private_1689400533_agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Pool N) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.poolCode N) m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (l := _root_.Light.Compiler.poolCode N)
    (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show _root_.Light.Compiler.cPool 0 ∈ _root_.Light.Compiler.Pool N
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
  · have := List.mem_range.1 hn
    show _root_.Light.Compiler.cPool (n + 1) ∈ _root_.Light.Compiler.Pool N
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end




section

/-- The memory after the first three instructions and the code for the pool. -/
private def private_54239f6749_poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.poolCode N) (_root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m)
end


section

private theorem private_ace6a9ccfe_agreeOutside_poolMem (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Constants N) m (_root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.trans_union ?_ (_root_.ThreeSum1960614.Machine.Light.Compiler.private_1689400533_agreeOutside_poolCode N _)
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_39e5ba589c_effects_headStraight]
  exact (((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (by simp) _).update (by simp) _).update (by simp) _
end






/-! ## The outermost frame -/



section

/-- The instructions of `zeroCode` write into the outermost frame. -/
private theorem private_71d3c3537a_writesIn_zeroCode (F : ℕ) : ∀ i ∈ _root_.Light.Compiler.zeroCode F, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn (_root_.Light.Compiler.MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + x) ∈ _root_.Light.Compiler.MainFrame F
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end




section

private theorem private_9d050fcb47_agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside ({_root_.Light.Compiler.cFP} ∪ _root_.Light.Compiler.MainFrame F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode F) m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (l := _root_.Light.Compiler.frameCode F) (List.forall_mem_cons.2 ⟨?_,
    List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_,
      List.forall_mem_singleton.2 ?_⟩⟩⟩) m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (_root_.ThreeSum1960614.Machine.Light.Compiler.private_71d3c3537a_writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 1) ∈ _
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
  · -- local variable 2 := the second argument
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 2) ∈ _
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end




/-! ## The memory in which the outermost statement starts -/



section

private theorem private_1410a86b87_startMem_eq (F N : ℕ) (m : ℤ → BitVec W) :
    _root_.Light.Compiler.startMem F N m = _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode F) (_root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m) := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append _ _ _
end


/-- The start-up code changes only the registers for 1, 0, -1, the pool, FP and the outermost
frame. -/
theorem agreeOutside_startMem (h3 : 3 ≤ F) (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Constants N ∪ ({_root_.Light.Compiler.cFP} ∪ _root_.Light.Compiler.MainFrame F)) m (_root_.Light.Compiler.startMem F N m) :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.private_1410a86b87_startMem_eq F N m ▸ (_root_.ThreeSum1960614.Machine.Light.Compiler.private_ace6a9ccfe_agreeOutside_poolMem N m).trans_union (_root_.ThreeSum1960614.Machine.Light.Compiler.private_9d050fcb47_agreeOutside_frameCode h3 _)



/-! ## The run from the first instruction to the outermost statement -/









end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler is correct on statements: the simulation theorem

A run of a statement of the light language in c steps is matched by a run of its code in at most
stepsPerStep · c steps of the machine (`sim`).

What never changes (the program, its code, the numbers of `Sizes`, and the facts that the code is in
place and that a frame is wide enough for the text) forms the structure `Setting`.  The situation
before the code of a statement runs is `Start`: the code is at pos, and the memory represents the
state in the frame q, with room on the stack for the calls still allowed.  The situation afterwards
is `Finished`: the machine has reached the position after the code, the memory represents the new
state in the same frame, and only cells that the statement may write have changed.  `Simulates` says
that `Start` leads to `Finished`.

The theorem is an induction on the run, with one lemma for each rule of the semantics: `sim_skip`,
`sim_set`, `sim_store`, `sim_seq`, `sim_iteTrue`, `sim_iteFalse`, `sim_whileFalse`,
`sim_whileTrue`, `sim_call`.  Each of them first takes the code of the statement apart (`codeAt_ite`
and its like say where the parts are) and then runs the parts in turn.  A call has four parts.
Enter (`steps_callEnter`): arguments, new frame, position to return to, jump.  The body: the
induction hypothesis.  Leave (`steps_callLeave`): return sequence and dispatcher.  Store the result
in the caller's variable (`steps_setVar`).

In the proofs S is the setting and B the situation at the start; the other letters are as in the
file on the cells.
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## Where the parts of the code of a statement are -/

section layout

variable {code : List _root_.EndStatement.Instr} {G : _root_.Light.Compiler.CodeLayout} {pos x p : ℕ} {e : _root_.ThreeSum1960614.Machine.Light.Expr} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s t : _root_.ThreeSum1960614.Machine.Light.Stmt}
  {args : List _root_.ThreeSum1960614.Machine.Light.Expr}

section

/-- The code of e, and the two instructions that store T₀ in x. -/
private theorem private_6e20212e35_codeAt_set (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e) pos)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e 0) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + e.size) [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cFP (_root_.Light.Compiler.cPool (2 * x)), _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR (_root_.Light.Compiler.cT 0)] :=
  ⟨h.left, h.right.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr])⟩
end


section

/-- The code of s, and the code of t. -/
private theorem private_ed72a3e8b9_codeAt_seq (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G (_root_.ThreeSum1960614.Machine.Light.Stmt.seq s t) pos)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G s pos) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + s.size G.F) (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G t (pos + s.size G.F)) :=
  ⟨h.left, h.right.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt])⟩
end


section

/-- The test, the first branch, the jump over the second branch, the second branch. -/
private theorem private_c3e1229152_codeAt_ite (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t) pos)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c (pos + c.size + s.size G.F + 1)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + c.size) (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G s (pos + c.size)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + c.size + s.size G.F)
        [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + c.size + s.size G.F + 1)
        (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G t (pos + c.size + s.size G.F + 1)) := by
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt] at h
  refine ⟨h.left.left.left, h.left.left.right.cast_pos ?_, h.left.right.cast_pos ?_,
    h.right.cast_pos ?_⟩ <;> simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.length_compileCond, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt]
end


section

/-- The test, the body, the jump back. -/
private theorem private_beff3fb097_codeAt_while (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) pos)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c (pos + c.size + s.size G.F + 1)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + c.size) (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G s (pos + c.size)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + c.size + s.size G.F) [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG pos] := by
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.length_compileCond, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt]
end


section

/-- The arguments and the new frame, the jump to the procedure, and the two instructions that store
the result. -/
private theorem private_f47039182a_codeAt_call (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) pos)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode args 0 ++ _root_.Light.Compiler.newFrame G.F args.length (pos + _root_.ThreeSum1960614.Machine.Light.Compiler.callSize G.F args)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + (_root_.ThreeSum1960614.Machine.Light.Compiler.argsSize args + (2 * G.F + 4))) [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG (G.entry.getD p 0)] ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + _root_.ThreeSum1960614.Machine.Light.Compiler.callSize G.F args)
        [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cFP (_root_.Light.Compiler.cPool (2 * x)), _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR _root_.Light.Compiler.cRET] := by
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.callCode] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.length_argsCode, _root_.Light.Compiler.length_newFrame, _root_.ThreeSum1960614.Machine.Light.Compiler.callSize]
end


end layout

/-! ## The setting -/





section

/-- At most n machine steps are within the bound for c ≥ 1 steps of the language. -/
private theorem private_6a0aa662a2_le_stepsPerStep_mul {a c n : ℕ} (h : a ≤ n) (hc : 1 ≤ c) :
    a ≤ _root_.Light.Compiler.stepsPerStep n * c :=
  calc a ≤ _root_.Light.Compiler.stepsPerStep n * 1 := by rw [_root_.Light.Compiler.stepsPerStep]; omega
    _ ≤ _root_.Light.Compiler.stepsPerStep n * c := Nat.mul_le_mul_left _ hc
end


section

/-- At most n machine steps, followed by b machine steps that are within the bound for k steps, are
within the bound for c + k steps if c ≥ 1. -/
private theorem private_de1fd4dadb_add_le_stepsPerStep_mul {a b c k n : ℕ} (h : a ≤ n) (hc : 1 ≤ c)
    (hb : b ≤ _root_.Light.Compiler.stepsPerStep n * k) : a + b ≤ _root_.Light.Compiler.stepsPerStep n * (c + k) :=
  Nat.mul_add _ c k ▸ Nat.add_le_add (_root_.ThreeSum1960614.Machine.Light.Compiler.private_6a0aa662a2_le_stepsPerStep_mul h hc) hb
end


section

/-- The count for a call whose code is at pos and has size + 2 instructions: size steps to enter, b
for the body, r + 2 (pos + size + 1) to leave, where r is the length of the return sequence, and 2
to store the result.  The cost a of the arguments is not needed. -/
private theorem private_a97be00aad_call_le_stepsPerStep_mul {pos size b r a k n : ℕ} (hpos : pos + (size + 2) ≤ n)
    (hr : r ≤ n) (hb : b ≤ _root_.Light.Compiler.stepsPerStep n * k) :
    size + b + (r + 2 * (pos + size + 1)) + 2 ≤ _root_.Light.Compiler.stepsPerStep n * (a + 2 + k) := by
  rw [Nat.mul_add (_root_.Light.Compiler.stepsPerStep n), Nat.mul_add (_root_.Light.Compiler.stepsPerStep n)]
  have hK : _root_.Light.Compiler.stepsPerStep n * 2 = 4 * n := by rw [_root_.Light.Compiler.stepsPerStep]; omega
  omega
end


variable {W : ℕ} (S : _root_.ThreeSum1960614.Machine.Light.Compiler.Setting W)







variable {S} {d pos q : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' σ₁ σ₂ : _root_.ThreeSum1960614.Machine.Light.State} {m : ℤ → BitVec W}

section


/-- The situation before a part t of the statement runs, in the same frame. -/
private theorem Start.private_e37f23946c_sub (B : _root_.ThreeSum1960614.Machine.Light.Compiler.Start S d s σ pos q m) {t : _root_.ThreeSum1960614.Machine.Light.Stmt} {pos' : ℕ} {m' : ℤ → BitVec W}
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt S.code pos' (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt S.toCodeLayout t pos'))
    (hpos : pos' + t.size S.F ≤ S.disp) (hw : t.width ≤ S.F) (hσ : σ'.Bounded S.lim)
    (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel S.toSizes σ' q m') : _root_.ThreeSum1960614.Machine.Light.Compiler.Start S d t σ' pos' q m' :=
  { rel := R, low := B.low, high := B.high, codeAt := hcode, below := hpos, width := hw,
    bounded := hσ, room := B.room }
end


section


/-- The room on the stack, seen from the frame of a procedure that is called. -/
private theorem Start.private_51fe0680ea_room_succ (B : _root_.ThreeSum1960614.Machine.Light.Compiler.Start S d s σ pos q m) (hd : d < S.lim.depth) :
    q + S.F + 1 + S.F + (S.F + 1) * (S.lim.depth - (d + 1)) ≤ S.Q := by
  have := B.room
  rw [show S.lim.depth - d = S.lim.depth - (d + 1) + 1 by omega, Nat.mul_succ] at this
  omega
end


section


/-- The test of an if or a while that is at pos. -/
private theorem Start.private_ed349007b2_test (B : _root_.ThreeSum1960614.Machine.Light.Compiler.Start S d s σ pos q m) {c : _root_.ThreeSum1960614.Machine.Light.Cond} {l : ℕ}
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt S.code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c l)) (hw : c.width ≤ S.F) (hs : c.Safe S.lim σ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Decides S.code S.F pos c.size l m (c.Holds σ) :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.decides_compileCond B.toFramed B.bounded c hcode hw hs
end


/-! ## Statements without calls -/

section

/-- skip: no code, no step. -/
private theorem private_632589ac73_sim_skip : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d _root_.ThreeSum1960614.Machine.Light.Stmt.skip σ σ 0 := fun _ _ m B =>
  ⟨m, 0, { run := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps.refl _, le := Nat.zero_le _, rel := B.rel, agree := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m }⟩
end


section

/-- x := e: the code of e leaves the value in T₀, and two instructions store it in x. -/
private theorem private_fdf8b3cade_sim_set {x : ℕ} {e : _root_.ThreeSum1960614.Machine.Light.Expr} (hs : e.Safe S.lim σ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) }
      (e.cost + 1) := by
  intro pos q m B
  obtain ⟨hx, he⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_set_le_iff.1 B.width
  obtain ⟨exprCode, setCode⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_6e20212e35_codeAt_set B.codeAt
  have hpos : pos + (e.size + 2) ≤ S.disp := B.below
  -- T₀ := e
  obtain ⟨val, A⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.effects_compileExpr_of_width B.toFramed e 0 he hs (by omega)
  have A₁ := A.mono _root_.ThreeSum1960614.Machine.Light.Compiler.temps_subset_scratch
  have run₁ := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_straight _ pos m exprCode (_root_.ThreeSum1960614.Machine.Light.Compiler.straight_compileExpr e 0)
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr] at run₁
  -- x := T₀
  obtain ⟨m₂, run₂, R₂, A₂⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.steps_setVar (B.toFramed.same A₁) hx setCode val (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
  exact ⟨m₂, _, {
    run := (run₁.trans run₂).cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Stmt.size, Nat.add_assoc])
    le := _root_.ThreeSum1960614.Machine.Light.Compiler.private_6a0aa662a2_le_stepsPerStep_mul (by omega) (by omega)
    rel := R₂
    agree := (A₁.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable).trans A₂ }⟩
end


section

/-- The cell at a := e: the code of a and e leaves the values in T₀ and T₁, and one instruction
stores. -/
private theorem private_2cc5d36d81_sim_store {a e : _root_.ThreeSum1960614.Machine.Light.Expr} (hsa : a.Safe S.lim σ) (hse : e.Safe S.lim σ)
    (haddr : S.lim.Addr (a.val σ)) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e) σ
      { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } (a.cost + e.cost + 1) := by
  intro pos q m B
  obtain ⟨ha, he⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_store_le_iff.1 B.width
  have hpos : pos + (a.size + e.size + 1) ≤ S.disp := B.below
  -- T₀ := a; T₁ := e
  obtain ⟨m₁, run₁, va, ve, A₁⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.steps_pair B.toFramed B.codeAt ha he hsa hse
  -- the cell at T₀ := T₁
  have run₂ := run₁.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_store (_root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_after_pair B.codeAt) va (S.inRange_addr haddr))
  rw [ve] at run₂
  exact ⟨_, _, {
    run := run₂.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Stmt.size, Nat.add_assoc])
    le := _root_.ThreeSum1960614.Machine.Light.Compiler.private_6a0aa662a2_le_stepsPerStep_mul (by omega) (by omega)
    rel := (B.rel.same A₁).setMem B.low haddr _
    agree := (A₁.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable).update (_root_.ThreeSum1960614.Machine.Light.Compiler.mem_writable_of_addr haddr) _ }⟩
end


section

/-- s₁; s₂: the code of s₁, then the code of s₂. -/
private theorem private_c4689c8c9b_sim_seq {c₁ c₂ : ℕ} (h₁ : _root_.ThreeSum1960614.Machine.Light.Exec S.lim S.P d s₁ σ σ₁ c₁)
    (ih₁ : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d s₁ σ σ₁ c₁) (ih₂ : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d s₂ σ₁ σ₂ c₂) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂) σ σ₂ (c₁ + c₂) := by
  intro pos q m B
  obtain ⟨hw₁, hw₂⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_seq_le_iff.1 B.width
  obtain ⟨firstCode, secondCode⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ed72a3e8b9_codeAt_seq B.codeAt
  have hpos : pos + (s₁.size S.F + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _ (B.private_e37f23946c_sub firstCode (by omega) hw₁ B.bounded B.rel)
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih₂ _ _ _
    (B.private_e37f23946c_sub secondCode (by omega) hw₂ (h₁.bounded B.bounded) R₁)
  exact ⟨m₂, n₁ + n₂, {
    run := (run₁.trans run₂).cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Stmt.size, Nat.add_assoc])
    le := Nat.mul_add _ c₁ c₂ ▸ Nat.add_le_add le₁ le₂
    rel := R₂
    agree := A₁.trans A₂ }⟩
end


section

/-- if c then s₁ else s₂, when c holds: the test goes on to the code of s₁, and a jump leads over
the code of s₂. -/
private theorem private_3e73f9f644_sim_iteTrue {c : _root_.ThreeSum1960614.Machine.Light.Cond} {k : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (ih : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d s₁ σ σ' k) : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, hw₁, -⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, thenCode, jumpCode, -⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_c3e1229152_codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.private_ed349007b2_test testCode hwc hs).of_holds holds
  -- the first branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.private_e37f23946c_sub thenCode (by omega) hw₁ B.bounded (B.rel.same A₀))
  -- the jump over the second branch
  have run₂ := (run₀.trans run₁).trans (_root_.ThreeSum1960614.Machine.Light.Compiler.steps_jump jumpCode R₁.neg S.inRange_neg_one)
  exact ⟨m₁, n₀ + 1 + n₁, {
    run := (run₂.cast_count (by omega)).cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Stmt.size]; omega)
    le := _root_.ThreeSum1960614.Machine.Light.Compiler.private_de1fd4dadb_add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable).trans A₁ }⟩
end


section

/-- if c then s₁ else s₂, when c fails: the test jumps to the code of s₂. -/
private theorem private_97ae231e95_sim_iteFalse {c : _root_.ThreeSum1960614.Machine.Light.Cond} {k : ℕ} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ)
    (ih : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d s₂ σ σ' k) : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, -, hw₂⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, -, -, elseCode⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_c3e1229152_codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.private_ed349007b2_test testCode hwc hs).of_fails fails
  -- the second branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.private_e37f23946c_sub elseCode (by omega) hw₂ B.bounded (B.rel.same A₀))
  exact ⟨m₁, n₀ + n₁, {
    run := (run₀.trans run₁).cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Stmt.size]; omega)
    le := _root_.ThreeSum1960614.Machine.Light.Compiler.private_de1fd4dadb_add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable).trans A₁ }⟩
end


section

/-- while c do s, when c fails: the test jumps to the position after the loop. -/
private theorem private_8b75f8f268_sim_whileFalse {c : _root_.ThreeSum1960614.Machine.Light.Cond} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ σ (c.cost + 1) := by
  intro pos q m B
  obtain ⟨hwc, -⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, -, -⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_beff3fb097_codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.private_ed349007b2_test testCode hwc hs).of_fails fails
  exact ⟨m₀, n₀, {
    run := run₀.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Stmt.size]; omega)
    le := _root_.ThreeSum1960614.Machine.Light.Compiler.private_6a0aa662a2_le_stepsPerStep_mul (by omega) (by omega)
    rel := B.rel.same A₀
    agree := A₀.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable }⟩
end


section

/-- while c do s, when c holds: the test goes on to the code of s, a jump leads back to the test,
and the loop runs again. -/
private theorem private_c1fa6bf845_sim_whileTrue {c : _root_.ThreeSum1960614.Machine.Light.Cond} {k₁ k₂ : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (h₁ : _root_.ThreeSum1960614.Machine.Light.Exec S.lim S.P d s σ σ₁ k₁) (ih₁ : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d s σ σ₁ k₁)
    (ih₂ : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ₁ σ₂ k₂) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ σ₂ (c.cost + 1 + k₁ + k₂) := by
  intro pos q m B
  obtain ⟨hwc, hw⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, bodyCode, jumpCode⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_beff3fb097_codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.private_ed349007b2_test testCode hwc hs).of_holds holds
  -- the body
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _
    (B.private_e37f23946c_sub bodyCode (by omega) hw B.bounded (B.rel.same A₀))
  -- the jump back
  have run₂ := (run₀.trans run₁).trans (_root_.ThreeSum1960614.Machine.Light.Compiler.steps_jump jumpCode R₁.neg S.inRange_neg_one)
  -- the loop again
  obtain ⟨m₃, n₃, run₃, le₃, R₃, A₃⟩ := ih₂ _ _ _
    (B.private_e37f23946c_sub B.codeAt B.below B.width (h₁.bounded B.bounded) R₁)
  exact ⟨m₃, n₀ + 1 + n₁ + n₃, {
    run := (run₂.trans run₃).cast_count (by omega)
    le := Nat.mul_add _ _ k₂ ▸ Nat.add_le_add (_root_.ThreeSum1960614.Machine.Light.Compiler.private_de1fd4dadb_add_le_stepsPerStep_mul (by omega) (by omega) le₁)
        le₃
    rel := R₃
    agree := ((A₀.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable).trans A₁).trans A₃ }⟩
end


/-! ## Calls -/

section call

variable {p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr}

section

/-- Entering a procedure: the arguments, the new frame with the position to return to, and the jump
to the entry e.  Afterwards the memory represents the state in which the procedure starts, in the
frame q + F + 1, and the stack cell before that frame holds the position after the jump.  Of the
stack, only cells from q + F on have changed. -/
private theorem private_7a21b7a4d9_steps_callEnter (B : _root_.ThreeSum1960614.Machine.Light.Compiler.Start S d (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) σ pos q m)
    (hsa : ∀ e ∈ args, e.Safe S.lim σ) (hd : d < S.lim.depth) {e : ℕ}
    (he : S.entry[p]? = some e) :
    ∃ m₂, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps S.code (_root_.ThreeSum1960614.Machine.Light.Compiler.callSize S.F args) ⟨pos, m⟩ ⟨e, m₂⟩ ∧
      _root_.ThreeSum1960614.Machine.Light.Compiler.Rel S.toSizes ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ (q + S.F + 1) m₂ ∧
      m₂ (_root_.Light.Compiler.cStack (q + S.F)) = _root_.ThreeSumApsp.WordRam.wd W ((pos + _root_.ThreeSum1960614.Machine.Light.Compiler.callSize S.F args : ℕ) : ℤ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.ThreeSum1960614.Machine.Light.Compiler.Writable S.toSizes (q + S.F)) m m₂ := by
  obtain ⟨-, hlen, hwa⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_call_le_iff.1 B.width
  obtain ⟨frameCode, jumpCode, -⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_f47039182a_codeAt_call B.codeAt
  have hpos : pos + (_root_.ThreeSum1960614.Machine.Light.Compiler.callSize S.F args + 2) ≤ S.disp := B.below
  rw [List.getD_eq_getElem?_getD, he, Option.getD_some] at jumpCode
  -- the arguments: there are at most F of them, each of width at most F
  obtain ⟨vals, A⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.effects_argsCode B.toFramed args 0 hwa hsa (by omega)
  have A₁ := A.mono _root_.ThreeSum1960614.Machine.Light.Compiler.temps_subset_scratch
  -- the new frame
  obtain ⟨R₂, hret, A₂⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.effects_newFrame (B.toFramed.same A₁)
    ((Nat.le_add_right _ _).trans (B.private_51fe0680ea_room_succ hd)) args (by simpa using vals)
    (ret := pos + _root_.ThreeSum1960614.Machine.Light.Compiler.callSize S.F args) (by omega)
  have run₂ := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_straight _ pos m frameCode
    (List.forall_mem_append.2 ⟨_root_.ThreeSum1960614.Machine.Light.Compiler.straight_argsCode _ _, _root_.ThreeSum1960614.Machine.Light.Compiler.straight_newFrame _ _ _⟩)
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_argsCode, _root_.Light.Compiler.length_newFrame] at run₂
  -- the jump
  exact ⟨_, (run₂.trans (_root_.ThreeSum1960614.Machine.Light.Compiler.steps_jump jumpCode R₂.neg S.inRange_neg_one)).cast_count
    (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.callSize]; omega), R₂, hret, (A₁.mono _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable).trans A₂⟩
end


section

/-- Leaving a procedure whose frame is q + F + 1, when the stack cell before that frame holds the
position ret: the return sequence and the dispatcher.  The machine arrives at ret; RET holds the
result (local variable 0), FP points to the frame q, and otherwise only scratch cells have
changed. -/
private theorem private_083d69c032_steps_callLeave (S : _root_.ThreeSum1960614.Machine.Light.Compiler.Setting W) {ret : ℕ} (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel S.toSizes σ (q + S.F + 1) m)
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt S.code pos (_root_.Light.Compiler.epilogue S.toCodeLayout))
    (hret : m (_root_.Light.Compiler.cStack (q + S.F)) = _root_.ThreeSumApsp.WordRam.wd W ret) (hlt : ret < S.disp) (hQ : q + S.F + 1 ≤ S.Q)
    (hF : 0 < S.F) :
    ∃ m', _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps S.code (_root_.Light.Compiler.epilogueSize + 2 * (ret + 1)) ⟨pos, m⟩ ⟨ret, m'⟩ ∧
      m' _root_.Light.Compiler.cFP = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack q) ∧ m' _root_.Light.Compiler.cRET = _root_.ThreeSumApsp.WordRam.wd W (σ.loc 0) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (insert _root_.Light.Compiler.cFP (_root_.Light.Compiler.Scratch S.F)) m m' := by
  have hN := S.offsets_le
  -- RET := the cell at FP, which is local variable 0
  have run₁ := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_load (i := _root_.Light.Compiler.cRET) hcode R.fp (S.inRange_stack hQ)
  rw [R.loc_zero hF] at run₁
  have A₁ := (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl (_root_.Light.Compiler.Scratch S.F) m).update (a := _root_.Light.Compiler.cRET) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (_root_.ThreeSumApsp.WordRam.wd W (σ.loc 0))
  -- ADDR := FP + 2, the address of the stack cell before the frame
  have run₂ := run₁.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_add hcode.tail (R.same A₁).fp ((R.same A₁).pool 2 (by omega)))
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.cStack_succ_add] at run₂
  have A₂ := A₁.update (a := _root_.Light.Compiler.cADDR) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (_root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack (q + S.F)))
  -- RR := the cell at ADDR, which holds ret
  have run₃ := run₂.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_load hcode.tail.tail (Function.update_self _ _ _)
    (S.inRange_stack (by omega)))
  rw [A₂.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hret] at run₃
  have A₃ := A₂.update (a := _root_.Light.Compiler.cRR) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (_root_.ThreeSumApsp.WordRam.wd W ret)
  -- FP := FP + 2 (F + 1), the frame of the caller
  have run₄ := run₃.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_add hcode.tail.tail.tail (R.same A₃).fp ((R.same A₃).pool _ hN))
  rw [Nat.add_assoc q, _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_add] at run₄
  -- the jump to the dispatcher
  have run₅ := run₄.trans (_root_.ThreeSum1960614.Machine.Light.Compiler.steps_jump hcode.tail.tail.tail.tail
    (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact (R.same A₃).neg))) S.inRange_neg_one)
  -- the dispatcher, which leaves -1 in RR
  have run₆ := run₅.trans (_root_.ThreeSum1960614.Machine.Light.Compiler.steps_dispatcher S.dispatcherAt hlt S.fits.pool_lt _
    (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact (R.same A₃).one))) (by (repeat
                                                (first
                                                  | rw [_root_.Function.update_self]
                                                  | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))))
  exact ⟨_, run₆, by (repeat
                        (first
                          | rw [_root_.Function.update_self]
                          | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))])), by (repeat
                                      (first
                                        | rw [_root_.Function.update_self]
                                        | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))])),
    ((A₃.mono (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _⟩
end


section

/-- x := p(args): enter, the body, leave, store the result. -/
private theorem private_8301884f89_sim_call {body : _root_.ThreeSum1960614.Machine.Light.Stmt} {k : ℕ} (hsa : ∀ e ∈ args, e.Safe S.lim σ)
    (hp : S.P[p]? = some body) (hd : d < S.lim.depth)
    (ih : _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S (d + 1) body ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ σ' k) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
      ((args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 2 + k) := by
  intro pos q m B
  obtain ⟨hx, -, -⟩ := _root_.ThreeSum1960614.Machine.Light.Stmt.width_call_le_iff.1 B.width
  obtain ⟨e, he, procCode, hend⟩ := S.bodyAt p body hp
  obtain ⟨-, -, resultCode⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_f47039182a_codeAt_call B.codeAt
  have hpos : pos + (_root_.ThreeSum1960614.Machine.Light.Compiler.callSize S.F args + 2) ≤ S.disp := B.below
  have hq := B.low
  have hroom := B.private_51fe0680ea_room_succ hd
  -- enter
  obtain ⟨m₁, run₁, R₁, hret, A₁⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_7a21b7a4d9_steps_callEnter B hsa hd he
  -- the body, in the frame q + F + 1
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih e (q + S.F + 1) m₁
    { rel := R₁, low := by omega, high := by omega, codeAt := procCode.left, below := by omega,
      width := S.width body (List.mem_of_getElem? hp),
      bounded := _root_.ThreeSum1960614.Machine.Light.bounded_callFrame B.bounded args hsa, room := hroom }
  -- the body writes the stack only from its frame on, so the position to return to is still there
  have hret₂ := A₂.read (a := _root_.Light.Compiler.cStack (q + S.F)) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hret
  -- leave
  obtain ⟨m₃, run₃, hfp, hres, A₃⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_083d69c032_steps_callLeave S R₂
    (procCode.right.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt])) hret₂ (by omega) (by omega)
    (Nat.zero_lt_of_lt hx)
  -- since the call began, the stack has changed only from cell q + F on: the local variables of the
  -- caller are as before, and the memory is as the procedure left it
  have A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.ThreeSum1960614.Machine.Light.Compiler.Writable S.toSizes (q + S.F)) m m₃ :=
    (A₁.trans (A₂.mono (_root_.ThreeSum1960614.Machine.Light.Compiler.writable_subset_writable (by omega)))).trans
      (A₃.mono (Set.insert_subset (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _root_.ThreeSum1960614.Machine.Light.Compiler.scratch_subset_writable))
  have I₃ : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed S.toSizes ⟨σ.loc, σ'.mem⟩ q m₃ := ⟨R₂.of_agreeOutside A₃ (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) hfp
    (fun y hy => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (B.rel.loc y hy))
    fun a ha => A₃.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R₂.mem a ha), hq, B.high⟩
  -- store the result
  obtain ⟨m₄, run₄, R₄, A₄⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.steps_setVar I₃ hx resultCode hres (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
  exact ⟨m₄, _, {
    run := (((run₁.trans run₂).trans run₃).trans run₄).cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Stmt.size, Nat.add_assoc])
    le := _root_.ThreeSum1960614.Machine.Light.Compiler.private_a97be00aad_call_le_stepsPerStep_mul hpos (by omega) le₂
    rel := R₄
    agree := (A.mono (_root_.ThreeSum1960614.Machine.Light.Compiler.writable_subset_writable (by omega))).trans A₄ }⟩
end


end call

/-! ## The theorem -/

/-- **The simulation theorem.**  The code of a statement matches every run of the statement. -/
theorem sim (S : _root_.ThreeSum1960614.Machine.Light.Compiler.Setting W) {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec S.lim S.P d s σ σ' c) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Simulates S d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_632589ac73_sim_skip
  | set hs => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_fdf8b3cade_sim_set hs
  | store hsa hse haddr => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_2cc5d36d81_sim_store hsa hse haddr
  | seq h₁ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_c4689c8c9b_sim_seq h₁ ih₁ ih₂
  | iteTrue hs holds _ ih => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_3e73f9f644_sim_iteTrue hs holds ih
  | iteFalse hs fails _ ih => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_97ae231e95_sim_iteFalse hs fails ih
  | whileFalse hs fails => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_8b75f8f268_sim_whileFalse hs fails
  | whileTrue hs holds h₁ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_c1fa6bf845_sim_whileTrue hs holds h₁ ih₁ ih₂
  | call hsa hp hd _ ih => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_8301884f89_sim_call hsa hp hd ih

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler is correct on whole programs

`compileProgram_correct`: if the call of procedure p0 of the light program P ends after c
steps, the compiled program gives its verdict within `ramSteps P dec c` = c₀ + K c steps, where c₀
and K depend on the text of P (and on dec) only.  If the memory of the machine held the memory of
the light program and the two arguments before (`Input`), it holds the final memory afterwards, with
the result in the cell -3 (`Outcome`).

The run of the machine has three parts.

1. The start-up code (`steps_start`) leads to a memory that represents the first state
   (`rel_startMem`).
2. The outermost statement is the call of p0.  The compiled program satisfies what the simulation
   theorem assumes (`setting`, `start_mainStmt`), so `sim` gives a run of at most K c steps to a
   memory that represents the last state.
3. The code that follows copies the result to the cell -3 and gives the verdict (`steps_tail`).

Each part comes with the set of cells that it may change.  The cells below `-lowCell` and the cells
from `lim.space` on are in none of the three sets (`not_mem_of_far`), and neither are the cells -1
and -2.

The notions of the compiler and of its proof are in the namespace `Light.Compiler`.  The statements
about programs name four of them, which are in `Light`: `compileProgram`, `mainStmt`, `verdictOf`,
`ramSteps`.  The passage to the notions of the word RAM also uses `compileProgram_correct` with
`Fits`, `Holds`, `Input` and `Outcome`, the cells `cARG1`, `cARG2`, `cRESULT`, and the numbers
`startCost`, `stepsPerStep`, `dispPos`, `frameSize`, `stackCells`, `lowCell`.
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec

variable {W : ℕ}

/-! ## The verdict -/



section

/-- What the code that follows the outermost statement leaves, if it starts in the memory m and the
result is r: the machine is about to give the verdict, the cell `cRESULT` holds the result, and only
that cell and the register D have changed. -/
private structure private_99e9c1f405_Verdict (code : List _root_.EndStatement.Instr) (dec : Bool) (r : ℤ) (m : ℤ → BitVec W)
    (cfg : _root_.ThreeSumApsp.WordRam.Cfg W) : Prop where
  verdict : _root_.ThreeSumApsp.WordRam.step code cfg = .inr (_root_.Light.verdictOf dec r)
  result : cfg.mem _root_.Light.Compiler.cRESULT = _root_.ThreeSumApsp.WordRam.wd W r
  agree : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside {_root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cD} m cfg.mem
end


section

/-- The code that follows the outermost statement gets there in at most three steps. -/
private theorem private_715aae6e9a_steps_tail {code : List _root_.EndStatement.Instr} {pos : ℕ} {dec : Bool}
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.Light.Compiler.tailCode dec pos)) {m : ℤ → BitVec W} {r : ℤ}
    (hres : m (_root_.Light.Compiler.cStack _root_.Light.Compiler.mainFrame) = _root_.ThreeSumApsp.WordRam.wd W r) (hzero : m _root_.Light.Compiler.cZERO = _root_.ThreeSumApsp.WordRam.wd W 0) (hr : _root_.ThreeSumApsp.WordRam.InRange W (-r)) :
    ∃ (n : ℕ) (cfg : _root_.ThreeSumApsp.WordRam.Cfg W), n ≤ 3 ∧ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code n ⟨pos, m⟩ cfg ∧ _root_.ThreeSum1960614.Machine.Light.Compiler.private_99e9c1f405_Verdict code dec r m cfg := by
  -- the cell for the result := the result
  have copy : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m _root_.Light.Compiler.cRESULT (_root_.ThreeSumApsp.WordRam.wd W r)⟩ :=
    add_zero r ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_add hcode hres hzero
  cases dec with
  | false =>
    -- accept
    have read : Function.update m _root_.Light.Compiler.cRESULT (_root_.ThreeSumApsp.WordRam.wd W r) _root_.Light.Compiler.cRESULT = _root_.ThreeSumApsp.WordRam.wd W r := Function.update_self ..
    exact ⟨1, _, by omega, copy, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.step_accept hcode.tail.head, read,
      (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (by simp) _⟩
  | true =>
    have rest : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code (pos + 1)
      [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cD _root_.Light.Compiler.cZERO (_root_.Light.Compiler.cStack _root_.Light.Compiler.mainFrame), _root_.EndStatement.Instr.bltz _root_.Light.Compiler.cD (pos + 4), _root_.EndStatement.Instr.reject, _root_.EndStatement.Instr.accept] := hcode.tail
    -- D := 0 - the result; go to accept if D < 0; reject
    have run := (copy.trans (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_sub rest (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact hzero)))
      (by ((repeat (first | rw [_root_.Function.update_self] | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]); exact hres))))).trans
      (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_bltz rest.tail (Function.update_self ..) (by rwa [zero_sub]))
    have keep : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside {_root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cD} m
        (Function.update (Function.update m _root_.Light.Compiler.cRESULT (_root_.ThreeSumApsp.WordRam.wd W r)) _root_.Light.Compiler.cD (_root_.ThreeSumApsp.WordRam.wd W (0 - r))) :=
      ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (by simp) _).update (by simp) _
    have read : Function.update (Function.update m _root_.Light.Compiler.cRESULT (_root_.ThreeSumApsp.WordRam.wd W r)) _root_.Light.Compiler.cD (_root_.ThreeSumApsp.WordRam.wd W (0 - r)) _root_.Light.Compiler.cRESULT =
        _root_.ThreeSumApsp.WordRam.wd W r := by
      (repeat
         (first
           | rw [_root_.Function.update_self]
           | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))
    by_cases hpos : 0 < r
    · rw [if_pos (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.step_accept rest.tail.tail.tail.head).trans (by simp [_root_.Light.verdictOf, hpos]), read, keep⟩
    · rw [if_neg (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.step_reject rest.tail.tail.head).trans (by simp [_root_.Light.verdictOf, hpos]), read, keep⟩
end


/-! ## Time and space of the compiled program -/









section

private theorem private_d2e33001c5_frame_le_stackCells (P : _root_.ThreeSum1960614.Machine.Light.Program) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) :
    _root_.Light.Compiler.mainFrame + _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 1 ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim := by
  have := Nat.le_mul_of_pos_right (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 1) (show 0 < lim.depth + 1 by omega)
  unfold _root_.ThreeSum1960614.Machine.Light.Compiler.stackCells
  omega
end


/-! ## The setting of the simulation theorem -/

section setting

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p0 : ℕ} {dec : Bool}

section

/-- The compiled program, with its numbers, satisfies what the simulation theorem assumes once and
for all. -/
private def private_960ac446a9_setting (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool)
    (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim)) : _root_.ThreeSum1960614.Machine.Light.Compiler.Setting W where
  toCodeLayout := _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec
  lim := lim
  Q := _root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim
  fits := hfit
  offsets_le := by
    have := _root_.ThreeSum1960614.Machine.Light.Compiler.two_mul_frameSize_add_le_dispPos P dec
    simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout]
    omega
  P := P
  code := _root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec
  bodyAt := _root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_bodies (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P _ (_root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_bodiesCode P p0 dec)
  dispatcherAt := _root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_dispatcher_dispPos P p0 dec
  width _ hb := _root_.ThreeSum1960614.Machine.Light.Compiler.width_le_frameSize hb
end


variable (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim))

section

/-- The outermost statement is at `mainPos` and runs in the frame `mainFrame`. -/
private theorem private_2d8e51b305_start_mainStmt {σ : _root_.ThreeSum1960614.Machine.Light.State} {m : ℤ → BitVec W} (hσ : σ.Bounded lim)
    (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel (_root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting P p0 dec hfit).toSizes σ _root_.Light.Compiler.mainFrame m) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Start (_root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting P p0 dec hfit) 0 (_root_.ThreeSum1960614.Machine.Light.mainStmt p0) σ _root_.Light.Compiler.mainPos _root_.Light.Compiler.mainFrame m where
  rel := R
  low := by decide
  high := (Nat.le_succ _).trans (_root_.ThreeSum1960614.Machine.Light.Compiler.private_d2e33001c5_frame_le_stackCells P lim)
  codeAt := _root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_mainStmt P p0 dec
  below := by
    have := _root_.ThreeSum1960614.Machine.Light.Compiler.two_mul_frameSize_add_le_dispPos P dec
    simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.size_mainStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout, _root_.Light.Compiler.mainPos]
    omega
  width := (_root_.ThreeSum1960614.Machine.Light.Compiler.width_mainStmt p0).trans_le (_root_.ThreeSum1960614.Machine.Light.Compiler.three_le_frameSize P)
  bounded := hσ
  room := by
    simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout, _root_.ThreeSum1960614.Machine.Light.Compiler.stackCells, Nat.sub_zero, Nat.mul_succ]
    omega
end


section

/-- The cells below `-lowCell` and the cells from `lim.space` on are not among those that the
start-up code, the outermost statement or the code for the verdict may change. -/
private theorem private_6f9d786750_not_mem_of_far {a : ℤ}
    (ha : a < -(_root_.ThreeSum1960614.Machine.Light.Compiler.lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a) :
    a ∉ _root_.Light.Compiler.Constants (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) ∪ ({_root_.Light.Compiler.cFP} ∪ _root_.Light.Compiler.MainFrame (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P)) ∪
      _root_.ThreeSum1960614.Machine.Light.Compiler.Writable (_root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting P p0 dec hfit).toSizes _root_.Light.Compiler.mainFrame ∪ {_root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cD} := by
  have hframe := _root_.ThreeSum1960614.Machine.Light.Compiler.private_d2e33001c5_frame_le_stackCells P lim
  have htemps := _root_.ThreeSum1960614.Machine.Light.Compiler.two_mul_frameSize_add_le_dispPos P dec
  have hstack : 2 * _root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.lowCell P dec lim := le_max_left _ _
  have hpool : 25 + 4 * _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.lowCell P dec lim := le_max_right _ _
  simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout]
  rcases ha with ha | ha <;> ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end


end setting

/-! ## The theorem -/









end Light.Compiler

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler

open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
variable {W : ℕ}
section

/-- **The compiler is correct.**  Let the call of procedure p0 of the program P on the arguments i,
j and the memory μ end after c steps within the limits, and let the word size fit the limits.  Then
the compiled program, started on any memory whose cells `a ≥ 0` hold the words of μ and whose
cells -1 and -2 hold i and j, gives its verdict within `startCost + stepsPerStep · c` steps.  Then
the cell -3 holds the result of the procedure and the cells `a ≥ 0` hold the final memory.  The
cells -1 and -2, the cells below `-lowCell` and the cells from `lim.space` on are unchanged.  The
two constants of the time depend on the text of P and on dec only. -/
theorem ThreeSum1960614.Machine.Light.Compiler.compileProgram_correct__implementation_98c501a79a {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ}
    {i j : ℤ} {σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} {m : ℤ → BitVec W}
    (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P 0 (_root_.ThreeSum1960614.Machine.Light.mainStmt p0) ⟨_root_.Light.frame [0, i, j], μ⟩ σ' c)
    (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim)) (hm : _root_.ThreeSum1960614.Machine.Light.Compiler.Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W, _root_.EndStatement.exec (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.ramSteps P dec c) 0 m
        = some (_root_.Light.verdictOf dec (σ'.loc 0), m') ∧ _root_.ThreeSum1960614.Machine.Light.Compiler.Outcome lim P dec m σ' m' := by
  have hF := _root_.ThreeSum1960614.Machine.Light.Compiler.three_le_frameSize P
  have hdisp := _root_.ThreeSum1960614.Machine.Light.Compiler.two_mul_frameSize_add_le_dispPos P dec
  have hσ : _root_.ThreeSum1960614.Machine.Light.State.Bounded lim ⟨_root_.Light.frame [0, i, j], μ⟩ :=
    _root_.ThreeSum1960614.Machine.Light.bounded_frame (by simp [hm.arg1_le, hm.arg2_le, (abs_nonneg i).trans hm.arg1_le]) hm.bounded
  have hσ' := h.bounded hσ
  -- the start-up code
  have run₁ := _root_.ThreeSum1960614.Machine.Light.Compiler.steps_start P p0 dec (_root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting P p0 dec hfit).inRange_neg_one m
  have keep₁ := _root_.ThreeSum1960614.Machine.Light.Compiler.agreeOutside_startMem hF (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) m
  -- the outermost statement
  obtain ⟨m', n, fin⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.sim (_root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting P p0 dec hfit) h _root_.Light.Compiler.mainPos _root_.Light.Compiler.mainFrame _ (_root_.ThreeSum1960614.Machine.Light.Compiler.private_2d8e51b305_start_mainStmt hfit hσ
    (_root_.ThreeSum1960614.Machine.Light.Compiler.rel_startMem _ hF (by simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout, _root_.Light.Compiler.mainFrame]; omega)
      (fun a _ => hm.rep a) hm.arg1 hm.arg2))
  have hn : n ≤ _root_.Light.Compiler.stepsPerStep (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) * c := fin.le
  have run₂ := fin.run.cast_pos (p' := _root_.ThreeSum1960614.Machine.Light.Compiler.tailPos (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P))
    (by simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.tailPos, _root_.ThreeSum1960614.Machine.Light.Compiler.size_mainStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.private_960ac446a9_setting, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout])
  -- the verdict
  obtain ⟨k, cfg, hk, run₃, tail⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_715aae6e9a_steps_tail (_root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_tailCode P p0 dec)
    (fin.rel.loc 0 (show 0 < _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P by omega)) fin.rel.zero
    (hfit.inRange (by rw [abs_neg]; exact hσ'.1 0))
  have run := (run₁.trans run₂).trans run₃
  have keep := (keep₁.trans_union fin.agree).trans_union tail.agree
  have far (a : ℤ) ha : cfg.mem a = m a := keep.cell (_root_.ThreeSum1960614.Machine.Light.Compiler.private_6f9d786750_not_mem_of_far hfit ha)
  refine ⟨cfg.mem, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_mono (c := ⟨0, m⟩) (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_of_steps run tail.verdict) ?_,
    { holds := ⟨fun a => ?_, hσ'.2⟩
      result := tail.result ▸ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd (hfit.inRange (hσ'.1 0))
      arg1 := keep.cell (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
      arg2 := keep.cell (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
      far := far }⟩
  · simp only [_root_.ThreeSum1960614.Machine.Light.ramSteps, _root_.ThreeSum1960614.Machine.Light.Compiler.startCost]
    omega
  · by_cases ha : a < lim.space
    · exact tail.agree.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (fin.rel.mem a ha)
    · rw [far _ (Or.inr (by exact_mod_cast not_lt.1 ha)), h.mem_outside a (not_lt.1 ha)]
      exact hm.rep a
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Compiler.compileProgram_correct__implementation_98c501a79a) := (@ThreeSum1960614.Machine.Light.Compiler.compileProgram_correct__implementation_98c501a79a)

#print axioms solution
