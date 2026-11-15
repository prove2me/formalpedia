-- Prove2me | solution 1 for TimeSpaceMA.widthListComputable_to_coinFreeRAM
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T20:07:17.721759+00:00
-- url     : https://prove2.me/submissions/45d60067-c57f-4872-91ac-125055fca3da

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_TimeSpaceMA_RAM
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

namespace TimeSpaceMA.RAMBlock

abbrev Mem := ℕ → ℕ

inductive Op
  | const (d c : ℕ)
  | add (d a b : ℕ)
  | monus (d a b : ℕ)
  | load (d a : ℕ)
  | store (a b : ℕ)

def Op.instr : Op → Instr
  | .const d c => .const d c
  | .add d a b => .add d a b
  | .monus d a b => .monus d a b
  | .load d a => .load d a
  | .store a b => .store a b

def Op.effect : Op → Mem → Mem
  | .const d c, m => Function.update m d c
  | .add d a b, m => Function.update m d (m a + m b)
  | .monus d a b, m => Function.update m d (m a - m b)
  | .load d a, m => Function.update m d (m (m a))
  | .store a b, m => Function.update m (m a) (m b)

def Op.cost : Op → Mem → ℕ
  | .const d c, _ => 1 + d.size + c.size
  | .add d a b, m => 1 + d.size + a.size + b.size + (m a).size + (m b).size + (m a+m b).size
  | .monus d a b, m => 1 + d.size + a.size + b.size + (m a).size + (m b).size + (m a-m b).size
  | .load d a, m => 1 + d.size + a.size + (m a).size + (m (m a)).size
  | .store a b, m => 1 + a.size + b.size + (m a).size + (m b).size

def checkCost (a b : ℕ) (m : Mem) : ℕ :=
  1 + a.size + b.size + (m a).size + (m b).size

def gotoCost (m : Mem) : ℕ := checkCost 0 0 m

inductive Code
  | atom (op : Op)
  | seq (a b : Code)
  | skip
  | ifLE (a b : ℕ) (yes no : Code)
  | whileLE (a b : ℕ) (body : Code)

abbrev Code.const (d c : ℕ) : Code := .atom (.const d c)
abbrev Code.add (d a b : ℕ) : Code := .atom (.add d a b)
abbrev Code.monus (d a b : ℕ) : Code := .atom (.monus d a b)
abbrev Code.load (d a : ℕ) : Code := .atom (.load d a)
abbrev Code.store (a b : ℕ) : Code := .atom (.store a b)
def Code.chain : List Code → Code := List.foldr Code.seq .skip

/-- Logical costs count every data operation and conditional test. The fixed widths of compiled
jump addresses are added by the compiler correctness theorem. -/
inductive Executes : Code → Mem → Mem → ℕ → Prop
  | atom (op m) : Executes (.atom op) m (op.effect m) (op.cost m)
  | skip (m) : Executes .skip m m 0
  | seq {a b m v w t u} : Executes a m v t → Executes b v w u →
      Executes (.seq a b) m w (t+u)
  | yes {a b p q m v t} : m a ≤ m b → Executes p m v t →
      Executes (.ifLE a b p q) m v (checkCost a b m + t)
  | no {a b p q m v t} : ¬m a ≤ m b → Executes q m v t →
      Executes (.ifLE a b p q) m v (checkCost a b m + t + gotoCost v)
  | done {a b p m} : ¬m a ≤ m b →
      Executes (.whileLE a b p) m m (checkCost a b m + gotoCost m)
  | again {a b p m v w t u} : m a ≤ m b → Executes p m v t → Executes (.whileLE a b p) v w u →
      Executes (.whileLE a b p) m w (checkCost a b m + t + gotoCost v + u)

def Code.size : Code → ℕ
  | .atom _ => 1
  | .skip => 0
  | .seq p q => p.size + q.size
  | .ifLE _ _ p q => 2 + q.size + p.size
  | .whileLE _ _ p => 3 + p.size

def Code.compile : Code → ℕ → Program
  | .atom op, _ => [op.instr]
  | .skip, _ => []
  | .seq p q, a => p.compile a ++ q.compile (a+p.size)
  | .ifLE r s p q, a =>
      [.jle r s (a+2+q.size)] ++ q.compile (a+1) ++
        [.jle 0 0 (a+2+q.size+p.size)] ++ p.compile (a+2+q.size)
  | .whileLE r s p, a =>
      [.jle r s (a+2), .jle 0 0 (a+3+p.size)] ++
        p.compile (a+2) ++ [.jle 0 0 a]

@[simp] theorem Code.length_compile (p : Code) (a : ℕ) : (p.compile a).length = p.size := by
  induction p generalizing a <;> simp [Code.compile, Code.size, *, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] <;> omega

theorem Code.compile_coinFree (p : Code) (a : ℕ) : (p.compile a).CoinFree := by
  intro d
  induction p generalizing a with
  | atom op => cases op <;> simp [Code.compile, Op.instr]
  | skip => simp [Code.compile]
  | seq p q hp hq => simp [Code.compile, hp, hq]
  | ifLE x y p q hp hq => simp [Code.compile, hp, hq]
  | whileLE x y p hp => simp [Code.compile, hp]

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA.RAMBlock

open Function

/-- The compiled code occupies its assigned interval in the full program. -/
def CodeAt (P : Program) (a : ℕ) (code : Program) : Prop :=
  a+code.length ≤ P.length ∧ ∀ i : ℕ, i < code.length → P[a+i]? = code[i]?

private theorem CodeAt.left {P : Program} {a : ℕ} {x y : Program}
    (h : CodeAt P a (x++y)) : CodeAt P a x := by
  refine ⟨by have := h.1; simp only [List.length_append] at this; omega, ?_⟩
  intro i hi
  rw [h.2 i (by simp; omega), List.getElem?_append_left hi]

private theorem CodeAt.right {P : Program} {a : ℕ} {x y : Program}
    (h : CodeAt P a (x++y)) : CodeAt P (a+x.length) y := by
  refine ⟨by have := h.1; simp only [List.length_append] at this; omega, ?_⟩
  intro i hi
  rw [Nat.add_assoc, h.2 (x.length+i) (by simpa using hi),
    List.getElem?_append_right (Nat.le_add_right ..), Nat.add_sub_cancel_left]

private theorem CodeAt.head {P r : Program} {a : ℕ} {ins : Instr}
    (h : CodeAt P a (ins::r)) : P[a]? = some ins := by
  simpa using h.2 0 (by simp)

private theorem CodeAt.dropHead {P r : Program} {a : ℕ} {ins : Instr}
    (h : CodeAt P a (ins::r)) : CodeAt P (a+1) r :=
  CodeAt.right (x := [ins]) h

/-- A linked block runs between two program counters, preserving the zero-tape cursor. -/
def LinkedRun (P : Program) (a b : ℕ) (m v : Mem) (cost : ℕ) : Prop :=
  ∀ w : ℕ, ∃ t c : ℕ, t ≤ cost ∧
    ((P.step zeroTape)^[t] ⟨a,m,0,false,w⟩) = ⟨b,v,0,false,c⟩ ∧
    c ≤ w + cost*(P.length.size+1)

private theorem LinkedRun.id (P : Program) (a : ℕ) (m : Mem) : LinkedRun P a a m m 0 :=
  fun w => ⟨0,w, by simp⟩

theorem LinkedRun.trans {P : Program} {a b c : ℕ} {m v w : Mem} {t u : ℕ}
    (h : LinkedRun P a b m v t) (h' : LinkedRun P b c v w u) :
    LinkedRun P a c m w (t+u) := by
  intro start
  obtain ⟨i,ci,hi,he,hci⟩ := h start
  obtain ⟨j,cj,hj,he',hcj⟩ := h' ci
  refine ⟨j+i, cj, by omega, ?_, ?_⟩
  · rw [Function.iterate_add_apply, he, he']
  · rw [Nat.add_mul]
    omega

private theorem linked_atom {P : Program} {a : ℕ} {op : Op} (h : P[a]? = some op.instr)
    (m : Mem) : LinkedRun P a (a+1) m (op.effect m) (op.cost m) := by
  intro w
  refine ⟨1,w+op.cost m, ?_, ?_, ?_⟩
  · cases op <;> dsimp [Op.cost] <;> omega
  · cases op <;> simp [Function.iterate_one, Program.step, h, Op.instr, Op.effect, Op.cost] <;> omega
  · have H := Nat.mul_le_mul_left (op.cost m) (show 1 ≤ P.length.size+1 by omega)
    simp at H
    omega

private theorem linked_test {P : Program} {idx a b target : ℕ} (m : Mem)
    (hp : P[idx]? = some (.jle a b target)) (hb : target ≤ P.length) :
    LinkedRun P idx (if m a ≤ m b then target else idx+1) m m (checkCost a b m) := by
  intro w
  refine ⟨1, w+checkCost a b m+target.size, ?_, ?_, ?_⟩
  · unfold checkCost; omega
  · simp [Function.iterate_one, Program.step, hp, checkCost]
    omega
  · have H := Nat.mul_le_mul_right P.length.size (show 1 ≤ checkCost a b m by
      unfold checkCost; omega)
    have hs := Nat.size_le_size hb
    rw [Nat.mul_add, Nat.mul_one]
    simp at H
    omega

private theorem linked_jump {P : Program} {idx target : ℕ} (m : Mem)
    (hp : P[idx]? = some (.jle 0 0 target)) (hb : target ≤ P.length) :
    LinkedRun P idx target m m (gotoCost m) := by
  simpa [gotoCost] using linked_test m hp hb

private theorem inBounds {P : Program} {a : ℕ} {c : Program} (h : CodeAt P a c) :
    a ≤ P.length := by have := h.1; omega

/-- An abstract execution is simulated by the compiled interval. The actual log-cost is
bounded by the logical cost times one plus the fixed width of jump destinations. -/
theorem Executes.linked {code : Code} {m v : Mem} {t : ℕ} (h : Executes code m v t)
    (P : Program) (a : ℕ) (hAt : CodeAt P a (code.compile a)) :
    LinkedRun P a (a+code.size) m v t := by
  induction h generalizing a with
  | atom op m =>
    exact linked_atom (CodeAt.head hAt) m
  | skip m =>
    simpa [Code.size] using LinkedRun.id P a m
  | @seq p q m w v t u hp hq ip iq =>
    simp only [Code.compile] at hAt
    have hx := ip a hAt.left
    have hy := iq (a+p.size) (by simpa using hAt.right)
    simpa [Code.size, Nat.add_assoc] using hx.trans hy
  | @yes r s p q m v t hle hp ip =>
    simp only [Code.compile] at hAt
    have hlen := hAt.1
    simp only [List.length_append, List.length_singleton, Code.length_compile] at hlen
    have hb : a+2+q.size ≤ P.length := by omega
    have hj := linked_test m (CodeAt.head hAt) hb
    rw [if_pos hle] at hj
    have htail : CodeAt P (a+1) (q.compile (a+1) ++
        (.jle 0 0 (a+2+q.size+p.size) :: p.compile (a+2+q.size))) := by
      have h := hAt.dropHead
      change CodeAt P (a+1) ((q.compile (a+1) ++ [.jle 0 0 (a+2+q.size+p.size)]) ++
        p.compile (a+2+q.size)) at h
      simpa only [List.append_assoc, List.singleton_append] using h
    have hex := (CodeAt.right (x := q.compile (a+1)) htail).dropHead
    have hyes : CodeAt P (a+2+q.size) (p.compile (a+2+q.size)) := by
      have he : a+1+(q.compile (a+1)).length+1 = a+2+q.size := by simp; omega
      rw [he] at hex
      exact hex
    have hp' := ip (a+2+q.size) hyes
    simpa [Code.size, Nat.add_assoc] using hj.trans hp'
  | @no r s p q m v t hle hq iq =>
    simp only [Code.compile] at hAt
    have hlen := hAt.1
    simp only [List.length_append, List.length_singleton, Code.length_compile] at hlen
    have hb : a+2+q.size ≤ P.length := by omega
    have hb' : a+2+q.size+p.size ≤ P.length := by omega
    have hj := linked_test m (CodeAt.head hAt) hb
    rw [if_neg hle] at hj
    have htail : CodeAt P (a+1) (q.compile (a+1) ++
        (.jle 0 0 (a+2+q.size+p.size) :: p.compile (a+2+q.size))) := by
      have h := hAt.dropHead
      change CodeAt P (a+1) ((q.compile (a+1) ++ [.jle 0 0 (a+2+q.size+p.size)]) ++
        p.compile (a+2+q.size)) at h
      simpa only [List.append_assoc, List.singleton_append] using h
    have hn := iq (a+1) (CodeAt.left htail)
    have hskip := linked_jump v (CodeAt.head (CodeAt.right htail)) hb'
    simp only [Code.length_compile] at hskip
    simpa [Code.size, Nat.add_assoc] using (hj.trans hn).trans hskip
  | @done r s body m hle =>
    simp only [Code.compile] at hAt
    have hlen := hAt.1
    simp only [List.length_append, List.length_cons, List.length_nil, Code.length_compile] at hlen
    have hb : a+2 ≤ P.length := by omega
    have hb' : a+3+body.size ≤ P.length := by omega
    have htest := linked_test m (CodeAt.head hAt) hb
    rw [if_neg hle] at htest
    have hskip := linked_jump m (CodeAt.head hAt.dropHead) hb'
    simpa [Code.size, Nat.add_assoc] using htest.trans hskip
  | @again r s body m w v t u hle hp hloop ip iloop =>
    have hloop' := iloop a hAt
    simp only [Code.compile] at hAt
    have hlen := hAt.1
    simp only [List.length_append, List.length_cons, List.length_nil, Code.length_compile] at hlen
    have hb : a+2 ≤ P.length := by omega
    have htest := linked_test m (CodeAt.head hAt) hb
    rw [if_pos hle] at htest
    have htail := hAt.dropHead.dropHead
    have hbody := ip (a+2) (CodeAt.left htail)
    have ha : a ≤ P.length := inBounds hAt
    have hback := linked_jump w (CodeAt.head (CodeAt.right htail)) ha
    have hback' : LinkedRun P (a+2+body.size) a w w (gotoCost w) := by
      simpa [Nat.add_assoc] using hback
    exact ((htest.trans hbody).trans hback').trans hloop'

/-- Compile a terminating block, then execute the final native halt instruction. -/
theorem Executes.programRuns {code : Code} {m v : Mem} {t : ℕ}
    (h : Executes code m v t) :
    let P := code.compile 0 ++ [.halt]
    ∃ st, P.RunsTo zeroTape m st ∧ st.mem = v ∧ st.work ≤ t*(P.length.size+1)+1 := by
  dsimp only
  let P := code.compile 0 ++ [.halt]
  have hAt : CodeAt P 0 (code.compile 0) := by
    refine ⟨by simp [P], ?_⟩
    intro i hi
    simpa [P] using List.getElem?_append_left (l₂ := [.halt]) hi
  obtain ⟨steps,cost,_,hr,hc⟩ := h.linked P 0 hAt 0
  have hlast : P[code.size]? = some .halt := by
    simp [P, List.getElem?_append_right]
  let st : State := ⟨code.size,v,0,true,cost+1⟩
  refine ⟨st, ⟨1+steps, ?_, rfl⟩, rfl, ?_⟩
  · rw [Function.iterate_add_apply]
    change (P.step zeroTape) (((P.step zeroTape)^[steps]) ⟨0,m,0,false,0⟩) = _
    rw [hr]
    simp [st, Program.step, hlast]
  · have hp : P.length = code.size + 1 := by simp [P]
    rw [hp, Nat.zero_add] at hc
    rw [show st.work = cost+1 from rfl, show (code.compile 0 ++ [Instr.halt]).length = code.size+1 from hp]
    exact Nat.add_le_add_right hc 1

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA.RAMBlock

/-- Structured RAM execution counted in primitive instructions, independent of bit lengths. -/
inductive Runs : Code → Mem → Mem → ℕ → Prop
  | atom (op m) : Runs (.atom op) m (op.effect m) 1
  | skip (m) : Runs .skip m m 0
  | seq {a b m v w t u} : Runs a m v t → Runs b v w u → Runs (.seq a b) m w (t+u)
  | yes {a b p q m v t} : m a ≤ m b → Runs p m v t → Runs (.ifLE a b p q) m v (1+t)
  | no {a b p q m v t} : ¬m a ≤ m b → Runs q m v t → Runs (.ifLE a b p q) m v (2+t)
  | done {a b p m} : ¬m a ≤ m b → Runs (.whileLE a b p) m m 2
  | again {a b p m v w t u} : m a ≤ m b → Runs p m v t → Runs (.whileLE a b p) v w u →
      Runs (.whileLE a b p) m w (2+t+u)

/-- Logical execution of a fixed straight-line sequence of primitive RAM instructions. -/
def execAtoms (m : Mem) (ops : List Op) : Mem := ops.foldl (fun st op => op.effect st) m

theorem runs_atoms (m : Mem) (ops : List Op) :
    Runs (Code.chain (ops.map Code.atom)) m (execAtoms m ops) ops.length := by
  induction ops generalizing m with
  | nil => exact .skip _
  | cons op ops ih =>
    change Runs (.seq (.atom op) (Code.chain (ops.map Code.atom))) m (execAtoms (op.effect m) ops)
      (ops.length+1)
    rw [Nat.add_comm]
    exact .seq (.atom _ _) (ih _)

/-- All live RAM values fit in the indicated number of bits. -/
def Mem.WidthLE (m : Mem) (B : ℕ) : Prop := ∀ r, (m r).size ≤ B

private theorem resize_add {x y B : ℕ} (hx : x.size ≤ B) (hy : y.size ≤ B) : (x+y).size ≤ B+1 := by
  have h₁ := Nat.size_le.mp hx
  have h₂ := Nat.size_le.mp hy
  apply Nat.size_le.mpr
  rw [Nat.pow_succ]
  omega

/-- Maximum bit width of a fixed register index or literal appearing in this instruction. -/
def Op.width : Op → ℕ
  | .const d c => max d.size c.size
  | .add d a b | .monus d a b => max d.size (max a.size b.size)
  | .load d a => max d.size a.size
  | .store a b => max a.size b.size

/-- Maximum width of a fixed field in the macro program. -/
def Code.width : Code → ℕ
  | .skip => 0
  | .atom o => o.width
  | .seq p q => max p.width q.width
  | .ifLE a b p q => max (max a.size b.size) (max p.width q.width)
  | .whileLE a b p => max (max a.size b.size) p.width

private theorem Op.effect_width (o : Op) {m : Mem} {B : ℕ} (ho : o.width ≤ B)
    (hm : m.WidthLE B) : (o.effect m).WidthLE (B+1) := by
  intro r
  have hold := Nat.le_trans (hm r) (Nat.le_succ B)
  cases o with
  | const d c =>
    have hc : c.size ≤ B := Nat.le_trans (Nat.le_max_right _ _) ho
    simp only [Op.effect, Function.update_apply]
    split
    · omega
    · exact hold
  | add d a b =>
    simp only [Op.effect, Function.update_apply]
    split
    · exact resize_add (hm _) (hm _)
    · exact hold
  | monus d a b =>
    simp only [Op.effect, Function.update_apply]
    split
    · exact Nat.le_trans (Nat.size_le_size (Nat.sub_le _ _)) (Nat.le_trans (hm _) (Nat.le_succ _))
    · exact hold
  | load d a =>
    simp only [Op.effect, Function.update_apply]
    split
    · exact Nat.le_trans (hm _) (Nat.le_succ _)
    · exact hold
  | store a b =>
    simp only [Op.effect, Function.update_apply]
    split
    · exact Nat.le_trans (hm _) (Nat.le_succ _)
    · exact hold

private theorem Op.cost_le (op : Op) {m : Mem} {B : ℕ}
    (ho : op.width ≤ B) (hm : m.WidthLE B) : op.cost m ≤ 8*(B+1) := by
  cases op with
  | const d c =>
    simp only [Op.width, Nat.max_le] at ho
    simp only [Op.cost]
    omega
  | add d a b =>
    simp only [Op.width, Nat.max_le] at ho
    have h₁ := hm a
    have h₂ := hm b
    have h₃ := resize_add h₁ h₂
    simp only [Op.cost]
    omega
  | monus d a b =>
    simp only [Op.width, Nat.max_le] at ho
    have h₁ := hm a
    have h₂ := hm b
    have h₃ := Nat.le_trans (Nat.size_le_size (Nat.sub_le (m a) (m b))) h₁
    simp only [Op.cost]
    omega
  | load d a =>
    simp only [Op.width, Nat.max_le] at ho
    have h₁ := hm a
    have h₂ := hm (m a)
    simp only [Op.cost]
    omega
  | store a b =>
    simp only [Op.width, Nat.max_le] at ho
    have h₁ := hm a
    have h₂ := hm b
    simp only [Op.cost]
    omega

private theorem checkCost_le (a b : ℕ) {m : Mem} {B : ℕ} (ha : a.size ≤ B) (hb : b.size ≤ B)
    (hm : m.WidthLE B) : checkCost a b m ≤ 8*(B+1) := by
  have h₁ := hm a
  have h₂ := hm b
  simp only [checkCost]
  omega

private theorem gotoCost_le {m : Mem} {B : ℕ} (hm : m.WidthLE B) : gotoCost m ≤ 8*(B+1) :=
  checkCost_le 0 0 (by simp) (by simp) hm

private theorem charge_mono {B A u t : ℕ} (h : A+u ≤ B+t) :
    u*(8*(A+u+1)) ≤ u*(8*(B+t+1)) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))

/-- A unit trace can be charged exactly according to the log-cost convention. The
resulting charge is at most `8*T*(B+T+1)`, and final data width is at most `B+T`. -/
theorem Runs.toExecutes {p : Code} {m v : Mem} {t : ℕ} (h : Runs p m v t)
    (B : ℕ) (hp : p.width ≤ B) (hm : m.WidthLE B) :
    v.WidthLE (B+t) ∧ ∃ w, Executes p m v w ∧ w ≤ t*(8*(B+t+1)) := by
  induction h generalizing B with
  | atom op m =>
    exact ⟨Op.effect_width op hp hm, op.cost m, .atom _ _,
      Nat.le_trans (Op.cost_le op hp hm) (by simp <;> omega)⟩
  | skip m => exact ⟨by simpa using hm, 0, .skip _, by simp⟩
  | @seq p q m v w t u h₁ h₂ ih₁ ih₂ =>
    simp only [Code.width, Nat.max_le] at hp
    obtain ⟨hv, a, ha, hca⟩ := ih₁ B hp.1 hm
    obtain ⟨hw, b, hb, hcb⟩ := ih₂ (B+t) (Nat.le_trans hp.2 (Nat.le_add_right _ _)) hv
    refine ⟨by simpa only [Nat.add_assoc] using hw, a+b, .seq ha hb, ?_⟩
    have hca' := Nat.le_trans hca (charge_mono (B := B) (t := t+u) (by omega))
    rw [Nat.add_mul]
    have hcb' : b ≤ u*(8*(B+(t+u)+1)) := by
      simpa only [show B+t+u+1 = B+(t+u)+1 by omega] using hcb
    omega
  | @yes x y p q m v t hle h ih =>
    simp only [Code.width, Nat.max_le] at hp
    obtain ⟨hv, a, ha, hca⟩ := ih B hp.2.1 hm
    have hc := checkCost_le x y hp.1.1 hp.1.2 hm
    let M := 8*(B+(1+t)+1)
    have hca' : a ≤ t*M := Nat.le_trans hca (charge_mono (by omega))
    have hc' : checkCost x y m ≤ M := by dsimp [M]; omega
    refine ⟨fun r => Nat.le_trans (hv r) (by omega), _, .yes hle ha, ?_⟩
    change checkCost x y m + a ≤ (1+t)*M
    rw [Nat.add_mul, Nat.one_mul]
    omega
  | @no x y p q m v t hn h ih =>
    simp only [Code.width, Nat.max_le] at hp
    obtain ⟨hv, a, ha, hca⟩ := ih B hp.2.2 hm
    have hc := checkCost_le x y hp.1.1 hp.1.2 hm
    have hg := gotoCost_le hv
    let M := 8*(B+(2+t)+1)
    have hca' : a ≤ t*M := Nat.le_trans hca (charge_mono (by omega))
    have hc' : checkCost x y m ≤ M := by dsimp [M]; omega
    have hg' : gotoCost v ≤ M := by dsimp [M]; omega
    refine ⟨fun r => Nat.le_trans (hv r) (by omega), _, .no hn ha, ?_⟩
    change checkCost x y m + a + gotoCost v ≤ (2+t)*M
    rw [Nat.add_mul, Nat.two_mul]
    omega
  | @done x y p m h =>
    simp only [Code.width, Nat.max_le] at hp
    have hc := checkCost_le x y hp.1.1 hp.1.2 hm
    have hg := gotoCost_le hm
    refine ⟨fun r => Nat.le_trans (hm r) (by omega), _, .done h, ?_⟩
    omega
  | @again x y p m v w t u hle hbody hwhile ih₁ ih₂ =>
    have hp' : p.width ≤ B := Nat.le_trans (Nat.le_max_right _ _) hp
    obtain ⟨hv, a, ha, hca⟩ := ih₁ B hp' hm
    obtain ⟨hw, b, hb, hcb⟩ := ih₂ (B+t) (Nat.le_trans hp (Nat.le_add_right _ _)) hv
    have hxy : max x.size y.size ≤ B := Nat.le_trans (Nat.le_max_left _ _) hp
    have hc := checkCost_le x y (Nat.le_trans (Nat.le_max_left _ _) hxy)
      (Nat.le_trans (Nat.le_max_right _ _) hxy) hm
    have hg := gotoCost_le hv
    let M := 8*(B+(2+t+u)+1)
    have hca' : a ≤ t*M := Nat.le_trans hca (charge_mono (by omega))
    have hcb' : b ≤ u*M := Nat.le_trans hcb (charge_mono (by omega))
    have hc' : checkCost x y m ≤ M := by dsimp [M]; omega
    have hg' : gotoCost v ≤ M := by dsimp [M]; omega
    refine ⟨fun r => Nat.le_trans (hw r) (by omega), _, .again hle ha hb, ?_⟩
    change checkCost x y m + a + gotoCost v + b ≤ (2+t+u)*M
    rw [Nat.add_mul, Nat.add_mul, Nat.two_mul]
    omega

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA

/-- The first two memory lanes store input and output; every work tape gets its own lane. -/
def ramDataBase (k : ℕ) : ℕ := 32 + 3*k

def ramDataAddress (k lane j : ℕ) : ℕ := ramDataBase k + j*(k+2) + lane

def workSide {k : ℕ} (i : Fin k) : ℕ := 32 + 3*i.val

def workMag {k : ℕ} (i : Fin k) : ℕ := workSide i + 1

def workSymbol {k : ℕ} (i : Fin k) : ℕ := workSide i + 2

/-- Encode blank, zero, and one as natural data; initially zero memory is blank. -/
def ramSymbol : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- Number in the input lane: a blank at 0, data at positions `1..length`, then blanks. -/
def ramInputSymbol (input : List Bool) (j : ℕ) : ℕ :=
  if j = 0 then 0 else ramSymbol input[j-1]?

/-- The two registers of a signed work head store its sign and its magnitude offset. -/
def ramHead (side mag : ℕ) : ℤ :=
  if side = 0 then Int.ofNat mag else Int.negSucc mag

/-- Natural data index for a signed work tape position. -/
def ramTapeIndex : ℤ → ℕ
  | .ofNat m => 2*m
  | .negSucc m => 2*m+1

@[simp] theorem ramTapeIndex_head (s m : ℕ) (hs : s ≤ 1) : ramTapeIndex (ramHead s m) = 2*m+s := by
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> rfl

@[simp] theorem workSide_lt_base {k : ℕ} (i : Fin k) : workSide i < ramDataBase k := by
  have := i.isLt
  simp [workSide, ramDataBase]

@[simp] theorem workMag_lt_base {k : ℕ} (i : Fin k) : workMag i < ramDataBase k := by
  have := i.isLt
  simp [workMag, workSide, ramDataBase]; omega

@[simp] theorem workSymbol_lt_base {k : ℕ} (i : Fin k) : workSymbol i < ramDataBase k := by
  have := i.isLt
  simp [workSymbol, workSide, ramDataBase]; omega

@[simp] theorem ramDataAddress_ge (k l j : ℕ) : ramDataBase k ≤ ramDataAddress k l j := by
  unfold ramDataAddress; omega

theorem ramDataAddress_eq_iff {k l l' j j' : ℕ} (hl : l < k+2) (hl' : l' < k+2) :
    ramDataAddress k l j = ramDataAddress k l' j' ↔ l=l' ∧ j=j' := by
  constructor
  · intro he
    have hh : j*(k+2)+l = j'*(k+2)+l' := by unfold ramDataAddress at he; omega
    have hm := congrArg (· % (k+2)) hh
    have hd := congrArg (· / (k+2)) hh
    rw [Nat.mul_comm j, Nat.mul_comm j'] at hm hd
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at hm
    rw [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hl,
      Nat.div_eq_of_lt hl', Nat.add_zero, Nat.add_zero] at hd
    exact ⟨hm,hd⟩
  · rintro ⟨rfl,rfl⟩; rfl

/-- A code for a source control state, reserving zero to represent source halting. -/
def ramStateCode {Q : Type} {q : ℕ} (ids : Q ≃ Fin q) : Option Q → ℕ
  | none => 0
  | some a => 1+(ids a).val

theorem ramStateCode_bound {Q : Type} {q : ℕ} (ids : Q ≃ Fin q) (s : Option Q) : ramStateCode ids s ≤ q := by
  cases s with
  | none => exact Nat.zero_le _
  | some s => have := (ids s).isLt; simp only [ramStateCode]; omega

/-- Layout invariants maintained at source-step boundaries. Input lane is read-only;
output lane has the chronological bits as a zero-based prefix. -/
structure RAMMiddleRep {k q : ℕ} {Q : Type} (ids : Q ≃ Fin q)
    {input : List Bool} (cfg : Turing.Cfg k Bool Q input) (mem : ℕ → ℕ) : Prop where
  lengthInput : mem 3 = input.length
  headInput : mem 4 = cfg.inputPos.val
  lengthOutput : mem 5 = cfg.output.length
  control : mem 6 = ramStateCode ids cfg.state
  zeroReg : mem 7 = 0
  oneReg : mem 8 = 1
  inputLane : ∀ j, mem (ramDataAddress k 0 j) = ramInputSymbol input j
  outputLane : ∀ j, mem (ramDataAddress k 1 j) = ramSymbol cfg.output[j]?
  headSign : ∀ i : Fin k, mem (workSide i) ≤ 1
  headWork : ∀ i : Fin k, ramHead (mem (workSide i)) (mem (workMag i)) = cfg.workTapePos i
  workLane : ∀ (i : Fin k) (j : ℤ),
    mem (ramDataAddress k (i.val+2) (ramTapeIndex j)) = ramSymbol (cfg.workTapes i j)

theorem ramInputSymbol_head {k : ℕ} {Q : Type} {input : List Bool} (cfg : Turing.Cfg k Bool Q input) :
    ramInputSymbol input cfg.inputPos.val = ramSymbol cfg.inputSymbol := by
  by_cases h0 : cfg.inputPos.val = 0
  · rw [h0, Turing.inputSymbol_eq_none_of_boundary (Or.inl h0)]
    rfl
  by_cases hend : cfg.inputPos.val = input.length + 1
  · rw [hend, Turing.inputSymbol_eq_none_of_boundary (Or.inr hend)]
    simp [ramInputSymbol]
  let j := cfg.inputPos.val - 1
  have hj : cfg.inputPos.val = 1+j := by dsimp [j]; omega
  have hlt : j < input.length := by have := cfg.inputPos.isLt; dsimp [j]; omega
  rw [Turing.inputSymbolInner j hj hlt]
  simp [ramInputSymbol, hj, List.getElem?_eq_getElem hlt]

/-- Inputs and references for a native transition, collected in finite RAM registers. -/
structure RAMReadRep {k : ℕ} {Q : Type} {input : List Bool}
    (cfg : Turing.Cfg k Bool Q input) (mem : ℕ → ℕ) : Prop where
  inputRead : mem 10 = ramSymbol cfg.inputSymbol
  workRead : ∀ i : Fin k, mem (workSymbol i) = ramSymbol (cfg.workTapeSymbols i)

@[simp] theorem ramTapeIndex_injective : Function.Injective ramTapeIndex := by
  intro x y h
  cases x <;> cases y <;> simp only [ramTapeIndex] at h
  · congr 1; omega
  · omega
  · omega
  · congr 1; omega

theorem ramSymbol_injective : Function.Injective ramSymbol := by
  intro a b h
  cases a with
  | none => cases b with | none => rfl | some b => cases b <;> simp [ramSymbol] at h
  | some a =>
    cases a <;> cases b with
    | none => simp [ramSymbol] at h
    | some b => cases b <;> simp [ramSymbol] at h ⊢

theorem workSide_injective {k : ℕ} : Function.Injective (@workSide k) := by
  intro i j h
  apply Fin.ext
  dsimp [workSide] at h
  omega

theorem workMag_injective {k : ℕ} : Function.Injective (@workMag k) := by
  intro i j h
  exact workSide_injective (by dsimp [workMag] at h; omega)

theorem workSymbol_injective {k : ℕ} : Function.Injective (@workSymbol k) := by
  intro i j h
  exact workSide_injective (by dsimp [workSymbol] at h; omega)

@[simp] theorem workSide_ne_mag {k : ℕ} (i j : Fin k) : workSide i ≠ workMag j := by
  dsimp [workMag, workSide]; omega

@[simp] theorem workSide_ne_symbol {k : ℕ} (i j : Fin k) : workSide i ≠ workSymbol j := by
  dsimp [workSymbol, workSide]; omega

@[simp] theorem workMag_ne_symbol {k : ℕ} (i j : Fin k) : workMag i ≠ workSymbol j := by
  dsimp [workSymbol, workMag, workSide]; omega

/-- The RAM memory obtained by changing one native work tape at its current head. -/
def ramWriteWork {k : ℕ} (mem : ℕ → ℕ) (i : Fin k) (s : Option Bool) : ℕ → ℕ :=
  Function.update mem
    (ramDataAddress k (i.val+2) (2*mem (workMag i)+mem (workSide i))) (ramSymbol s)

/-- The exact addressed store is the chosen native cell update. -/
theorem RAMMiddleRep.writeWork {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {mem : ℕ → ℕ}
    (h : RAMMiddleRep ids cfg mem) (i : Fin k) (s : Option Bool) :
    RAMMiddleRep ids
      { cfg with workTapes :=
        Function.update cfg.workTapes i (Function.update (cfg.workTapes i) (cfg.workTapePos i) s) }
      (ramWriteWork mem i s) := by
  have hz : 2*mem (workMag i)+mem (workSide i) = ramTapeIndex (cfg.workTapePos i) := by
    rw [← h.headWork i, ramTapeIndex_head _ _ (h.headSign i)]
  let addr := ramDataAddress k (i.val+2) (ramTapeIndex (cfg.workTapePos i))
  have haddr : ramDataBase k ≤ addr := ramDataAddress_ge _ _ _
  have hreg (r : ℕ) (hr : r < ramDataBase k) : r ≠ addr := by omega
  have hi2 : i.val+2 < k+2 := by omega
  unfold ramWriteWork
  rw [hz]
  change RAMMiddleRep ids _ (Function.update mem addr _)
  constructor
  · simpa only [Function.update_of_ne (hreg 3 (by unfold ramDataBase; omega))] using h.lengthInput
  · simpa only [Function.update_of_ne (hreg 4 (by unfold ramDataBase; omega))] using h.headInput
  · simpa only [Function.update_of_ne (hreg 5 (by unfold ramDataBase; omega))] using h.lengthOutput
  · simpa only [Function.update_of_ne (hreg 6 (by unfold ramDataBase; omega))] using h.control
  · simpa only [Function.update_of_ne (hreg 7 (by unfold ramDataBase; omega))] using h.zeroReg
  · simpa only [Function.update_of_ne (hreg 8 (by unfold ramDataBase; omega))] using h.oneReg
  · intro j
    have hne : ramDataAddress k 0 j ≠ addr := fun he => by
      have := (ramDataAddress_eq_iff (by omega : 0 < k+2) hi2).mp he
      omega
    simpa only [Function.update_of_ne hne] using h.inputLane j
  · intro j
    have hne : ramDataAddress k 1 j ≠ addr := fun he => by
      have := (ramDataAddress_eq_iff (by omega : 1 < k+2) hi2).mp he
      omega
    simpa only [Function.update_of_ne hne] using h.outputLane j
  · intro j
    simpa only [Function.update_of_ne (hreg _ (workSide_lt_base j))] using h.headSign j
  · intro j
    simpa only [Function.update_of_ne (hreg _ (workSide_lt_base j)),
      Function.update_of_ne (hreg _ (workMag_lt_base j))] using h.headWork j
  · intro j p
    have hj2 : j.val+2 < k+2 := by omega
    by_cases hji : j = i
    · subst j
      by_cases hp : p = cfg.workTapePos i
      · subst p; simp [addr]
      · have hne : ramDataAddress k (i.val+2) (ramTapeIndex p) ≠ addr := fun he =>
          hp (ramTapeIndex_injective ((ramDataAddress_eq_iff hi2 hi2).mp he).2)
        simpa only [Function.update_self, Function.update_of_ne hp, Function.update_of_ne hne] using h.workLane i p
    · have hne : ramDataAddress k (j.val+2) (ramTapeIndex p) ≠ addr := fun he =>
        hji (Fin.ext (Nat.add_right_cancel ((ramDataAddress_eq_iff hj2 hi2).mp he).1))
      simpa only [Function.update_of_ne hji, Function.update_of_ne hne] using h.workLane j p

/-- Store a single bit at the end of the output buffer, then increment the output cursor. -/
def ramAppendOutput (k : ℕ) (mem : ℕ → ℕ) (b : Bool) : ℕ → ℕ :=
  Function.update (Function.update mem (ramDataAddress k 1 (mem 5)) (ramSymbol (some b)))
    5 (mem 5+1)

/-- The output buffer appends exactly one bit. -/
theorem RAMMiddleRep.appendOutput {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {mem : ℕ → ℕ}
    (h : RAMMiddleRep ids cfg mem) (b : Bool) :
    RAMMiddleRep ids { cfg with output := cfg.output ++ [b] } (ramAppendOutput k mem b) := by
  let addr := ramDataAddress k 1 (mem 5)
  have hbase : ramDataBase k ≤ addr := ramDataAddress_ge _ _ _
  have hbaseMin : 32 ≤ ramDataBase k := by unfold ramDataBase; omega
  have hreg (r : ℕ) (hr : r < ramDataBase k) : r ≠ addr := by omega
  have hdata (l j : ℕ) : ramDataAddress k l j ≠ 5 := by
    have := ramDataAddress_ge k l j
    omega
  have h1 : 1 < k+2 := by omega
  unfold ramAppendOutput
  change RAMMiddleRep ids _ (Function.update (Function.update mem addr _) 5 _)
  constructor
  · simpa only [Function.update_of_ne (by decide : 3 ≠ 5), Function.update_of_ne (hreg 3 (by omega))] using h.lengthInput
  · simpa only [Function.update_of_ne (by decide : 4 ≠ 5), Function.update_of_ne (hreg 4 (by omega))] using h.headInput
  · simp [h.lengthOutput]
  · simpa only [Function.update_of_ne (by decide : 6 ≠ 5), Function.update_of_ne (hreg 6 (by omega))] using h.control
  · simpa only [Function.update_of_ne (by decide : 7 ≠ 5), Function.update_of_ne (hreg 7 (by omega))] using h.zeroReg
  · simpa only [Function.update_of_ne (by decide : 8 ≠ 5), Function.update_of_ne (hreg 8 (by omega))] using h.oneReg
  · intro j
    have hne : ramDataAddress k 0 j ≠ addr := fun he => by
      have := (ramDataAddress_eq_iff (by omega : 0 < k+2) h1).mp he
      omega
    simpa only [Function.update_of_ne (hdata 0 j), Function.update_of_ne hne] using h.inputLane j
  · intro j
    rw [Function.update_of_ne (hdata 1 j), List.getElem?_append]
    by_cases hj : j = mem 5
    · subst j
      simp [addr, h.lengthOutput]
    · have hne : ramDataAddress k 1 j ≠ addr := fun he => hj ((ramDataAddress_eq_iff h1 h1).mp he).2
      rw [Function.update_of_ne hne, h.outputLane]
      by_cases hb : j < cfg.output.length
      · simp [hb]
      · have hj2 : cfg.output.length < j := by rw [h.lengthOutput] at hj; omega
        simp [hb, List.getElem?_eq_none (show [b].length ≤ j-cfg.output.length by simp; omega)]
  · intro j
    have hj : workSide j ≠ 5 := by unfold workSide; omega
    simpa only [Function.update_of_ne hj, Function.update_of_ne (hreg _ (workSide_lt_base j))] using h.headSign j
  · intro j
    have hjs : workSide j ≠ 5 := by unfold workSide; omega
    have hjm : workMag j ≠ 5 := by unfold workMag workSide; omega
    simpa only [Function.update_of_ne hjs, Function.update_of_ne hjm,
      Function.update_of_ne (hreg _ (workSide_lt_base j)),
      Function.update_of_ne (hreg _ (workMag_lt_base j))] using h.headWork j
  · intro j p
    have hj2 : j.val+2 < k+2 := by omega
    have hne : ramDataAddress k (j.val+2) (ramTapeIndex p) ≠ addr := fun he => by
      have := (ramDataAddress_eq_iff hj2 h1).mp he
      omega
    simpa only [Function.update_of_ne (hdata _ _), Function.update_of_ne hne] using h.workLane j p

/-- Signed head registers after the action on a work tape. -/
def ramMoveWork (side mag : ℕ) (d : SignType) : ℕ × ℕ :=
  match d with
  | .zero => (side,mag)
  | .neg => if side = 0 then if mag = 0 then (1,0) else (0,mag-1) else (1,mag+1)
  | .pos => if side = 0 then (0,mag+1) else if mag = 0 then (0,0) else (1,mag-1)

theorem ramMoveWork_correct (side mag : ℕ) (d : SignType) (hs : side ≤ 1) :
    (ramMoveWork side mag d).1 ≤ 1 ∧
    ramHead (ramMoveWork side mag d).1 (ramMoveWork side mag d).2 =
      ramHead side mag + (d.cast : ℤ) := by
  rcases (show side = 0 ∨ side = 1 by omega) with rfl | rfl <;>
    cases mag <;> cases d <;> simp [ramMoveWork,ramHead] <;> omega

/-- Change the head coordinates on one work tape. -/
def ramChangeWorkHead {k : ℕ} (mem : ℕ → ℕ) (i : Fin k) (d : SignType) : ℕ → ℕ :=
  let p := ramMoveWork (mem (workSide i)) (mem (workMag i)) d
  Function.update (Function.update mem (workSide i) p.1) (workMag i) p.2

private theorem small_ne_workSide {k r : ℕ} (hr : r < 32) (i : Fin k) : r ≠ workSide i := by
  unfold workSide; omega

private theorem small_ne_workMag {k r : ℕ} (hr : r < 32) (i : Fin k) : r ≠ workMag i := by
  unfold workMag workSide; omega

private theorem small_ne_address {k r : ℕ} (hr : r < 32) (lane j : ℕ) :
    ramDataAddress k lane j ≠ r := by
  have h := ramDataAddress_ge k lane j
  unfold ramDataBase at h
  omega

/-- Work-head motion changes its native position and leaves all stored tape symbols intact. -/
theorem RAMMiddleRep.moveWork {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {mem : ℕ → ℕ}
    (h : RAMMiddleRep ids cfg mem) (i : Fin k) (d : SignType) :
    RAMMiddleRep ids
      { cfg with workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i + (d.cast : ℤ)) }
      (ramChangeWorkHead mem i d) := by
  let p := ramMoveWork (mem (workSide i)) (mem (workMag i)) d
  have hp := ramMoveWork_correct (mem (workSide i)) (mem (workMag i)) d (h.headSign i)
  have ha (l j : ℕ) : ramDataAddress k l j ≠ workSide i ∧ ramDataAddress k l j ≠ workMag i := by
    have := ramDataAddress_ge k l j
    have := workSide_lt_base i
    have := workMag_lt_base i
    omega
  unfold ramChangeWorkHead
  change RAMMiddleRep ids _ (Function.update (Function.update mem (workSide i) p.1) (workMag i) p.2)
  constructor
  · simpa only [Function.update_of_ne (small_ne_workSide (by decide : 3 < 32) i),
      Function.update_of_ne (small_ne_workMag (by decide : 3 < 32) i)] using h.lengthInput
  · simpa only [Function.update_of_ne (small_ne_workSide (by decide : 4 < 32) i),
      Function.update_of_ne (small_ne_workMag (by decide : 4 < 32) i)] using h.headInput
  · simpa only [Function.update_of_ne (small_ne_workSide (by decide : 5 < 32) i),
      Function.update_of_ne (small_ne_workMag (by decide : 5 < 32) i)] using h.lengthOutput
  · simpa only [Function.update_of_ne (small_ne_workSide (by decide : 6 < 32) i),
      Function.update_of_ne (small_ne_workMag (by decide : 6 < 32) i)] using h.control
  · simpa only [Function.update_of_ne (small_ne_workSide (by decide : 7 < 32) i),
      Function.update_of_ne (small_ne_workMag (by decide : 7 < 32) i)] using h.zeroReg
  · simpa only [Function.update_of_ne (small_ne_workSide (by decide : 8 < 32) i),
      Function.update_of_ne (small_ne_workMag (by decide : 8 < 32) i)] using h.oneReg
  · intro j
    simpa only [Function.update_of_ne (ha 0 j).1, Function.update_of_ne (ha 0 j).2] using h.inputLane j
  · intro j
    simpa only [Function.update_of_ne (ha 1 j).1, Function.update_of_ne (ha 1 j).2] using h.outputLane j
  · intro j
    by_cases hji : j = i
    · subst j; simp [p, hp.1]
    · have hne := fun he => hji (workSide_injective he)
      simpa only [Function.update_of_ne (workSide_ne_mag j i), Function.update_of_ne hne] using h.headSign j
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self, Function.update_of_ne (workSide_ne_mag i i), ← h.headWork i] using hp.2
    · have hs := fun he => hji (workSide_injective he)
      have hm := fun he => hji (workMag_injective he)
      simpa only [Function.update_of_ne hji, Function.update_of_ne hs, Function.update_of_ne hm,
        Function.update_of_ne (workSide_ne_mag j i),
        Function.update_of_ne (Ne.symm (workSide_ne_mag i j))] using h.headWork j
  · intro j x
    simpa only [Function.update_of_ne (ha _ _).1, Function.update_of_ne (ha _ _).2] using h.workLane j x

/-- Changing the registered input head simply changes the represented source head. -/
theorem RAMMiddleRep.setInputHead {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {mem : ℕ → ℕ}
    (h : RAMMiddleRep ids cfg mem) (p : Fin (input.length+2)) :
    RAMMiddleRep ids {cfg with inputPos := p} (Function.update mem 4 p.val) := by
  constructor
  · simpa only [Function.update_of_ne (by decide : 3 ≠ 4)] using h.lengthInput
  · simp
  · simpa only [Function.update_of_ne (by decide : 5 ≠ 4)] using h.lengthOutput
  · simpa only [Function.update_of_ne (by decide : 6 ≠ 4)] using h.control
  · simpa only [Function.update_of_ne (by decide : 7 ≠ 4)] using h.zeroReg
  · simpa only [Function.update_of_ne (by decide : 8 ≠ 4)] using h.oneReg
  · intro j; simpa only [Function.update_of_ne (small_ne_address (by decide : 4 < 32) 0 j)] using h.inputLane j
  · intro j; simpa only [Function.update_of_ne (small_ne_address (by decide : 4 < 32) 1 j)] using h.outputLane j
  · intro i; simpa only [Function.update_of_ne (Ne.symm (small_ne_workSide (by decide : 4 < 32) i))] using h.headSign i
  · intro i; simpa only [Function.update_of_ne (Ne.symm (small_ne_workSide (by decide : 4 < 32) i)),
      Function.update_of_ne (Ne.symm (small_ne_workMag (by decide : 4 < 32) i))] using h.headWork i
  · intro i j; simpa only [Function.update_of_ne (small_ne_address (by decide : 4 < 32) _ _)] using h.workLane i j

/-- Registers used for arithmetic or scans are excluded from the reference state. -/
def middleScratch (k r : ℕ) : Prop := r = 9 ∨ r = 10 ∨ r = 11 ∨ ∃ i : Fin k, r = workSymbol i

theorem RAMMiddleRep.congr {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m m' : ℕ → ℕ}
    (h : RAMMiddleRep ids cfg m) (he : ∀ r, ¬ middleScratch k r → m' r = m r) :
    RAMMiddleRep ids cfg m' := by
  have small (r : ℕ) (hr : r ≤ 8) : ¬ middleScratch k r := by
    rintro (h₁|h₁|h₁|⟨i,h₁⟩) <;> try omega
    unfold workSymbol workSide at h₁; omega
  have registerSide (i : Fin k) : ¬ middleScratch k (workSide i) := by
    rintro (h₁|h₁|h₁|⟨j,h₁⟩)
    all_goals first | exact workSide_ne_symbol i j h₁ | unfold workSide at h₁; omega
  have registerMag (i : Fin k) : ¬ middleScratch k (workMag i) := by
    rintro (h₁|h₁|h₁|⟨j,h₁⟩)
    all_goals first | exact workMag_ne_symbol i j h₁ | unfold workMag workSide at h₁; omega
  have address (l j : ℕ) : ¬ middleScratch k (ramDataAddress k l j) := by
    have hb := ramDataAddress_ge k l j
    have hbase : 32 ≤ ramDataBase k := by unfold ramDataBase; omega
    rintro (h₁|h₁|h₁|⟨i,h₁⟩) <;> try omega
    have := workSymbol_lt_base i
    omega
  constructor
  · rw [he _ (small 3 (by decide)), h.lengthInput]
  · rw [he _ (small 4 (by decide)), h.headInput]
  · rw [he _ (small 5 (by decide)), h.lengthOutput]
  · rw [he _ (small 6 (by decide)), h.control]
  · rw [he _ (small 7 (by decide)), h.zeroReg]
  · rw [he _ (small 8 (by decide)), h.oneReg]
  · intro j; rw [he _ (address 0 j), h.inputLane]
  · intro j; rw [he _ (address 1 j), h.outputLane]
  · intro i; rw [he _ (registerSide i)]; exact h.headSign i
  · intro i; rw [he _ (registerSide i), he _ (registerMag i), h.headWork]
  · intro i j; rw [he _ (address _ _), h.workLane]

theorem RAMMiddleRep.updateScratch {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {mem : ℕ → ℕ}
    (h : RAMMiddleRep ids cfg mem) {r : ℕ} (hr : middleScratch k r) (v : ℕ) :
    RAMMiddleRep ids cfg (Function.update mem r v) := by
  apply h.congr
  intro s hs
  have hn : s ≠ r := fun he => hs (by simpa only [he] using hr)
  exact Function.update_of_ne hn _ _

/-- Update the source control field at the end of an action. -/
theorem RAMMiddleRep.setControl {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {mem : ℕ → ℕ}
    (h : RAMMiddleRep ids cfg mem) (s : Option Q) :
    RAMMiddleRep ids {cfg with state := s} (Function.update mem 6 (ramStateCode ids s)) := by
  constructor
  · simpa only [Function.update_of_ne (by decide : 3 ≠ 6)] using h.lengthInput
  · simpa only [Function.update_of_ne (by decide : 4 ≠ 6)] using h.headInput
  · simpa only [Function.update_of_ne (by decide : 5 ≠ 6)] using h.lengthOutput
  · simp
  · simpa only [Function.update_of_ne (by decide : 7 ≠ 6)] using h.zeroReg
  · simpa only [Function.update_of_ne (by decide : 8 ≠ 6)] using h.oneReg
  · intro j; simpa only [Function.update_of_ne (small_ne_address (by decide : 6 < 32) 0 j)] using h.inputLane j
  · intro j; simpa only [Function.update_of_ne (small_ne_address (by decide : 6 < 32) 1 j)] using h.outputLane j
  · intro i; simpa only [Function.update_of_ne (Ne.symm (small_ne_workSide (by decide : 6 < 32) i))] using h.headSign i
  · intro i; simpa only [Function.update_of_ne (Ne.symm (small_ne_workSide (by decide : 6 < 32) i)),
      Function.update_of_ne (Ne.symm (small_ne_workMag (by decide : 6 < 32) i))] using h.headWork i
  · intro i j; simpa only [Function.update_of_ne (small_ne_address (by decide : 6 < 32) _ _)] using h.workLane i j

end TimeSpaceMA

namespace TimeSpaceMA.RAMMiddle

open RAMBlock

/-- Repeat `target += source` a fixed number of times. The source and target registers
must be distinct. The number of repetitions is fixed by the tape count. -/
def addRepeated (target source n : ℕ) : Code :=
  Code.chain ((List.replicate n (.add target target source)).map Code.atom)

theorem runs_addRepeated (m : Mem) {target source : ℕ} (h : target ≠ source) (n : ℕ) :
    Runs (addRepeated target source n) m (Function.update m target (m target + n*m source)) n := by
  induction n generalizing m with
  | zero =>
    have he : Function.update m target (m target) = m := by simp
    simpa only [addRepeated, List.replicate_zero, List.map_nil, Code.chain, List.foldr_nil,
      Nat.zero_mul, Nat.add_zero, he] using Runs.skip m
  | succ n ih =>
    let w := Function.update m target (m target + m source)
    have hseq := Runs.seq (Runs.atom (.add target target source) m) (ih w)
    have hm : Function.update w target (w target + n*w source) =
        Function.update m target (m target + (n+1)*m source) := by
      ext r
      by_cases hr : r = target
      · subst r; simp [w, Ne.symm h, Nat.add_mul, Nat.add_assoc, Nat.add_comm]
      · simp [w, hr]
    rw [hm] at hseq
    simpa only [addRepeated, List.replicate_succ, List.map_cons, Code.chain, List.foldr_cons,
      Nat.add_comm 1 n] using hseq

/-- Put the address of a tape cell with index in `source` into the address register. -/
def cellAddress (k lane source : ℕ) : Code :=
  .seq (.const 9 (ramDataBase k + lane)) (addRepeated 9 source (k+2))

private theorem runs_cellAddress (m : Mem) (k lane source : ℕ) (hs : source ≠ 9) :
    Runs (cellAddress k lane source) m
      (Function.update m 9 (ramDataAddress k lane (m source))) (1+(k+2)) := by
  let w := Function.update m 9 (ramDataBase k + lane)
  have h := Runs.seq (Runs.atom (.const 9 (ramDataBase k + lane)) m)
    (runs_addRepeated w (Ne.symm hs) (k+2))
  have he : Function.update w 9 (w 9 + (k+2)*w source) =
      Function.update m 9 (ramDataAddress k lane (m source)) := by
    ext r
    by_cases hr : r = 9
    · subst r; simp [w, hs, ramDataAddress, Nat.mul_comm, Nat.add_left_comm, Nat.add_comm]
    · simp [w, hr]
  rw [he] at h
  exact h

/-- Compute a work tape's current zigzag position, then its lane address. -/
def workAddress {k : ℕ} (i : Fin k) : Code :=
  .seq (.add 11 (workMag i) (workMag i))
    (.seq (.add 11 11 (workSide i)) (cellAddress k (i.val+2) 11))

private theorem runs_workAddress (m : Mem) {k : ℕ} (i : Fin k) :
    Runs (workAddress i) m
      (Function.update (Function.update m 11 (2*m (workMag i)+m (workSide i))) 9
        (ramDataAddress k (i.val+2) (2*m (workMag i)+m (workSide i)))) (1+(1+(1+(k+2)))) := by
  let m₁ := Function.update m 11 (m (workMag i)+m (workMag i))
  let m₂ := Function.update m₁ 11 (m₁ 11+m₁ (workSide i))
  have h := Runs.seq (Runs.atom (.add 11 (workMag i) (workMag i)) m)
    (Runs.seq (Runs.atom (.add 11 11 (workSide i)) m₁)
      (runs_cellAddress m₂ k (i.val+2) 11 (by decide)))
  have hs : workSide i ≠ 11 := by unfold workSide; omega
  have hm : m₂ = Function.update m 11 (2*m (workMag i)+m (workSide i)) := by
    ext r
    by_cases hr : r=11
    · subst r; simp [m₁, m₂, hs, Nat.two_mul]
    · simp [m₁, m₂, hr]
  change Runs _ m (Function.update m₂ 9 (ramDataAddress k (i.val+2) (m₂ 11))) _ at h
  rw [hm] at h
  exact h

/-- Read one work tape into its scan register. -/
def readWork {k : ℕ} (i : Fin k) : Code :=
  .seq (workAddress i) (.load (workSymbol i) 9)

/-- Read the input tape into the input scan register. -/
def readInput (k : ℕ) : Code :=
  .seq (cellAddress k 0 4) (.load 10 9)

/-- Apply the finite signed-head transition. -/
def shiftWork {k : ℕ} (i : Fin k) (d : SignType) : Code :=
  match d with
  | .zero => .skip
  | .neg => .ifLE (workSide i) 7
      (.ifLE (workMag i) 7 (.const (workSide i) 1) (.monus (workMag i) (workMag i) 8))
      (.add (workMag i) (workMag i) 8)
  | .pos => .ifLE (workSide i) 7 (.add (workMag i) (workMag i) 8)
      (.ifLE (workMag i) 7 (.const (workSide i) 0) (.monus (workMag i) (workMag i) 8))

/-- Write at the current work head, leaving subsequent motion to `shiftWork`. -/
def writeWork {k : ℕ} (i : Fin k) (s : Option Bool) : Code :=
  .seq (workAddress i) (.seq (.const 11 (ramSymbol s)) (.store 9 11))

/-- Move the bounded read-only head. -/
def shiftInput (d : SignType) : Code :=
  match d with
  | .zero => .skip
  | .neg => .monus 4 4 8
  | .pos => .ifLE 4 3 (.add 4 4 8) .skip

/-- Append one output bit to the chronological output stream. -/
def appendOutput (k : ℕ) (b : Bool) : Code :=
  .seq (cellAddress k 1 5) (.seq (.const 11 (ramSymbol (some b)))
    (.seq (.store 9 11) (.add 5 5 8)))

/-- Fixed code body to perform one native action on one work tape. -/
def workAction {k : ℕ} (i : Fin k) (a : Option (Option Bool) × SignType) : Code :=
  .seq (match a.1 with | none => .skip | some b => writeWork i b) (shiftWork i a.2)

/-- Fixed code body for a native rule after reading its state and symbols. -/
def action {k q : ℕ} {Q : Type} (ids : Q ≃ Fin q) (a : Turing.Action k Bool Q) : Code :=
  .seq (Code.chain ((List.finRange k).map fun i => workAction i (a.workTapes i)))
    (.seq (shiftInput a.inputTape)
      (.seq (match a.output with | none => .skip | some b => appendOutput k b)
        (.const 6 (ramStateCode ids a.state))))

/-- Dispatch on a register promised to encode a blank or one bit. -/
def symbolCases (r : ℕ) (f : Option Bool → Code) : Code :=
  .ifLE r 7 (f none) (.ifLE r 8 (f (some false)) (f (some true)))

/-- At source-step boundaries, collect every tape symbol before any write or move. -/
def readAll (k : ℕ) : Code :=
  .seq (readInput k) (Code.chain ((List.finRange k).map readWork))

/-- Scan a fixed list of work-symbol registers to select the finite transition. -/
def workCases {k : ℕ} (l : List (Fin k)) (symbols : Fin k → Option Bool)
    (f : (Fin k → Option Bool) → Code) : Code :=
  match l with
  | [] => f symbols
  | i :: l => symbolCases (workSymbol i) fun b => workCases l (Function.update symbols i b) f

/-- A fixed state chooses a transition by finite case analysis on all scanned symbols. -/
noncomputable def dispatchState {k q : ℕ} {Q : Type} (ids : Q ≃ Fin q)
    (tm : Turing.MultiTapeTM k Bool Q) (s : Q) : Code :=
  symbolCases 10 fun b => workCases (List.finRange k) (fun _ => none) fun w =>
    action ids (tm.tr s b w)

/-- Positive state codes are searched in ascending order; no on-line unbounded lookup. -/
noncomputable def dispatch {k q : ℕ} {Q : Type} (ids : Q ≃ Fin q)
    (tm : Turing.MultiTapeTM k Bool Q) (l : List (Fin q)) : Code :=
  match l with
  | [] => .skip
  | i::l => .seq (.const 9 (i.val+1)) (.ifLE 6 9 (dispatchState ids tm (ids.symm i))
      (dispatch ids tm l))

/-- Native execution follows the read and finite dispatch body until state code zero. -/
noncomputable def code {k q : ℕ} {Q : Type} (ids : Q ≃ Fin q)
    (tm : Turing.MultiTapeTM k Bool Q) : Code :=
  .whileLE 8 6 (.seq (readAll k) (dispatch ids tm (List.finRange q)))

private theorem regSide_big {k : ℕ} (i : Fin k) : 32 ≤ workSide i := by unfold workSide; omega
private theorem regMag_big {k : ℕ} (i : Fin k) : 32 ≤ workMag i := by unfold workMag workSide; omega
private theorem regSymbol_big {k : ℕ} (i : Fin k) : 32 ≤ workSymbol i := by unfold workSymbol workSide; omega

private theorem update_same (m : Mem) (r : ℕ) : Function.update m r (m r) = m := by simp
private theorem update_symm {a b : ℕ} (h : a ≠ b) (m : Mem) (x y : ℕ) :
    Function.update (Function.update m a x) b y = Function.update (Function.update m b y) a x := by
  ext r
  by_cases ha : r = a
  · subst r; simp [h]
  by_cases hb : r = b
  · subst r; simp [ha]
  simp [ha,hb]

private theorem outputOf_work_rep {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (i : Fin k) :
    m (ramDataAddress k (i.val+2) (2*m (workMag i)+m (workSide i))) =
      ramSymbol (cfg.workTapeSymbols i) := by
  rw [← ramTapeIndex_head _ _ (h.headSign i), h.headWork i]
  exact h.workLane i _

private theorem runs_readInput {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) :
    ∃ v t, Runs (readInput k) m v t ∧ t ≤ k+4 ∧ RAMMiddleRep ids cfg v ∧
      v 10 = ramSymbol cfg.inputSymbol ∧ ∀ r, r ≠ 9 → r ≠ 10 → v r = m r := by
  let a := ramDataAddress k 0 (m 4)
  let m₁ := Function.update m 9 a
  let v := Function.update m₁ 10 (ramSymbol cfg.inputSymbol)
  have hb : 9 ≠ a := by
    have := ramDataAddress_ge k 0 (m 4)
    unfold ramDataBase at this
    dsimp [a]; omega
  have ha : m₁ (m₁ 9) = ramSymbol cfg.inputSymbol := by
    simp only [m₁, Function.update_self, Function.update_of_ne (Ne.symm hb)]
    dsimp only [a]
    rw [h.headInput, h.inputLane, ramInputSymbol_head]
  refine ⟨v,(1+(k+2))+1, ?_, by omega, ?_, by simp [v], ?_⟩
  · apply Runs.seq (runs_cellAddress m k 0 4 (by decide))
    simpa only [Op.effect, ha, v] using Runs.atom (.load 10 9) m₁
  · exact (h.updateScratch (.inl rfl) _).updateScratch (.inr (.inl rfl)) _
  · intro r h9 h10; simp [v,m₁,h9,h10]

private theorem runs_readWork {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (i : Fin k) :
    ∃ v t, Runs (readWork i) m v t ∧ t ≤ k+6 ∧ RAMMiddleRep ids cfg v ∧
      v (workSymbol i) = ramSymbol (cfg.workTapeSymbols i) ∧
      ∀ r, r ≠ 9 → r ≠ 11 → r ≠ workSymbol i → v r = m r := by
  let j := 2*m (workMag i)+m (workSide i)
  let a := ramDataAddress k (i.val+2) j
  let m₁ := Function.update (Function.update m 11 j) 9 a
  let v := Function.update m₁ (workSymbol i) (ramSymbol (cfg.workTapeSymbols i))
  have ha : m₁ (m₁ 9) = ramSymbol (cfg.workTapeSymbols i) := by
    have hab := ramDataAddress_ge k (i.val+2) j
    unfold ramDataBase at hab
    simp only [m₁, Function.update_self, Function.update_of_ne (by omega : a ≠ 9),
      Function.update_of_ne (by omega : a ≠ 11)]
    exact outputOf_work_rep h i
  refine ⟨v,(1+(1+(1+(k+2))))+1, ?_, by omega, ?_, by simp [v], ?_⟩
  · apply Runs.seq (runs_workAddress m i)
    simpa only [Op.effect, ha, v] using Runs.atom (.load (workSymbol i) 9) m₁
  · exact ((h.updateScratch (.inr (.inr (.inl rfl))) _).updateScratch (.inl rfl) _).updateScratch
      (.inr (.inr (.inr ⟨i,rfl⟩))) _
  · intro r h9 h11 hi; simp [v,m₁,h9,h11,hi]

private theorem runs_shiftInput {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (d : SignType) :
    ∃ v t, Runs (shiftInput d) m v t ∧ t ≤ 2 ∧
      RAMMiddleRep ids { cfg with inputPos := Turing.moveInputPos cfg.inputPos d } v := by
  cases d with
  | zero => exact ⟨m,0,.skip _,by omega,by simpa using h⟩
  | neg =>
    let p := Turing.moveInputPos cfg.inputPos .neg
    have hp : p.val = m 4 - m 8 := by
      rw [h.headInput,h.oneReg]
      by_cases hp₀ : cfg.inputPos = 0
      · simp [p, hp₀]
      · dsimp only [p]; rw [Turing.moveInputPos_neg_of_ne_left _ hp₀]
    exact ⟨_,1,.atom _ _,by omega,by simpa only [Op.effect, ← hp] using h.setInputHead p⟩
  | pos =>
    let p := Turing.moveInputPos cfg.inputPos .pos
    by_cases hc : m 4 ≤ m 3
    · have hp : p.val = m 4 + m 8 := by
        rw [h.headInput,h.lengthInput] at hc
        rw [h.headInput,h.oneReg]
        dsimp only [p]
        rw [Turing.moveInputPos_pos_of_ne_right _ (by omega)]
      exact ⟨_,2,.yes hc (.atom _ _),by omega,by simpa only [Op.effect, ← hp] using h.setInputHead p⟩
    · have hp : cfg.inputPos.val = input.length + 1 := by
        rw [h.headInput,h.lengthInput] at hc
        have := cfg.inputPos.isLt
        omega
      have hep : p = cfg.inputPos := by
        have he : cfg.inputPos = ⟨input.length+1, by omega⟩ := Fin.ext hp
        unfold p; rw [he]; exact Turing.moveInputPos_rightBoundary
      refine ⟨m,2,.no hc (.skip m),by omega,?_⟩
      change RAMMiddleRep ids {cfg with inputPos := p} m
      rw [hep]
      cases cfg
      exact h

private theorem runs_shiftWork {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (i : Fin k) (d : SignType) :
    ∃ t, Runs (shiftWork i d) m (ramChangeWorkHead m i d) t ∧ t ≤ 5 := by
  let x := workSide i
  let y := workMag i
  have hxy : x ≠ y := workSide_ne_mag i i
  have hm (p : ℕ) : Function.update (Function.update m x (m x)) y p = Function.update m y p := by simp
  have hf (p : ℕ) : Function.update (Function.update m x p) y (m y) = Function.update m x p := by
    rw [update_symm hxy, update_same]
  have hside := h.headSign i
  change m x ≤ 1 at hside
  cases d with
  | zero =>
    have he : ramChangeWorkHead m i .zero = m := by simp [ramChangeWorkHead, ramMoveWork]
    rw [he]
    exact ⟨0,Runs.skip m,by omega⟩
  | neg =>
    change ∃ t, Runs (.ifLE x 7 (.ifLE y 7 (.const x 1) (.monus y y 8)) (.add y y 8)) _ _ t ∧ _
    by_cases hs : m x ≤ m 7
    · have hs' : m x = 0 := by rw [h.zeroReg] at hs; omega
      by_cases hz : m y ≤ m 7
      · have hz' : m y = 0 := by rw [h.zeroReg] at hz; omega
        refine ⟨1+(1+1),.yes hs (.yes hz ?_),by omega⟩
        have he : ramChangeWorkHead m i .neg = Function.update m x 1 := by
          change Function.update (Function.update m x (ramMoveWork (m x) (m y) .neg).1)
            y (ramMoveWork (m x) (m y) .neg).2 = _
          simp only [ramMoveWork,hs',hz',if_true]
          simpa only [hz'] using hf 1
        rw [he]
        exact .atom _ _
      · have hz' : m y ≠ 0 := by rw [h.zeroReg] at hz; omega
        refine ⟨1+(2+1),.yes hs (.no hz ?_),by omega⟩
        have he : ramChangeWorkHead m i .neg = Function.update m y (m y-m 8) := by
          change Function.update (Function.update m x (ramMoveWork (m x) (m y) .neg).1)
            y (ramMoveWork (m x) (m y) .neg).2 = _
          simp only [ramMoveWork,hs',if_true,if_neg hz',h.oneReg]
          simpa only [hs'] using hm (m y-1)
        rw [he]
        exact .atom _ _
    · have hs' : m x = 1 := by rw [h.zeroReg] at hs; omega
      refine ⟨2+1,.no hs ?_,by omega⟩
      have he : ramChangeWorkHead m i .neg = Function.update m y (m y+m 8) := by
        change Function.update (Function.update m x (ramMoveWork (m x) (m y) .neg).1)
          y (ramMoveWork (m x) (m y) .neg).2 = _
        simp only [ramMoveWork,hs',if_neg (by decide : 1 ≠ 0),h.oneReg]
        simpa only [hs'] using hm (m y+1)
      rw [he]
      exact .atom _ _
  | pos =>
    change ∃ t, Runs (.ifLE x 7 (.add y y 8)
      (.ifLE y 7 (.const x 0) (.monus y y 8))) _ _ t ∧ _
    by_cases hs : m x ≤ m 7
    · have hs' : m x = 0 := by rw [h.zeroReg] at hs; omega
      refine ⟨1+1,.yes hs ?_,by omega⟩
      have he : ramChangeWorkHead m i .pos = Function.update m y (m y+m 8) := by
        change Function.update (Function.update m x (ramMoveWork (m x) (m y) .pos).1)
          y (ramMoveWork (m x) (m y) .pos).2 = _
        simp only [ramMoveWork,hs',if_true,h.oneReg]
        simpa only [hs'] using hm (m y+1)
      rw [he]
      exact .atom _ _
    · have hs' : m x = 1 := by rw [h.zeroReg] at hs; omega
      by_cases hz : m y ≤ m 7
      · have hz' : m y = 0 := by rw [h.zeroReg] at hz; omega
        refine ⟨2+(1+1),.no hs (.yes hz ?_),by omega⟩
        have he : ramChangeWorkHead m i .pos = Function.update m x 0 := by
          change Function.update (Function.update m x (ramMoveWork (m x) (m y) .pos).1)
            y (ramMoveWork (m x) (m y) .pos).2 = _
          simp only [ramMoveWork,hs',if_neg (by decide : 1 ≠ 0),hz',if_true]
          simpa only [hz'] using hf 0
        rw [he]
        exact .atom _ _
      · have hz' : m y ≠ 0 := by rw [h.zeroReg] at hz; omega
        refine ⟨2+(2+1),.no hs (.no hz ?_),by omega⟩
        have he : ramChangeWorkHead m i .pos = Function.update m y (m y-m 8) := by
          change Function.update (Function.update m x (ramMoveWork (m x) (m y) .pos).1)
            y (ramMoveWork (m x) (m y) .pos).2 = _
          simp only [ramMoveWork,hs',if_neg (by decide : 1 ≠ 0),if_neg hz',h.oneReg]
          simpa only [hs'] using hm (m y-1)
        rw [he]
        exact .atom _ _

private theorem runs_writeWork {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (i : Fin k) (b : Option Bool) :
    ∃ v t, Runs (writeWork i b) m v t ∧ t ≤ k+7 ∧
      RAMMiddleRep ids
        { cfg with workTapes :=
          Function.update cfg.workTapes i (Function.update (cfg.workTapes i) (cfg.workTapePos i) b) } v := by
  let j := 2*m (workMag i)+m (workSide i)
  let a := ramDataAddress k (i.val+2) j
  let m₁ := Function.update (Function.update m 11 j) 9 a
  let m₂ := Function.update m₁ 11 (ramSymbol b)
  let v := Function.update m₂ a (ramSymbol b)
  have ha : m₂ 9 = a := by simp [m₂,m₁]
  have hb : m₂ 11 = ramSymbol b := by simp [m₂]
  refine ⟨v,(1+(1+(1+(k+2))))+(1+1),?_ , by omega, ?_⟩
  · apply Runs.seq (runs_workAddress m i)
    apply Runs.seq (Runs.atom (.const 11 (ramSymbol b)) m₁)
    simpa only [Op.effect, ha, hb, v] using (Runs.atom (.store 9 11) m₂)
  · have hr := h.writeWork i b
    apply hr.congr
    intro r hs
    have h9 : r ≠ 9 := fun he => hs (.inl he)
    have h11 : r ≠ 11 := fun he => hs (.inr (.inr (.inl he)))
    by_cases hra : r = a
    · subst r; simp [v,ramWriteWork,a,j]
    · change Function.update (Function.update (Function.update (Function.update m 11 j) 9 a) 11
        (ramSymbol b)) a (ramSymbol b) r = Function.update m a (ramSymbol b) r
      simp only [Function.update_of_ne hra, Function.update_of_ne h9, Function.update_of_ne h11]

private theorem runs_appendOutput {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (b : Bool) :
    ∃ v t, Runs (appendOutput k b) m v t ∧ t ≤ k+6 ∧
      RAMMiddleRep ids { cfg with output := cfg.output ++ [b] } v := by
  let a := ramDataAddress k 1 (m 5)
  let m₁ := Function.update m 9 a
  let m₂ := Function.update m₁ 11 (ramSymbol (some b))
  let m₃ := Function.update m₂ a (ramSymbol (some b))
  let v := Function.update m₃ 5 (m 5+1)
  have hbase := ramDataAddress_ge k 1 (m 5)
  unfold ramDataBase at hbase
  have ha : m₂ 9 = a := by simp [m₂,m₁]
  have hb : m₂ 11 = ramSymbol (some b) := by simp [m₂]
  have h5 : m₃ 5 = m 5 := by simp [m₃,m₂,m₁,show 5 ≠ a by omega]
  have h8 : m₃ 8 = 1 := by simp [m₃,m₂,m₁, show 8 ≠ a by omega, h.oneReg]
  refine ⟨v,(1+(k+2))+(1+(1+1)),?_ ,by omega,?_⟩
  · apply Runs.seq (runs_cellAddress m k 1 5 (by decide))
    apply Runs.seq (Runs.atom (.const 11 (ramSymbol (some b))) m₁)
    have hs : Runs (.store 9 11) m₂ m₃ 1 := by
      simpa only [Op.effect, ha, hb,m₃] using Runs.atom (.store 9 11) m₂
    apply Runs.seq hs
    simpa only [Op.effect,h5,h8,v] using Runs.atom (.add 5 5 8) m₃
  · apply (h.appendOutput b).congr
    intro r hs
    have h9 : r ≠ 9 := fun he => hs (.inl he)
    have h11 : r ≠ 11 := fun he => hs (.inr (.inr (.inl he)))
    by_cases hr : r = 5
    · subst r; simp [v,ramAppendOutput]
    · by_cases hra : r = a
      · subst r; simp [v,m₃,ramAppendOutput,a,hr]
      · simp [v,m₃,m₂,m₁,ramAppendOutput,a,h9,h11,hr,hra]

/-- The sequential write/move operations update one coordinate of the selected native action. -/
def applyWork {k : ℕ} {Q : Type} {input : List Bool} (cfg : Turing.Cfg k Bool Q input)
    (i : Fin k) (a : Option (Option Bool) × SignType) : Turing.Cfg k Bool Q input :=
  { cfg with
    workTapes := Function.update cfg.workTapes i <| match a.1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
    workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i + (a.2.cast : ℤ)) }

private theorem runs_workAction {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (i : Fin k) (a : Option (Option Bool) × SignType) :
    ∃ v t, Runs (workAction i a) m v t ∧ t ≤ k+12 ∧ RAMMiddleRep ids (applyWork cfg i a) v := by
  obtain ⟨write,dir⟩ := a
  cases write with
  | none =>
    obtain ⟨t,hr,ht⟩ := runs_shiftWork h i dir
    refine ⟨_,0+t,.seq (.skip m) hr,by omega,?_⟩
    simpa only [applyWork, Function.update_eq_self] using h.moveWork i dir
  | some b =>
    obtain ⟨w,t,ht,htime,hw⟩ := runs_writeWork h i b
    obtain ⟨u,hu,huTime⟩ := runs_shiftWork hw i dir
    exact ⟨_,t+u,.seq ht hu,by omega,hw.moveWork i dir⟩

private def applyWorks {k : ℕ} {Q : Type} {input : List Bool}
    (a : Fin k → Option (Option Bool) × SignType) (l : List (Fin k))
    (cfg : Turing.Cfg k Bool Q input) : Turing.Cfg k Bool Q input :=
  l.foldl (fun d i => applyWork d i (a i)) cfg

private theorem applyWorks_fields {k : ℕ} {Q : Type} {input : List Bool}
    (a : Fin k → Option (Option Bool) × SignType) (l : List (Fin k)) (hn : l.Nodup)
    (cfg : Turing.Cfg k Bool Q input) :
    let v := applyWorks a l cfg
    v.state = cfg.state ∧ v.inputPos = cfg.inputPos ∧ v.output = cfg.output ∧
    (∀ i, v.workTapes i = if i ∈ l then
      match (a i).1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
      else cfg.workTapes i) ∧
    ∀ i, v.workTapePos i = if i ∈ l then cfg.workTapePos i + ((a i).2.cast : ℤ) else cfg.workTapePos i := by
  dsimp only
  induction l generalizing cfg with
  | nil => simp [applyWorks]
  | cons j l ih =>
    obtain ⟨hjl,hnl⟩ := List.nodup_cons.mp hn
    change let v := applyWorks a l (applyWork cfg j (a j)); _
    dsimp only
    obtain ⟨hs,hi,ho,hw,hp⟩ := ih hnl (applyWork cfg j (a j))
    refine ⟨hs,hi,ho, ?_, ?_⟩
    · intro i
      change (applyWorks a l (applyWork cfg j (a j))).workTapes i = _
      rw [hw]
      by_cases hij : i = j
      · subst i; simp [hjl, applyWork]
      · simp [hij, applyWork]
    · intro i
      change (applyWorks a l (applyWork cfg j (a j))).workTapePos i = _
      rw [hp]
      by_cases hij : i = j
      · subst i; simp [hjl, applyWork]
      · simp [hij, applyWork]

private theorem runs_workActions {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (a : Fin k → Option (Option Bool) × SignType) (l : List (Fin k)) :
    ∃ v t, Runs (Code.chain (l.map fun i => workAction i (a i))) m v t ∧
      t ≤ l.length*(k+12) ∧ RAMMiddleRep ids (applyWorks a l cfg) v := by
  induction l generalizing m cfg with
  | nil => exact ⟨m,0,.skip _,by simp,h⟩
  | cons i l ih =>
    obtain ⟨w,t,ht,htime,hw⟩ := runs_workAction h i (a i)
    obtain ⟨v,u,hu,hut,hv⟩ := ih hw
    refine ⟨v,t+u,.seq ht hu,?_,hv⟩
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem runs_output {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (b : Option Bool) :
    ∃ v t, Runs (match b with | none => .skip | some x => appendOutput k x) m v t ∧
      t ≤ k+6 ∧ RAMMiddleRep ids {cfg with output := cfg.output ++ b.toList} v := by
  cases b with
  | none => exact ⟨m,0,.skip _,by omega,by simpa using h⟩
  | some b => exact runs_appendOutput h b

private theorem runs_action {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (a : Turing.Action k Bool Q) :
    ∃ v t, Runs (action ids a) m v t ∧ t ≤ k*(k+12)+k+9 ∧ RAMMiddleRep ids (a.apply cfg) v := by
  let l := List.finRange k
  have hl : l.Nodup := List.nodup_finRange k
  have hit (i : Fin k) : i ∈ l := List.mem_finRange i
  obtain ⟨w,t,ht,htime,hw⟩ := runs_workActions h a.workTapes l
  obtain ⟨x,u,hu,huTime,hx⟩ := runs_shiftInput hw a.inputTape
  obtain ⟨y,z,hz,hzTime,hy⟩ := runs_output hx a.output
  have hf := hy.setControl a.state
  refine ⟨_,t+(u+(z+1)),.seq ht (.seq hu (.seq hz (.atom _ _))),?_,?_⟩
  · change t ≤ (List.finRange k).length*(k+12) at htime
    rw [List.length_finRange] at htime
    omega
  · obtain ⟨hs,hi,ho,hwork,hpos⟩ := applyWorks_fields a.workTapes l hl cfg
    change RAMMiddleRep ids (a.apply cfg) (Function.update y 6 (ramStateCode ids a.state))
    convert hf using 1
    apply Turing.Cfg.ext
    · rfl
    · change Turing.moveInputPos cfg.inputPos a.inputTape =
        Turing.moveInputPos (applyWorks a.workTapes l cfg).inputPos a.inputTape
      rw [hi]
    · funext i
      rw [Turing.Action.apply_workTapes]
      dsimp only
      have hh := hwork i
      rw [if_pos (hit i)] at hh
      cases hcase : (a.workTapes i).1 <;> simp only [hcase] at hh ⊢
      all_goals exact hh.symm
    · funext i
      rw [Turing.Action.apply_workTapePos]
      simpa only [if_pos (hit i)] using (hpos i).symm
    · change cfg.output ++ a.output.toList = (applyWorks a.workTapes l cfg).output ++ a.output.toList
      rw [ho]

private theorem runs_readWorks {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (l : List (Fin k)) :
    ∃ v t, Runs (Code.chain (l.map readWork)) m v t ∧
      t ≤ l.length*(k+6) ∧ RAMMiddleRep ids cfg v ∧
      v 10 = m 10 ∧ ∀ i : Fin k,
        v (workSymbol i) = if i ∈ l then ramSymbol (cfg.workTapeSymbols i) else m (workSymbol i) := by
  induction l generalizing m with
  | nil => exact ⟨m,0,.skip _,by simp,h,rfl,by simp⟩
  | cons i l ih =>
    obtain ⟨w,t,ht,htime,hw,hwi,hwRegs⟩ := runs_readWork h i
    obtain ⟨v,u,hu,huTime,hv,hv10,hvRegs⟩ := ih hw
    refine ⟨v,t+u,.seq ht hu,?_,hv,?_,?_⟩
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · rw [hv10,hwRegs 10 (by decide) (by decide) (by have := regSymbol_big i; omega)]
    · intro j
      rw [hvRegs]
      by_cases hj : j=i
      · subst j; simp [hwi]
      · have hs : workSymbol j ≠ workSymbol i := fun he => hj (workSymbol_injective he)
        rw [hwRegs _ (by have := regSymbol_big j; omega) (by have := regSymbol_big j; omega) hs]
        simp only [List.mem_cons, hj, false_or]

private theorem runs_readAll {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    {input : List Bool} {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) :
    ∃ v t, Runs (readAll k) m v t ∧ t ≤ k+4+k*(k+6) ∧
      RAMMiddleRep ids cfg v ∧ RAMReadRep cfg v := by
  obtain ⟨w,t,ht,htime,hw,hread,_⟩ := runs_readInput h
  obtain ⟨v,u,hu,huTime,hv,hv10,hvRegs⟩ := runs_readWorks hw (List.finRange k)
  refine ⟨v,t+u,.seq ht hu,?_,hv,⟨hv10.trans hread,?_⟩⟩
  · rw [List.length_finRange] at huTime; omega
  · intro i; simpa only [List.mem_finRange, if_true] using hvRegs i

/-- A ternary case test chooses the required branch, using at most four test or jump steps. -/
private theorem runs_symbolCases {m v : Mem} {r t : ℕ} {b : Option Bool}
    (f : Option Bool → Code) (h0 : m 7=0) (h1 : m 8=1) (hb : m r = ramSymbol b)
    (h : Runs (f b) m v t) : ∃ u, Runs (symbolCases r f) m v u ∧ u ≤ t+4 := by
  cases b with
  | none => exact ⟨1+t,.yes (by rw [hb,h0]; decide) h,by omega⟩
  | some b =>
    cases b
    · refine ⟨2+(1+t),.no ?_ (.yes ?_ h),by omega⟩ <;> first | rw [hb,h0]; decide | rw [hb,h1]; decide
    · refine ⟨2+(2+t),.no ?_ (.no ?_ h),by omega⟩ <;> first | rw [hb,h0]; decide | rw [hb,h1]; decide

private theorem runs_workCases {k : ℕ} {m v : Mem} {t : ℕ}
    (l : List (Fin k)) (symbols scanned : Fin k → Option Bool)
    (f : (Fin k → Option Bool) → Code)
    (h0 : m 7=0) (h1 : m 8=1)
    (hreads : ∀ i, m (workSymbol i) = ramSymbol (scanned i))
    (hSymbols : ∀ i, i ∉ l → symbols i = scanned i)
    (h : Runs (f scanned) m v t) :
    ∃ u, Runs (workCases l symbols f) m v u ∧ u ≤ t+4*l.length := by
  induction l generalizing symbols with
  | nil =>
    have he : symbols = scanned := funext fun i => hSymbols i (by simp)
    exact ⟨t,by simpa only [workCases,he] using h,by simp⟩
  | cons i l ih =>
    have hb : ∀ j, j ∉ l → Function.update symbols i (scanned i) j = scanned j := by
      intro j hj
      by_cases he : j=i
      · subst j; simp
      · rw [Function.update_of_ne he]
        exact hSymbols j (by simpa [he] using hj)
    obtain ⟨u,hu,ht⟩ := ih (Function.update symbols i (scanned i)) hb
    obtain ⟨w,hw,hwtime⟩ := runs_symbolCases
      (fun b => workCases l (Function.update symbols i b) f) h0 h1 (hreads i) hu
    refine ⟨w,hw,?_⟩
    simp [Nat.mul_add]
    omega

private theorem runs_dispatchState {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    (tm : Turing.MultiTapeTM k Bool Q) (s : Q) {input : List Bool}
    {cfg : Turing.Cfg k Bool Q input} {m : Mem}
    (h : RAMMiddleRep ids cfg m) (hread : RAMReadRep cfg m) :
    ∃ v t, Runs (dispatchState ids tm s) m v t ∧ t ≤ k*(k+12)+5*k+13 ∧
      RAMMiddleRep ids ((tm.tr s cfg.inputSymbol cfg.workTapeSymbols).apply cfg) v := by
  obtain ⟨v,t,ha,hat,hv⟩ := runs_action h (tm.tr s cfg.inputSymbol cfg.workTapeSymbols)
  obtain ⟨u,hu,hut⟩ := runs_workCases (List.finRange k) (fun _ => none) cfg.workTapeSymbols
    (fun w => action ids (tm.tr s cfg.inputSymbol w)) h.zeroReg h.oneReg hread.workRead
    (fun i hi => (hi (List.mem_finRange i)).elim) ha
  obtain ⟨w,hw,hwt⟩ := runs_symbolCases
    (fun b => workCases (List.finRange k) (fun _ => none) fun a => action ids (tm.tr s b a))
    h.zeroReg h.oneReg hread.inputRead hu
  refine ⟨v,w,hw,?_,hv⟩
  rw [List.length_finRange] at hut
  omega

private theorem readRep_update9 {k : ℕ} {Q : Type} {input : List Bool}
    {cfg : Turing.Cfg k Bool Q input} {m : Mem} (h : RAMReadRep cfg m) (v : ℕ) :
    RAMReadRep cfg (Function.update m 9 v) := by
  constructor
  · simpa using h.inputRead
  · intro i
    have hi : workSymbol i ≠ 9 := by have := regSymbol_big i; omega
    simpa only [Function.update_of_ne hi] using h.workRead i

/-- Test the exact code for the live state in a sorted finite state table. -/
private theorem runs_dispatch {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    (tm : Turing.MultiTapeTM k Bool Q) {input : List Bool}
    {cfg : Turing.Cfg k Bool Q input} {m : Mem} (s : Q) (hs : cfg.state = some s)
    (h : RAMMiddleRep ids cfg m) (hread : RAMReadRep cfg m)
    (l : List (Fin q)) (hl : ids s ∈ l) (hSorted : l.Pairwise (· < ·)) :
    ∃ v t, Runs (dispatch ids tm l) m v t ∧
      t ≤ 3*l.length + (k*(k+12)+5*k+13) ∧ RAMMiddleRep ids (tm.step cfg) v := by
  induction l generalizing m with
  | nil => simp at hl
  | cons i l ih =>
    let w := Function.update m 9 (i.val+1)
    have hw : RAMMiddleRep ids cfg w := h.updateScratch (.inl rfl) _
    have hwr : RAMReadRep cfg w := readRep_update9 hread _
    have hstate : w 6 = (ids s).val+1 := by simp [w,h.control,hs,ramStateCode,Nat.add_comm]
    have h9 : w 9 = i.val+1 := by simp [w]
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hSorted
    by_cases hi : ids s = i
    · have hEq : ids.symm i = s := by rw [← hi, Equiv.symm_apply_apply]
      have hcheck : w 6 ≤ w 9 := by rw [hstate,h9,hi]
      obtain ⟨v,t,ht,htime,hv⟩ := runs_dispatchState tm (ids.symm i) hw hwr
      refine ⟨v,1+(1+t),.seq (.atom _ _) (.yes hcheck ht),?_,?_⟩
      · simp only [List.length_cons, Nat.mul_add] at htime ⊢; omega
      · rw [hEq] at hv
        rwa [tm.step_of_state hs]
    · have hmem : ids s ∈ l := (List.mem_cons.mp hl).resolve_left hi
      have hcheck : ¬ w 6 ≤ w 9 := by
        rw [hstate,h9]
        have ht : i.val < (ids s).val := hhead _ hmem
        omega
      obtain ⟨v,t,ht,htime,hv⟩ := ih hw hwr hmem htail
      refine ⟨v,1+(2+t),.seq (.atom _ _) (.no hcheck ht),?_,hv⟩
      simp only [List.length_cons, Nat.mul_add] at htime ⊢
      omega

/-- A constant bound, depending only on the fixed source machine's tape and state counts,
for simulating one source transition as RAM primitive steps. -/
def stepCount (k q : ℕ) : ℕ := (k+4+k*(k+6)) + (3*q+(k*(k+12)+5*k+13))

private theorem runs_step {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    (tm : Turing.MultiTapeTM k Bool Q) {input : List Bool}
    {cfg : Turing.Cfg k Bool Q input} {m : Mem} (s : Q) (hs : cfg.state = some s)
    (h : RAMMiddleRep ids cfg m) :
    ∃ v t, Runs (.seq (readAll k) (dispatch ids tm (List.finRange q))) m v t ∧
      t ≤ stepCount k q ∧ RAMMiddleRep ids (tm.step cfg) v := by
  obtain ⟨w,t,ht,htt,hw,hread⟩ := runs_readAll h
  obtain ⟨v,u,hu,huu,hv⟩ := runs_dispatch tm s hs hw hread (List.finRange q)
    (List.mem_finRange (ids s)) (List.pairwise_lt_finRange q)
  refine ⟨v,t+u,.seq ht hu,?_,hv⟩
  rw [List.length_finRange] at huu
  exact Nat.add_le_add htt huu

private theorem runs_until_halt {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    (tm : Turing.MultiTapeTM k Bool Q) {input : List Bool}
    (t : ℕ) {cfg : Turing.Cfg k Bool Q input} {m : Mem} (h : RAMMiddleRep ids cfg m)
    (hh : (tm.runFrom cfg t).Halted) :
    ∃ v cost, Runs (code ids tm) m v cost ∧
      cost ≤ (stepCount k q+2)*t+2 ∧ RAMMiddleRep ids (tm.runFrom cfg t) v := by
  induction t generalizing cfg m with
  | zero =>
    change cfg.state = none at hh
    have h6 : m 6 = 0 := by rw [h.control,hh]; rfl
    have hn : ¬ m 8 ≤ m 6 := by rw [h.oneReg,h6]; decide
    exact ⟨m,2,.done hn,by simp,h⟩
  | succ t ih =>
    cases hst : cfg.state with
    | none =>
      have h6 : m 6 = 0 := by rw [h.control,hst]; rfl
      have hn : ¬ m 8 ≤ m 6 := by rw [h.oneReg,h6]; decide
      have hf : tm.runFrom cfg (t+1) = cfg :=
        Turing.MultiTapeTM.runFrom_eq_of_halt tm cfg (τ := 0) (Nat.zero_le _) hst
      exact ⟨m,2,.done hn,by omega,hf.symm ▸ h⟩
    | some s =>
      have hg : m 8 ≤ m 6 := by rw [h.oneReg,h.control,hst]; simp [ramStateCode]
      obtain ⟨w,u,hu,htime,hw⟩ := runs_step tm s hst h
      have hshift : tm.runFrom cfg (t+1) = tm.runFrom (tm.step cfg) t := by
        unfold Turing.MultiTapeTM.runFrom
        exact Function.iterate_succ_apply _ _ _
      rw [hshift] at hh ⊢
      obtain ⟨v,cost,hv,hcost,hrep⟩ := ih hw hh
      refine ⟨v,2+u+cost,.again hg hu hv,?_,hrep⟩
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- Exact simulation between the encoder and decoder, with absolute unit-step time linear
in the number of fixed native source steps. -/
theorem runs {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    (tm : Turing.MultiTapeTM k Bool Q) {input output : List Bool} {m : Mem} (t : ℕ)
    (h : RAMMiddleRep ids (tm.initCfg input) m)
    (hh : (tm.runFrom (tm.initCfg input) t).Halted)
    (ho : (tm.runFrom (tm.initCfg input) t).output = output) :
    ∃ v cost, Runs (code ids tm) m v cost ∧ cost ≤ (stepCount k q+2)*t+2 ∧
      v 5 = output.length ∧ v 7 = 0 ∧
      ∀ j, v (ramDataAddress k 1 j) = ramSymbol output[j]? := by
  obtain ⟨v,cost,hv,ht,hr⟩ := runs_until_halt tm t h hh
  refine ⟨v,cost,hv,ht,hr.lengthOutput.trans (congrArg List.length ho),hr.zeroReg,?_⟩
  intro j
  rw [hr.outputLane,ho]

end TimeSpaceMA.RAMMiddle

namespace TimeSpaceMA.RAMMiddle

open RAMBlock Turing.MultiTapeTM

/-- Native time gives a middle-block execution and also bounds the length of the output
handed to the decoder. -/
theorem runs_of_native {k q : ℕ} {Q : Type} {ids : Q ≃ Fin q}
    (tm : Turing.MultiTapeTM k Bool Q) {input output : List Bool} {m : Mem} (t : ℕ)
    (h : RAMMiddleRep ids (tm.initCfg input) m)
    (hc : tm.Computes input output) (ht : tm.RunsInTime input t) :
    ∃ v cost, Runs (code ids tm) m v cost ∧ cost ≤ (stepCount k q+2)*t+2 ∧
      output.length ≤ t ∧ v 5 = output.length ∧ v 7 = 0 ∧
      ∀ j, v (ramDataAddress k 1 j) = ramSymbol output[j]? := by
  have hh := runsInTime_iff_halted.mp ht
  obtain ⟨u,hu,ho⟩ := hc
  have hsame : tm.runFrom (tm.initCfg input) t = tm.runFrom (tm.initCfg input) u := by
    rcases Nat.le_total t u with htu | hut
    · exact (runFrom_eq_of_halt tm _ htu hh).symm
    · exact runFrom_eq_of_halt tm _ hut hu
  have hout : (tm.runFrom (tm.initCfg input) t).output = output := (congrArg Turing.Cfg.output hsame).trans ho
  have hlen : output.length ≤ t := by
    have hl := tm.length_output_runFrom_le (tm.initCfg input) t
    rw [hout] at hl
    simpa only [Turing.MultiTapeNTM.initCfg, Turing.Cfg.init, List.length_nil, Nat.zero_add] using hl
  obtain ⟨v,c,hr,hc,hv,h0,hm⟩ := runs tm t h hh hout
  exact ⟨v,c,hr,hc,hlen,hv,h0,hm⟩

end TimeSpaceMA.RAMMiddle

namespace TimeSpaceMA.RAMBlock

/-- Registers 7=0, 8=1, 11=remainder, 12=quotient, 13=power, 14=half-power, 15=double-power,
16=two. Find the largest even power at most the current remainder. -/
def halfDoubleOps : List Op := [.add 14 13 7, .add 13 15 7, .add 15 15 15]

def halfDoubleLoop : Code := .whileLE 15 11 (.chain (halfDoubleOps.map Code.atom))

def halfPrepareOps : List Op := [.const 13 2, .const 14 1, .const 15 4]

def halfTakeOps : List Op := [.monus 11 11 13, .add 12 12 14]

def halfBody : Code := .seq (.chain (halfPrepareOps.map Code.atom))
  (.seq halfDoubleLoop (.chain (halfTakeOps.map Code.atom)))

def halfLoop : Code := .whileLE 16 11 halfBody

def halve : Code := .seq (.const 12 0) halfLoop

private theorem power_double_steps (m : Mem) (h7 : m 7 = 0) :
    execAtoms m halfDoubleOps = Function.update (Function.update (Function.update m 14 (m 13))
      13 (m 15)) 15 (m 15 + m 15) := by
  simp [execAtoms, halfDoubleOps, Op.effect, h7]

private theorem power_prepare_steps (m : Mem) :
    execAtoms m halfPrepareOps = Function.update (Function.update (Function.update m 13 2) 14 1) 15 4 := rfl

private theorem half_take_steps (m : Mem) :
    execAtoms m halfTakeOps = Function.update (Function.update m 11 (m 11 - m 13))
      12 (m 12 + m 14) := by
  simp [execAtoms, halfTakeOps, Op.effect]

private theorem size_lt_of_lt_two_pow {r j : ℕ} (h : r < 2^j) : r.size ≤ j := Nat.size_le.mpr h

private theorem size_ge_of_two_pow_le {r j : ℕ} (h : 2^j ≤ r) : j < r.size := Nat.lt_size.mpr h

private theorem halfDoubleLoop_runs (m : Mem) (j F : ℕ)
    (hf : m 11 < 2^(j+F+1)) (h7 : m 7 = 0)
    (h13 : m 13 = 2^(j+1)) (h14 : m 14 = 2^j) (h15 : m 15 = 2^(j+1+1)) :
    ∃ out t l, Runs halfDoubleLoop m out t ∧ t ≤ 5*F+2 ∧
      out 13 = 2^(l+1) ∧ out 14 = 2^l ∧ out 15 = 2^(l+1+1) ∧
      out 11 < 2^(l+1+1) ∧
      (m 13 ≤ m 11 → out 13 ≤ out 11) ∧
      ∀ r, r ≠ 13 → r ≠ 14 → r ≠ 15 → out r = m r := by
  induction F generalizing j m with
  | zero =>
    have hn : ¬ m 15 ≤ m 11 := by
      rw [h15]
      have hp : (2 : ℕ)^(j+1) ≤ 2^(j+1+1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le hf hp)
    refine ⟨m,2,j,.done hn,by omega,h13,h14,h15,?_,fun h => h,fun _ _ _ _ => rfl⟩
    rw [← h15]
    exact Nat.lt_of_not_ge hn
  | succ F ih =>
    by_cases hnext : m 15 ≤ m 11
    · let mm := execAtoms m halfDoubleOps
      have he := power_double_steps m h7
      have hm13 : mm 13 = 2^(j+1+1) := by simpa [mm, he] using h15
      have hm14 : mm 14 = 2^(j+1) := by simpa [mm, he] using h13
      have hm15 : mm 15 = 2^(j+1+1+1) := by
        simp only [mm, he, Function.update_self]
        rw [h15, show (2:ℕ)^(j+1+1+1)=2^(j+1+1)*2 from Nat.pow_succ _ _, Nat.mul_two]
      have hun (r : ℕ) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) : mm r = m r := by
        simp [mm, he, Function.update_of_ne h13, Function.update_of_ne h14, Function.update_of_ne h15]
      have hmf : mm 11 < 2^((j+1)+F+1) := by
        rw [hun 11 (by decide) (by decide) (by decide), show (j+1)+F+1=j+(F+1)+1 by omega]
        exact hf
      have hm7 : mm 7 = 0 := by rw [hun 7 (by decide) (by decide) (by decide), h7]
      obtain ⟨out,t,l,hr,ht,ha,hb,hc,hd,hm,hpres⟩ := ih mm (j+1) hmf hm7 hm13 hm14 hm15
      refine ⟨out,2+3+t,l,.again hnext (runs_atoms m halfDoubleOps) hr,by omega,ha,hb,hc,hd,?_,?_⟩
      · intro _
        apply hm
        rw [hm13, hun 11 (by decide) (by decide) (by decide), ← h15]
        exact hnext
      · intro r hr₁ hr₂ hr₃
        rw [hpres r hr₁ hr₂ hr₃, hun r hr₁ hr₂ hr₃]
    · refine ⟨m,2,j,.done hnext,by omega,h13,h14,h15,?_,fun h => h,fun _ _ _ _ => rfl⟩
      rw [← h15]
      exact Nat.lt_of_not_ge hnext

private theorem halfBody_runs (m : Mem) (h7 : m 7 = 0) (hr : 2 ≤ m 11) :
    ∃ out t l, Runs halfBody m out t ∧ t ≤ 5*(m 11).size + 7 ∧
      out 11 = m 11 - 2^(l+1) ∧ out 12 = m 12 + 2^l ∧
      2^(l+1) ≤ m 11 ∧ m 11 < 2^(l+1+1) ∧
      (out 11).size < (m 11).size ∧
      ∀ r, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → out r = m r := by
  let mm := execAtoms m halfPrepareOps
  have he := power_prepare_steps m
  have hun (r : ℕ) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) : mm r = m r := by
    simp [mm, he, Function.update_of_ne h13, Function.update_of_ne h14, Function.update_of_ne h15]
  have hmf : mm 11 < 2^(0+(m 11).size+1) := by
    rw [hun 11 (by decide) (by decide) (by decide), Nat.zero_add]
    exact Nat.lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by decide) (by omega))
  have hm7 : mm 7 = 0 := by rw [hun 7 (by decide) (by decide) (by decide), h7]
  obtain ⟨mid,t,l,ht,hb,h13,h14,h15,hupper,hlower,hpres⟩ :=
    halfDoubleLoop_runs mm 0 (m 11).size hmf hm7 (by simp [mm, he])
      (by simp [mm, he]) (by simp [mm, he])
  have he11 : mid 11 = m 11 := (hpres 11 (by decide) (by decide) (by decide)).trans
    (hun 11 (by decide) (by decide) (by decide))
  have he12 : mid 12 = m 12 := (hpres 12 (by decide) (by decide) (by decide)).trans
    (hun 12 (by decide) (by decide) (by decide))
  have hlo : 2^(l+1) ≤ m 11 := by
    rw [← h13, ← he11]
    apply hlower
    simpa [mm, he] using hr
  let out := execAtoms mid halfTakeOps
  have hout := half_take_steps mid
  have hr' : out 11 = m 11 - 2^(l+1) := by simp [out, hout, he11, h13]
  have hq' : out 12 = m 12 + 2^l := by simp [out, hout, he12, h14]
  have hhi : m 11 < 2^(l+1+1) := by rwa [he11] at hupper
  refine ⟨out,3+(t+2),l,.seq (runs_atoms m halfPrepareOps) (.seq ht (runs_atoms mid halfTakeOps)),
    by omega,hr',hq',hlo,hhi,?_,?_⟩
  · have hg : l+1 < (m 11).size := size_ge_of_two_pow_le hlo
    have hsmall : out 11 < 2^(l+1) := by
      rw [hr', Nat.pow_succ] at *
      omega
    exact Nat.lt_of_le_of_lt (size_lt_of_lt_two_pow hsmall) hg
  · intro r h11 h12 h13 h14 h15
    simp only [out,hout,Function.update_of_ne h11,Function.update_of_ne h12]
    rw [hpres r h13 h14 h15, hun r h13 h14 h15]

private theorem halfLoop_runs (F : ℕ) (m : Mem) (hf : (m 11).size ≤ F) (h7 : m 7 = 0)
    (h16 : m 16 = 2) :
    ∃ out t, Runs halfLoop m out t ∧ t ≤ 20*(F+1)^2 ∧
      out 11 = m 11 % 2 ∧ out 12 = m 12 + m 11 / 2 ∧
      ∀ r, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → out r = m r := by
  induction F generalizing m with
  | zero =>
    have hz : m 11 = 0 := Nat.size_eq_zero.mp (by omega)
    have hno : ¬ m 16 ≤ m 11 := by omega
    exact ⟨m,2,.done hno,by decide,by simp [hz],by simp [hz],fun _ _ _ _ _ _ => rfl⟩
  | succ F ih =>
    by_cases he : m 16 ≤ m 11
    · have hr : 2 ≤ m 11 := by simpa [h16] using he
      obtain ⟨mid,b,l,hb,hcb,hmid11,hmid12,hl,hu,hdecrease,hpres⟩ := halfBody_runs m h7 hr
      have hmf : (mid 11).size ≤ F := by omega
      have hm7 : mid 7 = 0 := by rw [hpres 7 (by decide) (by decide) (by decide) (by decide) (by decide), h7]
      have hm16 : mid 16 = 2 := by rw [hpres 16 (by decide) (by decide) (by decide) (by decide) (by decide), h16]
      obtain ⟨out,t,ht,hct,ho1,ho2,hou⟩ := ih mid hmf hm7 hm16
      have heq : m 11 = mid 11 + 2 * 2^l := by rw [hmid11, Nat.pow_succ, Nat.mul_comm 2]; omega
      have hmod : m 11 % 2 = mid 11 % 2 := by rw [heq, Nat.add_mul_mod_self_left]
      have hdiv : m 11 / 2 = mid 11 / 2 + 2^l := by rw [heq, Nat.add_mul_div_left _ _ (by decide)]
      refine ⟨out,2+b+t,.again he hb ht,?_,ho1.trans hmod.symm,?_,?_⟩
      · rw [show (F+1+1)^2=(F+1)^2 + 2*(F+1)+1 by simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add]; omega]
        omega
      · rw [ho2,hmid12,hdiv]
        omega
      · intro r h11 h12 h13 h14 h15
        rw [hou r h11 h12 h13 h14 h15, hpres r h11 h12 h13 h14 h15]
    · have hr : m 11 < 2 := by omega
      exact ⟨m,2,.done he,by
        have h : 1 ≤ (F+1+1)^2 := Nat.pow_pos (by omega)
        omega, (Nat.mod_eq_of_lt hr).symm, by rw [Nat.div_eq_of_lt hr, Nat.add_zero],
        fun _ _ _ _ _ _ => rfl⟩

/-- Compute binary quotient and remainder by two in the RAM's restricted arithmetic instruction
set. The chain is quadratic in the bit length of its operand. -/
theorem halve_runs (m : Mem) (h7 : m 7 = 0) (h16 : m 16 = 2) :
    ∃ out t, Runs halve m out t ∧ t ≤ 20*((m 11).size+1)^2+1 ∧
      out 11 = m 11 % 2 ∧ out 12 = m 11 / 2 ∧
      ∀ r, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → out r = m r := by
  let mid := Function.update m 12 0
  obtain ⟨out,t,hr,hb,ha,hb',hpres⟩ := halfLoop_runs (m 11).size mid
    (by simp [mid]) (by simpa [mid] using h7) (by simpa [mid] using h16)
  refine ⟨out,1+t,.seq (.atom (.const 12 0) m) hr,by omega,?_,?_,?_⟩
  · simpa [mid] using ha
  · simpa [mid] using hb'
  · intro r h11 h12 h13 h14 h15
    rw [hpres r h11 h12 h13 h14 h15]
    exact Function.update_of_ne h12 _ _

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA

open RAMBlock
open Turing.MultiTapeTM

private theorem addressZero_eq (κ j : ℕ) : ramDataAddress κ 0 j = ramDataBase κ + j*(κ+2) := by
  simp [ramDataAddress]

private theorem addr_not_small (κ j : ℕ) {r : ℕ} (hr : r < 32) : ramDataAddress κ 0 j ≠ r := by
  have hd := ramDataAddress_ge κ 0 j
  unfold ramDataBase at hd
  omega

private theorem rawInput_append (xs : List Bool) (b : Bool) (j : ℕ)
    (hj : j ≠ xs.length+1) : ramInputSymbol (xs++[b]) j = ramInputSymbol xs j := by
  by_cases hz : j = 0
  · simp [ramInputSymbol,hz]
  simp only [ramInputSymbol, hz, if_false]
  by_cases hh : j-1 < xs.length
  · rw [List.getElem?_append_left hh]
  · have hu : xs.length ≤ j-1 := by omega
    have hs : 1 ≤ (j-1)-xs.length := by omega
    rw [List.getElem?_append_right hu, List.getElem?_eq_none hu,
      List.getElem?_eq_none (by simpa using hs : [b].length ≤ j-1-xs.length)]

private theorem rawInput_append_last (xs : List Bool) (b : Bool) :
    ramInputSymbol (xs++[b]) (xs.length+1) = 1 + b.toNat := by
  simp [ramInputSymbol]
  cases b <;> rfl

/-- The serializer's stream invariant. Register 9 points at the next input lane cell. -/
structure InputStream (κ : ℕ) (xs : List Bool) (m : Mem) : Prop where
  lengthReg : m 3 = xs.length
  zeroReg : m 7 = 0
  oneReg : m 8 = 1
  addrReg : m 9 = ramDataAddress κ 0 (xs.length + 1)
  strideReg : m 10 = κ+2
  twoReg : m 16 = 2
  cells : ∀ j, m (ramDataAddress κ 0 j) = ramInputSymbol xs j

private theorem InputStream.updateScratch {κ : ℕ} {xs : List Bool} {m : Mem}
    (h : InputStream κ xs m) (r val : ℕ) (hr : r < 32)
    (h3 : r ≠ 3) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h16 : r ≠ 16) :
    InputStream κ xs (Function.update m r val) := by
  exact ⟨by simpa [Function.update_of_ne h3.symm] using h.lengthReg,
    by simpa [Function.update_of_ne h7.symm] using h.zeroReg,
    by simpa [Function.update_of_ne h8.symm] using h.oneReg,
    by simpa [Function.update_of_ne h9.symm] using h.addrReg,
    by simpa [Function.update_of_ne h10.symm] using h.strideReg,
    by simpa [Function.update_of_ne h16.symm] using h.twoReg,
    fun j => by rw [Function.update_of_ne (addr_not_small κ j hr), h.cells]⟩

private theorem InputStream.congr {κ : ℕ} {xs : List Bool} {m out : Mem}
    (h : InputStream κ xs m) (h3 : out 3=m 3) (h7 : out 7=m 7) (h8 : out 8=m 8)
    (h9 : out 9=m 9) (h10 : out 10=m 10) (h16 : out 16=m 16)
    (hc : ∀ j, out (ramDataAddress κ 0 j) = m (ramDataAddress κ 0 j)) : InputStream κ xs out :=
  ⟨h3.trans h.lengthReg, h7.trans h.zeroReg, h8.trans h.oneReg, h9.trans h.addrReg,
    h10.trans h.strideReg, h16.trans h.twoReg, fun j => (hc j).trans (h.cells j)⟩

private def inputEmitOps (r : ℕ) : List Op := [.store 9 r, .add 9 9 10, .add 3 3 8]
private def inputEmit (r : ℕ) : Code := .chain ((inputEmitOps r).map Code.atom)

private def streamWritable (κ r : ℕ) : Prop := r = 3 ∨ (7 ≤ r ∧ r ≤ 19) ∨
  ∃ j, r = ramDataAddress κ 0 j

private def inputPreserved (κ : ℕ) (m out : Mem) : Prop :=
  ∀ r, ¬ streamWritable κ r → out r = m r

private theorem preserveRefl (κ : ℕ) (m : Mem) : inputPreserved κ m m := fun _ _ => rfl
private theorem preserveTrans {κ : ℕ} {a b c : Mem}
    (h₁ : inputPreserved κ a b) (h₂ : inputPreserved κ b c) : inputPreserved κ a c :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

private theorem input_preserve_write {κ : ℕ} (m : Mem) (r x : ℕ) (hr : streamWritable κ r) :
    inputPreserved κ m (Function.update m r x) := by
  intro i hi
  have hne : i ≠ r := by intro he; apply hi; rwa [he]
  exact Function.update_of_ne hne _ _

private theorem input_emit_effect (κ : ℕ) (xs : List Bool) (m : Mem) (r : ℕ)
    (h : InputStream κ xs m) :
    execAtoms m (inputEmitOps r) = Function.update (Function.update
      (Function.update m (m 9) (m r)) 9 (m 9 + m 10)) 3 (m 3+1) := by
  have h9 : ∀ r < 32, r ≠ m 9 := by
    intro z hz
    rw [h.addrReg]
    exact Ne.symm (addr_not_small _ _ hz)
  simp only [execAtoms, inputEmitOps, List.foldl, Op.effect]
  rw [Function.update_of_ne (by decide : 3 ≠ 9), Function.update_of_ne (by decide : 8 ≠ 9),
    Function.update_of_ne (h9 3 (by decide)), Function.update_of_ne (h9 8 (by decide)),
    Function.update_of_ne (h9 9 (by decide)), Function.update_of_ne (h9 10 (by decide)), h.oneReg]

private theorem inputEmit_runs (κ : ℕ) (xs : List Bool) (m : Mem) (r : ℕ) (b : Bool)
    (h : InputStream κ xs m) (hr : m r = 1+b.toNat) :
    ∃ out, Runs (inputEmit r) m out 3 ∧ InputStream κ (xs++[b]) out ∧
      inputPreserved κ m out ∧ ∀ v < 32, v ≠ 3 → v ≠ 9 → out v = m v := by
  let out := execAtoms m (inputEmitOps r)
  have he := input_emit_effect κ xs m r h
  have hun (v : ℕ) (hv : v < 32) (h3 : v ≠ 3) (h9 : v ≠ 9) : out v = m v := by
    simp only [out, he, Function.update_of_ne h3, Function.update_of_ne h9]
    have hs : v ≠ m 9 := by rw [h.addrReg]; exact (addr_not_small _ _ hv).symm
    rw [Function.update_of_ne hs]
  refine ⟨out,runs_atoms m (inputEmitOps r),?_,?_,hun⟩
  · constructor
    · simp [out, he, h.lengthReg]
    · rw [hun 7 (by decide) (by decide) (by decide), h.zeroReg]
    · rw [hun 8 (by decide) (by decide) (by decide), h.oneReg]
    · simp only [out, he, Function.update_of_ne (by decide : 9 ≠ 3), Function.update_self,
        h.addrReg, h.strideReg, List.length_append, List.length_singleton, addressZero_eq, Nat.add_mul, Nat.one_mul]
      omega
    · rw [hun 10 (by decide) (by decide) (by decide), h.strideReg]
    · rw [hun 16 (by decide) (by decide) (by decide), h.twoReg]
    · intro j
      simp only [out, he, Function.update_of_ne (addr_not_small κ j (by decide : 3 < 32)),
        Function.update_of_ne (addr_not_small κ j (by decide : 9 < 32)), h.addrReg, hr]
      by_cases hj : j = xs.length+1
      · subst j; rw [Function.update_self, rawInput_append_last]
      · have hne : ramDataAddress κ 0 j ≠ ramDataAddress κ 0 (xs.length+1) := fun h' =>
          hj ((ramDataAddress_eq_iff (by omega : 0 < κ+2) (by omega : 0 < κ+2)).mp h').2
        rw [Function.update_of_ne hne, h.cells, rawInput_append _ _ _ hj]
  · have haddr : streamWritable κ (m 9) := Or.inr (Or.inr ⟨_,h.addrReg⟩)
    rw [show out = _ from he]
    exact preserveTrans (input_preserve_write _ _ _ haddr)
      (preserveTrans (input_preserve_write _ _ _ (Or.inr (Or.inl (by omega))))
        (input_preserve_write _ _ _ (Or.inl rfl)))

private def prepBit : Code := .add 17 11 8
private def finishBit : Code := .add 11 12 7
private def emitTags (framed : Bool) : Code := if framed then inputEmit 16 else .skip
private def binaryBody (framed : Bool) : Code :=
  .chain [halve, prepBit, emitTags framed, inputEmit 17, finishBit]
private def binaryLoop (framed : Bool) : Code := .whileLE 8 11 (binaryBody framed)

private def bitLabels (framed : Bool) (ws : List Bool) : List Bool :=
  if framed then ws.flatMap (fun b => [true,b]) else ws

private theorem bitLabels_cons (framed b : Bool) (ws : List Bool) :
    bitLabels framed (b::ws) = (if framed then [true,b] else [b]) ++ bitLabels framed ws := by
  cases framed <;> rfl

private theorem binaryBody_runs (κ : ℕ) (framed : Bool) (xs : List Bool) (m : Mem)
    (h : InputStream κ xs m) :
    ∃ out t, Runs (binaryBody framed) m out t ∧ t ≤ 20*((m 11).size+1)^2+9 ∧
      InputStream κ (xs ++ (if framed then [true,(m 11).bodd] else [(m 11).bodd])) out ∧
      out 11 = m 11 /2 ∧ inputPreserved κ m out := by
  obtain ⟨a,u,ha,hu,hr,hq,hkeep⟩ := halve_runs m h.zeroReg h.twoReg
  have hsmall (r : ℕ) (hr : r ≤ 10 ∨ 16 ≤ r) : a r = m r :=
    hkeep r (by omega) (by omega) (by omega) (by omega) (by omega)
  have haStream : InputStream κ xs a := h.congr
    (hsmall 3 (by decide)) (hsmall 7 (by decide)) (hsmall 8 (by decide))
    (hsmall 9 (by decide)) (hsmall 10 (by decide)) (hsmall 16 (by decide))
    (fun j => hsmall _ (Or.inr (by have := ramDataAddress_ge κ 0 j; unfold ramDataBase at this; omega)))
  have pa : inputPreserved κ m a := by
    intro r hnot
    exact hkeep r (by intro he; apply hnot; right; left; omega)
      (by intro he; apply hnot; right; left; omega) (by intro he; apply hnot; right; left; omega)
      (by intro he; apply hnot; right; left; omega) (by intro he; apply hnot; right; left; omega)
  let b := Function.update a 17 (a 11 + a 8)
  have hb : Runs prepBit a b 1 := .atom (.add 17 11 8) a
  have hbStream : InputStream κ xs b := haStream.updateScratch 17 _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have pb : inputPreserved κ a b := input_preserve_write _ _ _ (Or.inr (Or.inl (by decide)))
  have hbitNat : (m 11).bodd.toNat = m 11 % 2 := by
    have he := Nat.bodd_add_div2 (m 11)
    rw [Nat.div2_val] at he
    omega
  have hb17 : b 17 = 1+(m 11).bodd.toNat := by simp [b,hr,haStream.oneReg,hbitNat]; omega
  have hb12 : b 12 = m 11/2 := by simpa [b] using hq
  have htag : ∃ c z, Runs (emitTags framed) b c z ∧ z ≤ 3 ∧
      InputStream κ (xs ++ (if framed then [true] else [])) c ∧
      inputPreserved κ b c ∧ c 12 = b 12 ∧ c 17 = b 17 := by
    cases framed
    · exact ⟨b,0,.skip _,by decide,by simpa using hbStream,preserveRefl _ _,rfl,rfl⟩
    · obtain ⟨c,hc,hcs,pc,huc⟩ := inputEmit_runs κ xs b 16 true hbStream (by simpa using hbStream.twoReg)
      exact ⟨c,3,hc,by decide,hcs,pc,huc 12 (by decide) (by decide) (by decide),
        huc 17 (by decide) (by decide) (by decide)⟩
  obtain ⟨c,z,hc,hz,hcStream,pc,hc12,hc17⟩ := htag
  obtain ⟨d,hd,hdStream,pd,hud⟩ := inputEmit_runs κ _ c 17 (m 11).bodd hcStream (hc17.trans hb17)
  let out := Function.update d 11 (d 12 + d 7)
  have ho : Runs finishBit d out 1 := .atom (.add 11 12 7) d
  have hs : InputStream κ ((xs ++ (if framed then [true] else [])) ++ [(m 11).bodd]) out :=
    hdStream.updateScratch 11 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hwords : (xs ++ (if framed then [true] else [])) ++ [(m 11).bodd] =
      xs ++ (if framed then [true,(m 11).bodd] else [(m 11).bodd]) := by cases framed <;> simp
  rw [hwords] at hs
  have po : inputPreserved κ d out := input_preserve_write _ _ _ (Or.inr (Or.inl (by decide)))
  refine ⟨out,u+(1+(z+(3+(1+0)))),.seq ha (.seq hb (.seq hc (.seq hd (.seq ho (.skip _))))),
    by omega,hs,?_,preserveTrans pa (preserveTrans pb (preserveTrans pc (preserveTrans pd po)))⟩
  simp [out, hud 12 (by decide) (by decide) (by decide), hc12, hb12, hdStream.zeroReg]

private theorem nat_bits_lsb {n : ℕ} (hn : n ≠ 0) : n.bits = n.bodd :: (n/2).bits := by
  have hb := Nat.bit_bodd_div2 n
  have hcond (hz : n.div2 = 0) : n.bodd = true := by
    cases he : n.bodd
    · simp [hz,he] at hb
      exact False.elim (hn hb.symm)
    · rfl
  rw [← Nat.div2_val, ← Nat.bits_append_bit n.div2 n.bodd hcond, hb]

private theorem binaryLoop_runs (κ : ℕ) (framed : Bool) (F : ℕ) (xs : List Bool) (m : Mem)
    (h : InputStream κ xs m) (hf : (m 11).size ≤ F) :
    ∃ out t, Runs (binaryLoop framed) m out t ∧ t ≤ 40*(F+1)^3 ∧
      InputStream κ (xs ++ bitLabels framed (m 11).bits) out ∧ inputPreserved κ m out := by
  induction F generalizing xs m with
  | zero =>
    have h0 : m 11 = 0 := Nat.size_eq_zero.mp (by omega)
    have hne : ¬ m 8 ≤ m 11 := by simp [h.oneReg,h0]
    exact ⟨m,2,.done hne,by decide,by simpa [h0,bitLabels] using h,preserveRefl _ _⟩
  | succ F ih =>
    by_cases h0 : m 11 = 0
    · have hne : ¬ m 8 ≤ m 11 := by simp [h.oneReg,h0]
      exact ⟨m,2,.done hne,by
        have hp : 1 ≤ (F+1+1)^3 := Nat.pow_pos (by omega)
        omega,by simpa [h0,bitLabels] using h,preserveRefl _ _⟩
    · have hyes : m 8 ≤ m 11 := by rw [h.oneReg]; omega
      obtain ⟨mid,a,ha,hba,hs,hq,hpa⟩ := binaryBody_runs κ framed xs m h
      have hb := nat_bits_lsb h0
      have hm : (mid 11).size ≤ F := by
        have he : (m 11).size = (mid 11).size + 1 := by
          rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, hb, hq]; simp
        omega
      obtain ⟨out,b,hbRun,hbb,hout,hpb⟩ := ih _ _ hs hm
      have hs' : InputStream κ (xs ++ bitLabels framed (m 11).bits) out := by
        rw [hb,bitLabels_cons,← List.append_assoc,← hq]
        exact hout
      refine ⟨out,2+a+b,.again hyes ha hbRun,?_,hs',preserveTrans hpa hpb⟩
      have hpa' : ((m 11).size+1)^2 ≤ (F+2)^2 := Nat.pow_le_pow_left (by omega) 2
      have ha' : a ≤ 20*(F+2)^2+9 := by omega
      have hcost : 2+(20*(F+2)^2+9)+40*(F+1)^3 ≤ 40*(F+1+1)^3 := by
        have hf3 : (F+2)^3 = (F+1)^3 + 3*(F+1)^2 + 3*(F+1)+1 := by ring
        have hf2 : (F+2)^2 = (F+1)^2 + 2*(F+1)+1 := by ring
        rw [show F+1+1 = F+2 by omega, hf3, hf2]
        omega
      omega

private def unaryBody : Code := .chain [inputEmit 16,inputEmit 16,.monus 18 18 8]
private def unaryLoop : Code := .whileLE 8 18 unaryBody

private theorem unaryBody_runs (κ : ℕ) (xs : List Bool) (m : Mem)
    (h : InputStream κ xs m) :
    ∃ out, Runs unaryBody m out 7 ∧ InputStream κ (xs ++ [true,true]) out ∧
      out 18 = m 18-1 ∧ inputPreserved κ m out := by
  obtain ⟨a,ha,has,pa,hua⟩ := inputEmit_runs κ xs m 16 true h (by simpa using h.twoReg)
  obtain ⟨b,hb,hbs,pb,hub⟩ := inputEmit_runs κ _ a 16 true has (by simpa using has.twoReg)
  let out := Function.update b 18 (b 18-b 8)
  have ho : Runs (.monus 18 18 8) b out 1 := .atom (.monus 18 18 8) b
  have hout : InputStream κ (xs++[true,true]) out := by
    simpa [List.append_assoc] using (hbs.updateScratch 18 (b 18-b 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have po : inputPreserved κ b out := input_preserve_write _ _ _ (Or.inr (Or.inl (by decide)))
  refine ⟨out,.seq ha (.seq hb (.seq ho (.skip _))),hout,?_,preserveTrans pa (preserveTrans pb po)⟩
  simp [out, hub 18 (by decide) (by decide) (by decide), hua 18 (by decide) (by decide) (by decide), hbs.oneReg]

private theorem unaryLoop_runs (κ f : ℕ) (xs : List Bool) (m : Mem)
    (h : InputStream κ xs m) (hf : m 18 = f) :
    ∃ out, Runs unaryLoop m out (9*f+2) ∧
      InputStream κ (xs ++ bitLabels true (List.replicate f true)) out ∧ inputPreserved κ m out := by
  induction f generalizing m xs with
  | zero =>
    have hn : ¬ m 8 ≤ m 18 := by simp [h.oneReg,hf]
    exact ⟨m,.done hn,by simpa [bitLabels] using h,preserveRefl _ _⟩
  | succ f ih =>
    have hy : m 8 ≤ m 18 := by simp [h.oneReg,hf]
    obtain ⟨mid,ht,hm,hf',hp⟩ := unaryBody_runs κ xs m h
    have hm18 : mid 18 = f := by rw [hf',hf]; omega
    obtain ⟨out,hu,ho,hpres⟩ := ih _ _ hm hm18
    refine ⟨out,?_,?_,preserveTrans hp hpres⟩
    · rw [show 9*(f+1)+2=2+7+(9*f+2) by omega]
      exact .again hy ht hu
    · rw [List.replicate_succ,bitLabels_cons,← List.append_assoc]
      exact ho

private theorem bitLabels_frame (ws : List Bool) : bitLabels true ws ++ [false] = frame ws := rfl

private def inputInitOps (κ : ℕ) : List Op :=
  [.const 3 0, .const 7 0, .const 8 1, .const 9 (ramDataAddress κ 0 1), .const 10 (κ+2),
    .const 16 2, .add 18 0 7]

private theorem init_effect (κ n k v : ℕ) :
    InputStream κ [] (execAtoms (memOf [n,k,v]) (inputInitOps κ)) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro j
    have hlarge : 32 ≤ ramDataAddress κ 0 j := by
      have := ramDataAddress_ge κ 0 j
      unfold ramDataBase at this
      omega
    simp only [execAtoms,inputInitOps,List.foldl,Op.effect]
    repeat rw [Function.update_of_ne (by omega)]
    have hq : [n,k,v].length ≤ ramDataAddress κ 0 j := by simp; omega
    simp [ramInputSymbol,ramSymbol,memOf,List.getD_eq_getElem?_getD,List.getElem?_eq_none hq]

private theorem init_preserves (κ n k v : ℕ) :
    inputPreserved κ (memOf [n,k,v]) (execAtoms (memOf [n,k,v]) (inputInitOps κ)) := by
  have h3 : streamWritable κ 3 := Or.inl rfl
  have hr (r : ℕ) (hi : 7 ≤ r ∧ r ≤ 19) : streamWritable κ r := Or.inr (Or.inl hi)
  change inputPreserved κ _ (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (memOf [n,k,v]) 3 0) 7 0) 8 1)
      9 (ramDataAddress κ 0 1)) 10 (κ+2)) 16 2) 18 _)
  exact preserveTrans (input_preserve_write _ _ _ h3)
    (preserveTrans (input_preserve_write _ _ _ (hr 7 (by decide)))
    (preserveTrans (input_preserve_write _ _ _ (hr 8 (by decide)))
    (preserveTrans (input_preserve_write _ _ _ (hr 9 (by decide)))
    (preserveTrans (input_preserve_write _ _ _ (hr 10 (by decide)))
    (preserveTrans (input_preserve_write _ _ _ (hr 16 (by decide)))
      (input_preserve_write _ _ _ (hr 18 (by decide))))))))

private theorem copyInput_runs (κ : ℕ) (xs : List Bool) (m : Mem) (r : ℕ)
    (h : InputStream κ xs m) :
    ∃ out, Runs (.add 11 r 7) m out 1 ∧ InputStream κ xs out ∧
      out 11 = m r ∧ inputPreserved κ m out := by
  let out := Function.update m 11 (m r + m 7)
  exact ⟨out,.atom (.add 11 r 7) m,h.updateScratch 11 _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide),by simp [out,h.zeroReg],
    input_preserve_write _ _ _ (Or.inr (Or.inl (by decide)))⟩

/-- Serialize `[n,k,v]` into the exact native machine input lane. -/
def ramWidthInput (κ : ℕ) : Code :=
  .chain [.chain ((inputInitOps κ).map Code.atom),unaryLoop,inputEmit 8,
    .add 11 1 7,binaryLoop true,inputEmit 8,.add 11 2 7,binaryLoop false]

private theorem widthUnaryTriple_bits' (n k v : ℕ) :
    encPair encUnary (encPair encNat encNat) (n,k,v) =
      frame (List.replicate n true) ++ frame k.bits ++ v.bits := by
  simp [List.append_assoc]

private theorem memOf3_zero {n k v r : ℕ} (hr : 3 ≤ r) : memOf [n,k,v] r = 0 := by
  rw [memOf,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa using hr : [n,k,v].length ≤ r)]
  rfl

/-- Verified unit execution and memory layout for the exact unary/binary input encoding. -/
theorem ramWidthInput_runs (κ n k v : ℕ) (hk : k ≤ n) (hv : v < 2^n) :
    let input := encPair encUnary (encPair encNat encNat) (n,k,v)
    ∃ out t, Runs (ramWidthInput κ) (memOf [n,k,v]) out t ∧ t ≤ 110*(n+1)^3 ∧
      InputStream κ input out ∧ (∀ r ≤ 2, out r = memOf [n,k,v] r) ∧
      (∀ r, 4 ≤ r → r ≤ 6 → out r = 0) ∧
      (∀ r, 32 ≤ r → r < ramDataBase κ → out r = 0) ∧
      ∀ l j, 0 < l → l < κ+2 → out (ramDataAddress κ l j) = 0 := by
  let start := memOf [n,k,v]
  let a := execAtoms start (inputInitOps κ)
  have ha := runs_atoms start (inputInitOps κ)
  have hpa := init_preserves κ n k v
  have haq : a 18 = n := rfl
  obtain ⟨b,hb,hbs,hpb⟩ := unaryLoop_runs κ n [] a (init_effect κ n k v) haq
  obtain ⟨c,hc,hcs,hpc,_⟩ := inputEmit_runs κ _ b 8 false hbs (by simpa using hbs.oneReg)
  have hcs' : InputStream κ (frame (List.replicate n true)) c := by
    simpa only [List.nil_append,bitLabels_frame] using hcs
  obtain ⟨d,hd,hds,hd11,hpd⟩ := copyInput_runs κ _ c 1 hcs'
  have hpd' := preserveTrans hpa (preserveTrans hpb (preserveTrans hpc hpd))
  have hd11' : d 11 = k := by
    rw [hd11,(preserveTrans hpa (preserveTrans hpb hpc)) 1]
    · rfl
    · simp [streamWritable]
      intro j
      have := addr_not_small κ j (by decide : 1 < 32)
      exact this.symm
  have hks : k.size ≤ n := Nat.size_le.mpr (hk.trans_lt (Nat.lt_two_pow_self (n := n)))
  obtain ⟨e,t,he,ht,hes,hpe⟩ := binaryLoop_runs κ true n _ d hds (by rwa [hd11'])
  rw [hd11'] at hes
  obtain ⟨f,hf,hfs,hpf,_⟩ := inputEmit_runs κ _ e 8 false hes (by simpa using hes.oneReg)
  have hfs' : InputStream κ (frame (List.replicate n true) ++ frame k.bits) f := by
    simpa only [List.append_assoc,bitLabels_frame] using hfs
  obtain ⟨g,hg,hgs,hg11,hpg⟩ := copyInput_runs κ _ f 2 hfs'
  have presG := preserveTrans hpd' (preserveTrans hpe (preserveTrans hpf hpg))
  have hg11' : g 11 = v := by
    rw [hg11,(preserveTrans hpd' (preserveTrans hpe hpf)) 2]
    · rfl
    · simp [streamWritable]
      intro j
      have := addr_not_small κ j (by decide : 2 < 32)
      exact this.symm
  have hvs : v.size ≤ n := Nat.size_le.mpr hv
  obtain ⟨out,u,hu,hub,hus,hpu⟩ := binaryLoop_runs κ false n _ g hgs (by rwa [hg11'])
  rw [hg11'] at hus
  have hrun : Runs (ramWidthInput κ) start out (7+((9*n+2)+(3+(1+(t+(3+(1+(u+0)))))))) :=
    .seq ha (.seq hb (.seq hc (.seq hd (.seq he (.seq hf (.seq hg (.seq hu (.skip _))))))))
  have pres := preserveTrans presG hpu
  refine ⟨out,_,hrun,?_,?_,?_,?_,?_,?_⟩
  · have hpoly : 9*n+17 ≤ 30*(n+1)^3 := by
      have hp : n+1 ≤ (n+1)^3 := by simpa using Nat.pow_le_pow_right (show 0 < n+1 by omega) (show 1 ≤ 3 by decide)
      omega
    omega
  · rw [widthUnaryTriple_bits']
    exact hus
  · intro r hr
    apply pres
    rintro (h|h|⟨j,h⟩) <;> try omega
    exact (addr_not_small _ _ (by omega : r < 32)) h.symm
  · intro r hl hu'
    rw [pres r,memOf3_zero (by omega)]
    rintro (h|h|⟨j,h⟩) <;> try omega
    exact (addr_not_small _ _ (by omega : r < 32)) h.symm
  · intro r hl hu'
    rw [pres r,memOf3_zero (by omega)]
    rintro (h|h|⟨j,h⟩) <;> try omega
    have := ramDataAddress_ge κ 0 j
    omega
  · intro l j hl hlu
    have haddr := ramDataAddress_ge κ l j
    have hBase : 32 ≤ ramDataBase κ := by unfold ramDataBase; omega
    rw [pres _,memOf3_zero (by omega)]
    rintro (h|h|⟨z,h⟩) <;> try omega
    have hli := (ramDataAddress_eq_iff hlu (by omega : 0 < κ+2)).mp h
    omega

end TimeSpaceMA

namespace TimeSpaceMA

open RAMBlock Turing.MultiTapeTM

/-- Serialize input and initialize the read head and finite source control. -/
def ramWidthInputInit (κ : ℕ) {Q : Type} {q : ℕ} (ids : Q ≃ Fin q) (start : Q) : Code :=
  .seq (ramWidthInput κ) (.chain [.const 4 1,.const 6 (ramStateCode ids (some start))])

/-- The native initial configuration is represented exactly by the RAM serializer's output. -/
theorem ramWidthInputInit_runs (κ n k v : ℕ) (hk : k ≤ n) (hv : v < 2^n)
    {Q : Type} {q : ℕ} (ids : Q ≃ Fin q) (start : Q) :
    let input := encPair encUnary (encPair encNat encNat) (n,k,v)
    ∃ out t, Runs (ramWidthInputInit κ ids start) (memOf [n,k,v]) out t ∧ t ≤ 112*(n+1)^3 ∧
      RAMMiddleRep ids (Turing.Cfg.init (k := κ) start input) out := by
  obtain ⟨mid,t,hm,ht,hs,_,hz,hwork,hlane⟩ := ramWidthInput_runs κ n k v hk hv
  let m := Function.update mid 4 1
  let out := Function.update m 6 (ramStateCode ids (some start))
  have hu : Runs (.const 4 1) mid m 1 := .atom (.const 4 1) mid
  have ho : Runs (.const 6 (ramStateCode ids (some start))) m out 1 := .atom (.const 6 _) m
  have he (r : ℕ) (h4 : r ≠ 4) (h6 : r ≠ 6) : out r = mid r := by
    simp [out,m,Function.update_of_ne h4,Function.update_of_ne h6]
  have hb : 32 ≤ ramDataBase κ := by unfold ramDataBase; omega
  have ha (l j : ℕ) : out (ramDataAddress κ l j) = mid (ramDataAddress κ l j) := by
    have := ramDataAddress_ge κ l j
    exact he _ (by omega) (by omega)
  have hside (i : Fin κ) : out (workSide i) = 0 := by
    have hg : 32 ≤ workSide i := by unfold workSide; omega
    exact (he _ (by omega) (by omega)).trans (hwork _ hg (workSide_lt_base i))
  have hmag (i : Fin κ) : out (workMag i) = 0 := by
    have hg : 32 ≤ workMag i := by unfold workMag workSide; omega
    exact (he _ (by omega) (by omega)).trans (hwork _ hg (workMag_lt_base i))
  refine ⟨out,t+(1+(1+0)),.seq hm (.seq hu (.seq ho (.skip _))),?_,?_⟩
  · have hp : 1 ≤ (n+1)^3 := Nat.pow_pos (by omega)
    omega
  constructor
  · rw [he 3 (by decide) (by decide), hs.lengthReg]
  · simp [out,m]
  · rw [he 5 (by decide) (by decide), hz 5 (by decide) (by decide)]
    rfl
  · rfl
  · rw [he 7 (by decide) (by decide), hs.zeroReg]
  · rw [he 8 (by decide) (by decide), hs.oneReg]
  · intro j
    rw [ha, hs.cells]
  · intro j
    rw [ha, hlane 1 j (by decide) (by omega)]
    rfl
  · intro i
    rw [hside]
    omega
  · intro i
    rw [hside,hmag]
    rfl
  · intro i j
    rw [ha, hlane (i.val+2) (ramTapeIndex j) (by omega)
      (by have := i.isLt; omega)]
    rfl

end TimeSpaceMA

namespace TimeSpaceMA.RAMMiddle

open RAMBlock

/-- Claimed register frame before decoding the native output words. -/
def decoderInitAtoms (k : ℕ) : List Op :=
  let first := ramDataBase k+1
  let d := k+2
  [.const 8 1, .const 12 first, .const 13 d, .const 14 first, .const 15 0,
    .const 19 2, .const 20 (first-d)]

def decoderInit (k : ℕ) : Code :=
  .seq (Code.chain ((decoderInitAtoms k).map Code.atom))
    (.seq (addRepeated 20 5 (k+2))
      (.seq (.add 14 20 13) (.monus 11 14 7)))

/-- Prepare the decoder's registered addresses and constants, preserving the raw output lane.
The buffer for decoded integers starts at the first cell past the raw stream. -/
theorem decoderInit_runs (k : ℕ) (output : List Bool) (m : Mem)
    (hlen : m 5 = output.length) (h0 : m 7 = 0) :
    ∃ v t, Runs (decoderInit k) m v t ∧ t = k+11 ∧
      v 12 = ramDataBase k+1 ∧ v 13 = k+2 ∧
      v 14 = ramDataBase k+1 + output.length*(k+2) ∧
      v 11 = ramDataBase k+1 + output.length*(k+2) ∧
      v 15 = 0 ∧ v 19 = 2 ∧ v 8 = 1 ∧
      v 20 = ramDataBase k+1 + output.length*(k+2) - (k+2) ∧
      ∀ r, ramDataBase k+1 ≤ r → v r = m r := by
  let w := execAtoms m (decoderInitAtoms k)
  let z := Function.update w 20 (w 20+(k+2)*w 5)
  let x := Function.update z 14 (z 20+z 13)
  let v := Function.update x 11 (x 14-x 7)
  have hwWidth : w 5 = output.length := by simp [w,execAtoms,decoderInitAtoms,Op.effect,hlen]
  have hwClock : w 20 = ramDataBase k+1-(k+2) := by simp [w,execAtoms,decoderInitAtoms,Op.effect]
  have hwStride : w 13 = k+2 := by simp [w,execAtoms,decoderInitAtoms,Op.effect]
  have hxZero : x 7 = 0 := by simp [x,z,w,execAtoms,decoderInitAtoms,Op.effect,h0]
  have hx : x 14 = ramDataBase k+1 + output.length*(k+2) := by
    simp only [x,z,Function.update_self,Function.update_of_ne (by decide : 13 ≠ 20),
      hwClock,hwWidth,hwStride,Nat.mul_comm (k+2)]
    have hd : k+2 ≤ ramDataBase k+1 := by unfold ramDataBase; omega
    omega
  refine ⟨v,(decoderInitAtoms k).length+((k+2)+(1+1)),
    .seq (runs_atoms m _) (.seq (runs_addRepeated w (by decide) _) (.seq (.atom _ _) (.atom _ _))),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [decoderInitAtoms]; omega
  · simp [v,x,z,w,execAtoms,decoderInitAtoms,Op.effect]
  · simp [v,x,z,hwStride]
  · simpa only [v,Function.update_of_ne (by decide : 14 ≠ 11)] using hx
  · simp [v,hx,hxZero]
  · simp [v,x,z,w,execAtoms,decoderInitAtoms,Op.effect]
  · simp [v,x,z,w,execAtoms,decoderInitAtoms,Op.effect]
  · simp [v,x,z,w,execAtoms,decoderInitAtoms,Op.effect]
  · simp only [v,x,z,Function.update_of_ne (by decide : 20 ≠ 11),
      Function.update_of_ne (by decide : 20 ≠ 14),Function.update_self,hwClock,hwWidth,
      Nat.mul_comm (k+2)]
    have hd : k+2 ≤ ramDataBase k+1 := by unfold ramDataBase; omega
    omega
  · intro r hr
    have hr' : 32 < r := by unfold ramDataBase at hr; omega
    have h8 : r ≠ 8 := by omega
    have h11 : r ≠ 11 := by omega
    have h12 : r ≠ 12 := by omega
    have h13 : r ≠ 13 := by omega
    have h14 : r ≠ 14 := by omega
    have h15 : r ≠ 15 := by omega
    have h19 : r ≠ 19 := by omega
    have h20 : r ≠ 20 := by omega
    simp [v,x,z,w,execAtoms,decoderInitAtoms,Op.effect,h8,h11,h12,h13,h14,h15,h19,h20]

end TimeSpaceMA.RAMMiddle

namespace TimeSpaceMA.RAMBlock

open Turing.MultiTapeTM

/-- The framed output of the source machine is read at a physical RAM address. -/
private def outAdvance : Code := .add 12 12 13

private def outBit : Code := Code.chain [
  outAdvance, .load 18 12,
  .ifLE 18 8 .skip (.add 16 16 17),
  .add 17 17 17, outAdvance, .load 18 12
]

private def outFrame : Code := Code.chain [
  .const 16 0, .const 17 1, .load 18 12, .whileLE 19 18 outBit, outAdvance
]

/-- Decode a framed LSB word into registers, retaining the following data. -/
private def ofBitsCarry (a p : ℕ) (word : List Bool) : ℕ :=
  a + p * ofBits word

private theorem ofBits_cons (b : Bool) (w : List Bool) :
    ofBits (b::w) = 2 * ofBits w + b.toNat := by
  change Nat.bit b (ofBits w) = _
  rw [Nat.bit_val]

/-- The output stream at a cursor uses the fixed lane stride. -/
private def MatchStream (m : Mem) (start stride : ℕ) (w : List Bool) : Prop :=
  ∀ i : Fin w.length,
    m (start+i.val*stride) = ramSymbol (some w[i])

private theorem MatchStream.head {m : Mem} {s d : ℕ} {b : Bool} {w : List Bool}
    (h : MatchStream m s d (b::w)) : m s = ramSymbol (some b) := by
  simpa using h ⟨0, by simp⟩

private theorem MatchStream.tail {m : Mem} {s d : ℕ} {b : Bool} {w : List Bool}
    (h : MatchStream m s d (b::w)) : MatchStream m (s+d) d w := by
  intro i
  simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h ⟨i.val+1, by simpa using i.isLt⟩

private theorem MatchStream.update {m : Mem} {s d r v : ℕ} {w : List Bool}
    (h : MatchStream m s d w) (hr : r < s) : MatchStream (Function.update m r v) s d w := by
  intro i
  rw [Function.update_of_ne (show s+i.val*d ≠ r by omega)]
  exact h i

private def frameFinal (m : Mem) (next value power : ℕ) : Mem :=
  Function.update (Function.update (Function.update (Function.update m 12 next)
    16 value) 17 power) 18 1

private def bitFinal (m : Mem) (next value power symbol : ℕ) : Mem :=
  Function.update (Function.update (Function.update (Function.update m 12 next)
    16 value) 17 power) 18 symbol

private theorem outBit_runs (m : Mem) (b : Bool) (s d : ℕ) (w rest : List Bool)
    (hs : 19 < s) (hptr : m 12 = s) (hd : m 13 = d) (hone : m 8 = 1)
    (h : MatchStream m s d (true :: b :: (frame w ++ rest))) :
    ∃ t ≤ 9, Runs outBit m
      (bitFinal m (s+2*d) (m 16 + m 17*b.toNat) (2*m 17)
        (if w.isEmpty then 1 else 2)) t := by
  have hb : m (s+d) = ramSymbol (some b) := h.tail.head
  have hc : m (s+d+d) = if w.isEmpty then 1 else 2 := by
    cases w with
    | nil =>
      have hz : m (s+d+d) = ramSymbol (some false) :=
        MatchStream.head (show MatchStream m (s+d+d) (m 13) (false::rest) by
          rw [hd]; exact h.tail.tail)
      simpa [ramSymbol] using hz
    | cons c w =>
      have hz : m (s+d+d) = ramSymbol (some true) :=
        MatchStream.head (show MatchStream m (s+d+d) d (true::c::(frame w++rest)) from h.tail.tail)
      simpa [ramSymbol] using hz
  let m₁ := Op.effect (.add 12 12 13) m
  let m₂ := Op.effect (.load 18 12) m₁
  let m₃ := if b then Function.update m₂ 16 (m₂ 16 + m₂ 17) else m₂
  let m₄ := Op.effect (.add 17 17 17) m₃
  let m₅ := Op.effect (.add 12 12 13) m₄
  have set2 : m₂ 18 = ramSymbol (some b) := by
    simpa [m₂, m₁, Op.effect, hptr, hd, Function.update_of_ne (show s+d ≠ 12 by omega)] using hb
  have m2one : m₂ 8 = 1 := by simp [m₂, m₁, Op.effect, hone]
  obtain ⟨t, ht, htRun⟩ : ∃ t ≤ 3, Runs (.ifLE 18 8 .skip (.add 16 16 17)) m₂ m₃ t := by
    cases b with
    | false =>
      exact ⟨1, by decide, Runs.yes (by simp [set2, m2one, ramSymbol]) (.skip _)⟩
    | true =>
      exact ⟨3, by decide, Runs.no (by simp [set2, m2one, ramSymbol]) (.atom _ _)⟩
  refine ⟨5+t, by omega, ?_⟩
  have hfinal : Op.effect (.load 18 12) m₅ =
      bitFinal m (s+2*d) (m 16 + m 17*b.toNat) (2*m 17)
        (if w.isEmpty then 1 else 2) := by
    funext a
    have hss : s+d+d ≠ 12 ∧ s+d+d ≠ 16 ∧ s+d+d ≠ 17 ∧ s+d+d ≠ 18 := by omega
    cases b <;> simp only [m₅, m₄, m₃, m₂, m₁, Op.effect, Bool.false_eq_true, if_false,
      if_true, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
      bitFinal, Function.update_self, Function.update_of_ne (by decide : (13:ℕ) ≠ 12),
      Function.update_of_ne (by decide : (12:ℕ) ≠ 17), Function.update_of_ne (by decide : (12:ℕ) ≠ 16),
      Function.update_of_ne (by decide : (12:ℕ) ≠ 18), Function.update_of_ne (by decide : (13:ℕ) ≠ 18),
      Function.update_of_ne (by decide : (13:ℕ) ≠ 16), Function.update_of_ne (by decide : (13:ℕ) ≠ 17),
      Function.update_of_ne (by decide : (17:ℕ) ≠ 12), Function.update_of_ne (by decide : (17:ℕ) ≠ 18),
      Function.update_of_ne (by decide : (17:ℕ) ≠ 16), Function.update_of_ne (by decide : (16:ℕ) ≠ 12),
      Function.update_of_ne (by decide : (16:ℕ) ≠ 18), hptr, hd, hss.1, hss.2.1, hss.2.2.1, hss.2.2.2, hc,
      show s+2*d = s+d+d by omega, two_mul, Function.update_apply] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all [Nat.add_assoc]
  rw [← hfinal]
  have ht' : Runs outBit m (Op.effect (.load 18 12) m₅) (1+(1+(t+(1+(1+(1+0)))))) := by
    exact .seq (.atom _ _) (.seq (.atom _ _) (.seq htRun (.seq (.atom _ _) (.seq (.atom _ _)
      (.seq (.atom _ _) (.skip _))))))
  convert ht' using 1 <;> omega

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA.RAMBlock

open Turing.MultiTapeTM

private def exceptFrame (a : ℕ) : Prop := a = 12 ∨ a = 16 ∨ a = 17 ∨ a = 18

private theorem bitFinal_read (m : Mem) (s a p c r : ℕ) (hr : ¬exceptFrame r) :
    bitFinal m s a p c r = m r := by
  simp [bitFinal, Function.update_apply, exceptFrame] at hr ⊢
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

private theorem outFrameLoop_runs (m : Mem) (w rest : List Bool) (s d : ℕ)
    (hs : 19 < s) (hptr : m 12 = s) (hd : m 13 = d)
    (hone : m 8 = 1) (htwo : m 19 = 2)
    (head : m 18 = if w.isEmpty then 1 else 2)
    (h : MatchStream m s d (frame w ++ rest)) :
    ∃ t ≤ 11*w.length+2, Runs (.whileLE 19 18 outBit) m
      (bitFinal m (s+(2*w.length)*d) (ofBitsCarry (m 16) (m 17) w)
        (2^w.length*m 17) 1) t := by
  induction w generalizing m s with
  | nil =>
    have h18 : m 18 = 1 := head
    have eq : bitFinal m s (m 16) (m 17) 1 = m := by
      rw [← hptr, ← h18]
      simp [bitFinal, Function.update_eq_self]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_mul, Nat.add_zero,
      ofBitsCarry, ofBits, List.foldr_nil, pow_zero, Nat.one_mul, eq]
    exact ⟨2, le_rfl, .done (by omega)⟩
  | cons b w ih =>
    let m' := bitFinal m (s+2*d) (m 16+m 17*b.toNat) (2*m 17) (if w.isEmpty then 1 else 2)
    obtain ⟨u,hu,hr⟩ := outBit_runs m b s d w rest hs hptr hd hone
      (show MatchStream m s d (true::b::(frame w++rest)) from h)
    have hstream : MatchStream m' (s+2*d) d (frame w ++ rest) := by
      intro i
      rw [show m' (s+2*d+i.val*d) = m (s+2*d+i.val*d) from
        bitFinal_read m _ _ _ _ _ (by unfold exceptFrame; omega)]
      have hi := MatchStream.tail (MatchStream.tail
        (show MatchStream m s d (true::b::(frame w++rest)) from h)) i
      simpa only [show s+2*d = s+d+d by omega] using hi
    have h12 : m' 12 = s+2*d := by simp [m',bitFinal]
    have h13 : m' 13 = d := by simpa [m',bitFinal] using hd
    have h8 : m' 8 = 1 := by simpa [m',bitFinal] using hone
    have h19 : m' 19 = 2 := by simpa [m',bitFinal] using htwo
    have h18 : m' 18 = if w.isEmpty then 1 else 2 := by simp [m',bitFinal]
    obtain ⟨v,hv,hr'⟩ := ih m' (s+2*d) (by omega) h12 h13 h8 h19 h18 hstream
    have hj : m 19 ≤ m 18 := by simp [htwo, head]
    have ha : s+2*d+2*w.length*d = s+(2*(b::w).length)*d := by simp; ring
    have hb : ofBitsCarry (m' 16) (m' 17) w = ofBitsCarry (m 16) (m 17) (b::w) := by
      simp [m', bitFinal, ofBitsCarry, ofBits_cons]
      ring
    have hc : 2^w.length*m' 17 = 2^(b::w).length*m 17 := by
      simp [m',bitFinal,pow_succ]
      ring
    have he : bitFinal m' (s+2*d+2*w.length*d) (ofBitsCarry (m' 16) (m' 17) w)
        (2^w.length*m' 17) 1 =
      bitFinal m (s+(2*(b::w).length)*d) (ofBitsCarry (m 16) (m 17) (b::w))
        (2^(b::w).length*m 17) 1 := by
      rw [ha,hb,hc]
      funext a
      simp [m', bitFinal, Function.update_apply]
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all
    refine ⟨2+u+v, by simp; omega, ?_⟩
    rw [← he]
    exact .again hj hr hr'

private theorem outFrame_runs (m : Mem) (w rest : List Bool) (s d : ℕ)
    (hs : 19 < s) (hptr : m 12 = s) (hd : m 13 = d)
    (hone : m 8 = 1) (htwo : m 19 = 2) (h : MatchStream m s d (frame w ++ rest)) :
    ∃ t ≤ 11*w.length+6, Runs outFrame m (frameFinal m (s+(frame w).length*d)
      (ofBits w) (2^w.length)) t := by
  let m₁ := Op.effect (.const 16 0) m
  let m₂ := Op.effect (.const 17 1) m₁
  let m₃ := Op.effect (.load 18 12) m₂
  have hm18 : m₃ 18 = if w.isEmpty then 1 else 2 := by
    have he : m₃ 18 = m s := by
      dsimp [m₃,m₂,m₁,Op.effect]
      rw [Function.update_self]
      simpa [hptr, Function.update_of_ne (show s ≠ 16 by omega),
        Function.update_of_ne (show s ≠ 17 by omega)]
    rw [he]
    cases w with
    | nil => exact (MatchStream.head (show MatchStream m s d (false::rest) from h))
    | cons b w => exact (MatchStream.head (show MatchStream m s d (true::b::(frame w++rest)) from h))
  have hmatch : MatchStream m₃ s d (frame w ++ rest) :=
    ((h.update (r := 16) (v := 0) (by omega)).update (r := 17) (v := 1) (by omega)).update (by omega)
  obtain ⟨u,hu,hr⟩ := outFrameLoop_runs m₃ w rest s d hs
    (by simp [m₃,m₂,m₁,Op.effect,hptr]) (by simp [m₃,m₂,m₁,Op.effect,hd])
    (by simp [m₃,m₂,m₁,Op.effect,hone]) (by simp [m₃,m₂,m₁,Op.effect,htwo]) hm18 hmatch
  let z := bitFinal m₃ (s+(2*w.length)*d) (ofBitsCarry (m₃ 16) (m₃ 17) w) (2^w.length*m₃ 17) 1
  have he : Op.effect (.add 12 12 13) z = frameFinal m (s+(frame w).length*d)
      (ofBits w) (2^w.length) := by
    have hep : s + 2*w.length*d + d = s+(frame w).length*d := by rw [length_frame]; ring
    funext a
    simp [z,bitFinal,frameFinal,m₃,m₂,m₁,Op.effect,ofBitsCarry,hd,hep,Function.update_apply]
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all
  refine ⟨3+u+1, by omega, ?_⟩
  rw [← he]
  convert (show Runs outFrame m (Op.effect (.add 12 12 13) z) (1+(1+(1+(u+(1+0))))) from
    .seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq hr (.seq (.atom _ _) (.skip _)))))) using 1 <;> omega

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA.RAMBlock

open Turing.MultiTapeTM

private def saveDecoded : Code := Code.chain [.store 14 16, .add 14 14 13, .add 15 15 8]

private def decodeOne : Code := .seq outFrame saveDecoded

private def decoderLoop : Code := .whileLE 12 20 decodeOne

private def decodedState (m : Mem) (next dst count value power addr : ℕ) : Mem :=
  Function.update (Function.update
    (Function.update (frameFinal m next value power) addr value) 14 dst) 15 count

private theorem decodedState_preserves {m : Mem} {next dst count value power addr r : ℕ}
    (hr : 20 < r) (h : r ≠ addr) :
    decodedState m next dst count value power addr r = m r := by
  simp [decodedState, frameFinal, Function.update_of_ne h,
    show r ≠ 12 by omega, show r ≠ 14 by omega, show r ≠ 15 by omega,
    show r ≠ 16 by omega, show r ≠ 17 by omega, show r ≠ 18 by omega]

private theorem decodedState_reads {m : Mem} {next dst count value power addr : ℕ}
    (ha : 20 < addr) :
    (decodedState m next dst count value power addr) 12 = next ∧
    (decodedState m next dst count value power addr) 14 = dst ∧
    (decodedState m next dst count value power addr) 15 = count ∧
    (decodedState m next dst count value power addr) 8 = m 8 ∧
    (decodedState m next dst count value power addr) 13 = m 13 ∧
    (decodedState m next dst count value power addr) 19 = m 19 ∧
    (decodedState m next dst count value power addr) 20 = m 20 ∧
    (decodedState m next dst count value power addr) 11 = m 11 ∧
    (decodedState m next dst count value power addr) addr = value := by
  have n12 : (12:ℕ) ≠ addr := by omega
  have n11 : (11:ℕ) ≠ addr := by omega
  have n8 : (8:ℕ) ≠ addr := by omega
  have n13 : (13:ℕ) ≠ addr := by omega
  have n19 : (19:ℕ) ≠ addr := by omega
  have n20 : (20:ℕ) ≠ addr := by omega
  have na14 : addr ≠ 14 := by omega
  have na15 : addr ≠ 15 := by omega
  simp [decodedState, frameFinal, n12, n11, n8, n13, n19, n20, na14, na15]

private theorem ofBits_bits (x : ℕ) : ofBits x.bits = x := by
  induction x using Nat.binaryRec with
  | zero => rfl
  | bit b n ih =>
    by_cases h : n=0 ∧ b=false
    · obtain ⟨rfl,rfl⟩ := h; rfl
    · rw [Nat.bits_append_bit _ _ (by intro hn; by_contra hb; exact h ⟨hn, by simpa using hb⟩),
        ofBits_cons, ih, Nat.bit_val]

private theorem decodeOne_runs (m : Mem) (value : ℕ) (rest : List Bool) (s dst d : ℕ)
    (hs : 20 < s) (hD : 20 < dst)
    (hptr : m 12 = s) (hd : m 13 = d) (hto : m 14 = dst) (htwo : m 19 = 2)
    (hone : m 8 = 1) (h : MatchStream m s d (frame value.bits ++ rest)) :
    ∃ t ≤ 11*value.bits.length+9, Runs decodeOne m
      (decodedState m (s+(frame value.bits).length*d) (dst+d) (m 15+1)
        value (2^value.bits.length) dst) t := by
  obtain ⟨u,hu,hr⟩ := outFrame_runs m value.bits rest s d (by omega) hptr hd hone htwo h
  rw [ofBits_bits] at hr
  let v := frameFinal m (s+(frame value.bits).length*d) value (2^value.bits.length)
  let w := Op.effect (.store 14 16) v
  let z := Op.effect (.add 14 14 13) w
  have hv14 : v 14 = dst := by simp [v,frameFinal,hto]
  have hv16 : v 16 = value := by simp [v,frameFinal]
  have hw14 : w 14 = dst := by
    change (Function.update v (v 14) (v 16)) 14 = dst
    rw [hv14, hv16, Function.update_of_ne (by omega : (14:ℕ) ≠ dst), hv14]
  have hw13 : w 13 = d := by
    change (Function.update v (v 14) (v 16)) 13 = d
    rw [hv14, hv16, Function.update_of_ne (by omega : (13:ℕ) ≠ dst)]
    simp [v,frameFinal,hd]
  have hz15 : z 15 = m 15 := by
    change (Function.update (Function.update v (v 14) (v 16)) 14 (w 14 + w 13)) 15 = m 15
    rw [hv14, hv16, Function.update_of_ne (by decide : (15:ℕ) ≠ 14), Function.update_of_ne (by omega : (15:ℕ) ≠ dst)]
    simp [v,frameFinal]
  have hz8 : z 8 = 1 := by
    change (Function.update (Function.update v (v 14) (v 16)) 14 (w 14 + w 13)) 8 = 1
    rw [hv14, hv16, Function.update_of_ne (by decide : (8:ℕ) ≠ 14), Function.update_of_ne (by omega : (8:ℕ) ≠ dst)]
    simp [v,frameFinal,hone]
  have he : Op.effect (.add 15 15 8) z =
      decodedState m (s+(frame value.bits).length*d) (dst+d) (m 15+1)
        value (2^value.bits.length) dst := by
    change Function.update z 15 (z 15+z 8) = _
    rw [hz15,hz8]
    unfold z
    change Function.update (Function.update w 14 (w 14+w 13)) 15 _ = _
    rw [hw14,hw13]
    unfold w
    change Function.update (Function.update (Function.update v (v 14) (v 16)) 14 _) 15 _ = _
    rw [hv14,hv16]
    rfl
  refine ⟨u+(1+(1+(1+0))),by omega,?_⟩
  rw [← he]
  exact .seq hr (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.skip _))))

private theorem decode_loop_runs (m : Mem) (xs : List ℕ) (s dst d : ℕ)
    (hd : 0 < d) (hs : 20 < s) (hD : 20 < dst) (hds : s+(encList encNat xs).length*d ≤ dst)
    (hptr : m 12 = s) (hstride : m 13 = d) (hto : m 14 = dst)
    (htwo : m 19 = 2) (hone : m 8 = 1)
    (hend : m 20 = s+(encList encNat xs).length*d-d)
    (hstream : MatchStream m s d (encList encNat xs)) :
    ∃ v t, Runs decoderLoop m v t ∧ t ≤ 13*(encList encNat xs).length+2 ∧
      v 12 = s+(encList encNat xs).length*d ∧ v 13 = d ∧
      v 15 = m 15+xs.length ∧ v 8 = 1 ∧ v 11 = m 11 ∧
      (∀ i : Fin xs.length, v (dst+i.val*d) = xs[i]) ∧
      ∀ r > 20, (∀ i : Fin xs.length, r ≠ dst+i.val*d) → v r = m r := by
  induction xs generalizing m s dst with
  | nil =>
    simp only [encList_nil, List.length_nil, Nat.zero_mul, Nat.add_zero] at hend ⊢
    have hguard : ¬m 12 ≤ m 20 := by rw [hptr,hend]; omega
    exact ⟨m,2,.done hguard,by omega,hptr,hstride,rfl,hone,rfl,fun i => Fin.elim0 i,fun _ _ _ => rfl⟩
  | cons x xs ih =>
    let n := (frame x.bits).length
    let bits := encList encNat xs
    have hbits : encList encNat (x::xs) = frame x.bits ++ bits := by
      simp [bits, encNat_apply]
    have hL : (encList encNat (x::xs)).length = n+bits.length := by rw [hbits,List.length_append]
    have hn : 1 ≤ n := by simp [n,length_frame]
    have ht : m 12 ≤ m 20 := by
      rw [hptr,hend,hL,Nat.add_mul]
      have hh : d ≤ n*d := by simpa using Nat.mul_le_mul_right d hn
      omega
    obtain ⟨u,hu,run₁⟩ := decodeOne_runs m x bits s dst d hs hD hptr hstride hto htwo hone
      (hbits ▸ hstream)
    let m' := decodedState m (s+n*d) (dst+d) (m 15+1) x (2^x.bits.length) dst
    obtain ⟨h12,h14,h15,h8,h13,h19,h20,h11,hat⟩ := decodedState_reads
      (m := m) (next := s+n*d) (dst := dst+d) (count := m 15+1) (value := x)
      (power := 2^x.bits.length) hD
    have hmatch' : MatchStream m' (s+n*d) d bits := by
      intro i
      have hi : n+i.val < (encList encNat (x::xs)).length := by
        rw [hL]; exact Nat.add_lt_add_left i.isLt _
      have he := hstream ⟨n+i.val,hi⟩
      have hp : i.val*d < bits.length*d := Nat.mul_lt_mul_of_pos_right i.isLt hd
      have hbound : s+n*d+bits.length*d ≤ dst := by
        simpa only [hL,Nat.add_mul,← Nat.add_assoc] using hds
      have hne : s+n*d+i.val*d ≠ dst := by omega
      change m' (s+n*d+i.val*d) = _
      unfold m'
      rw [decodedState_preserves (by omega) hne]
      have hb : ((encList encNat (x::xs))[n+i.val]) = bits[i] := by
        simp [hbits, List.getElem_append_right, show ¬ n+i.val < (frame x.bits).length by change ¬ n+i.val < n; omega, n]
      rw [← hb]
      have he' : m (s+(n+i.val)*d) = ramSymbol (some ((encList encNat (x::xs))[n+i.val])) := he
      simpa only [Nat.add_mul, Nat.add_assoc] using he'
    have he20 : m' 20 = s+n*d+bits.length*d-d := by
      unfold m'
      rw [h20,hend,hL,Nat.add_mul,Nat.add_assoc]
    obtain ⟨z,t,run₂,ht₂,hz12,hz13,hz15,hz8,hz11,hout,hpres⟩ :=
      ih m' (s+n*d) (dst+d) (by omega) (by omega) (by
        have hs' : s+n*d+bits.length*d ≤ dst := by
          simpa only [hL,Nat.add_mul,← Nat.add_assoc] using hds
        change s+n*d+bits.length*d ≤ dst+d
        omega)
        h12 (h13.trans hstride) h14 (h19.trans htwo) (h8.trans hone) he20 hmatch'
    refine ⟨z,2+u+t,.again ht run₁ run₂,?_ ,?_ ,hz13,?_ ,hz8,hz11.trans h11,?_ ,?_⟩
    · rw [hL]
      have hn' : n = 2*x.bits.length+1 := by simp [n,length_frame]
      change t ≤ 13*bits.length+2 at ht₂
      omega
    · rw [hL,Nat.add_mul,← Nat.add_assoc]
      exact hz12
    · rw [hz15,show m' 15 = m 15+1 from h15,List.length_cons]
      omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change z (dst+0*d) = x
        simp only [Nat.zero_mul,Nat.add_zero]
        rw [hpres dst hD (fun j => by have h := Nat.zero_le (j.val*d); omega)]
        exact hat
      · change z (dst+(j.val+1)*d) = xs[j]
        simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hout j
    · intro r hr hne
      have hr0 : r ≠ dst := by
        simpa using hne ⟨0,by simp⟩
      rw [hpres r hr (fun i => by
        have h := hne i.succ
        simpa [Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)]
      exact decodedState_preserves hr hr0

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA.RAMBlock

open Turing.MultiTapeTM

private def copyTailStep : Code := Code.chain [
  .load 23 22, .store 21 23, .add 21 21 8, .add 22 22 13
]

private def copyTail : Code := .whileLE 21 0 copyTailStep

private def copyTailState (m : Mem) (idx first d value : ℕ) : Mem :=
  Function.update (Function.update (Function.update
    (Function.update m 23 value) (idx+1) value) 21 (idx+2)) 22 (first+(idx+1)*d)

private theorem copyTailStep_runs {m : Mem} {idx first d value : ℕ}
    (hi : 23 ≤ idx) (h21 : m 21 = idx+1) (h22 : m 22 = first+idx*d)
    (h8 : m 8 = 1) (h13 : m 13 = d) (hread : m (first+idx*d) = value) :
    Runs copyTailStep m (copyTailState m idx first d value) 4 := by
  have n23 : idx+1 ≠ 23 := by omega
  have n8 : (8:ℕ) ≠ idx+1 := by omega
  have n13 : (13:ℕ) ≠ idx+1 := by omega
  have n21 : (21:ℕ) ≠ idx+1 := by omega
  have n22 : (22:ℕ) ≠ idx+1 := by omega
  have h := runs_atoms m [.load 23 22, .store 21 23, .add 21 21 8, .add 22 22 13]
  have he : execAtoms m [.load 23 22, .store 21 23, .add 21 21 8, .add 22 22 13] =
      copyTailState m idx first d value := by
    simp [execAtoms, Op.effect, copyTailState, h22, h21, h8, h13, hread, n23, n8, n13, n21, n22,
      Ne.symm n23, Nat.add_mul, Nat.add_assoc]
  exact he ▸ h

private theorem copyTail_runs (xs : List ℕ) (first d : ℕ) (hf : 23 < first) (hd : 1 ≤ d)
    (remaining idx : ℕ) (m : Mem) (hi : 23 ≤ idx) (hr : remaining = xs.length-idx)
    (h0 : m 0 = xs.length) (h8 : m 8 = 1) (h13 : m 13 = d)
    (h21 : m 21 = idx+1) (h22 : m 22 = first+idx*d)
    (hin : ∀ i : Fin xs.length, idx ≤ i.val → m (first+i.val*d) = xs[i]) :
    ∃ v t, Runs copyTail m v t ∧ t ≤ 6*remaining+2 ∧
      (∀ i : Fin xs.length, idx ≤ i.val → v (i.val+1) = xs[i]) ∧
      (∀ r, r < idx+1 → r ≠ 21 → r ≠ 22 → r ≠ 23 → v r = m r) ∧
      (∀ r > xs.length, 23 < r → v r = m r) := by
  induction remaining generalizing idx m with
  | zero =>
    have hh : ¬m 21 ≤ m 0 := by rw [h21,h0]; omega
    exact ⟨m,2,.done hh,by omega,fun i hit => by omega, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hn : idx < xs.length := by omega
    let value := xs[idx]
    let m' := copyTailState m idx first d value
    have hstep : Runs copyTailStep m m' 4 :=
      copyTailStep_runs hi h21 h22 h8 h13 (hin ⟨idx,hn⟩ le_rfl)
    have hkeep {r : ℕ} (ha : r ≠ 21) (hb : r ≠ 22) (hc : r ≠ 23) (ht : r ≠ idx+1) :
        m' r = m r := by
      simp [m', copyTailState, ha,hb,hc,ht]
    have hout : m' (idx+1) = value := by
      simp [m', copyTailState, show idx+1 ≠ 21 by omega, show idx+1 ≠ 22 by omega]
    have h21' : m' 21 = idx+1+1 := by simp [m',copyTailState]
    have h22' : m' 22 = first+(idx+1)*d := by simp [m',copyTailState]
    have ha : ∀ i : Fin xs.length, idx+1 ≤ i.val → m' (first+i.val*d) = xs[i] := by
      intro i hii
      have hmul : i.val ≤ i.val*d := by simpa using Nat.mul_le_mul_left i.val hd
      rw [hkeep (by omega) (by omega) (by omega) (by omega)]
      exact hin i (by omega)
    obtain ⟨v,t,ht,htb,hresult,hbelow,hlow⟩ := ih (idx+1) m' (by omega) (by omega)
      ((hkeep (by decide) (by decide) (by decide) (by omega)).trans h0)
      ((hkeep (by decide) (by decide) (by decide) (by omega)).trans h8)
      ((hkeep (by decide) (by decide) (by decide) (by omega)).trans h13) h21' h22' ha
    have hg : m 21 ≤ m 0 := by rw [h21,h0]; omega
    refine ⟨v,2+4+t,.again hg hstep ht,by omega,?_,?_,?_⟩
    · intro i hii
      by_cases hie : i.val = idx
      · have eqIdx : i = (⟨idx,hn⟩ : Fin xs.length) := Fin.ext hie
        subst i
        rw [hbelow _ (by omega) (by omega) (by omega) (by omega), hout]
        rfl
      · exact hresult i (by omega)
    · intro r hb ha hbb hc
      rw [hbelow r (by omega) ha hbb hc, hkeep ha hbb hc (by omega)]
    · intro r hr' hrs
      rw [hlow r hr' hrs, hkeep (by omega) (by omega) (by omega) (by omega)]

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA.RAMBlock

open Turing.MultiTapeTM

private theorem encList_length_ge (xs : List ℕ) : xs.length ≤ (encList encNat xs).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h : encList encNat (x::xs) = frame x.bits ++ encList encNat xs := by simp [encNat_apply]
    rw [List.length_cons,h,List.length_append,length_frame]
    omega

private def initCopyTail (d : ℕ) : Code := Code.chain [
  .const 7 0, .add 0 15 7, .const 21 24, .const 22 (23*d), .add 22 22 11
]

/-- Read the source output frames, and copy the high destinations without touching the staged
values. Low destinations are left for a bounded direct-address phase. -/
def ramDecodeHigh (k : ℕ) : Code :=
  .seq (RAMMiddle.decoderInit k) (.seq decoderLoop (.seq (initCopyTail (k+2)) copyTail))

theorem ramDecodeHigh_runs (k : ℕ) (xs : List ℕ) (m : Mem)
    (h5 : m 5 = (encList encNat xs).length) (h7 : m 7 = 0)
    (hLane : ∀ j, m (ramDataAddress k 1 j) = ramSymbol (encList encNat xs)[j]?) :
    ∃ v t first, Runs (ramDecodeHigh k) m v t ∧
      t ≤ k+20+19*(encList encNat xs).length ∧
      xs.length < first ∧ 23 < first ∧ v 0 = xs.length ∧ v 7 = 0 ∧ v 11 = first ∧
      (∀ i : Fin xs.length, v (first+i.val*(k+2)) = xs[i]) ∧
      (∀ i : Fin xs.length, 23 ≤ i.val → v (i.val+1) = xs[i]) := by
  let input := encList encNat xs
  let s := ramDataBase k+1
  let d := k+2
  let first := s+input.length*d
  have hs : 32 < s := by unfold s ramDataBase; omega
  have hfs : s ≤ first := by unfold first; omega
  have hLen : xs.length ≤ input.length := encList_length_ge xs
  have hMul : input.length ≤ input.length*d := by
    simpa using Nat.mul_le_mul_left input.length (show 1 ≤ d by unfold d; omega)
  have hf : xs.length < first := by unfold first; omega
  obtain ⟨w,u,hinit,hu,h12,h13,h14,h11,h15,h19,h8,h20,hkeep⟩ :=
    RAMMiddle.decoderInit_runs k input m h5 h7
  have hStream : MatchStream w s d input := by
    intro i
    change w (s+i.val*d) = ramSymbol (some input[i])
    have ha : s+i.val*d = ramDataAddress k 1 i.val := by
      simp [s,d,ramDataAddress,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    rw [hkeep _ (by change s ≤ s+i.val*d; omega), ha, hLane,
      List.getElem?_eq_getElem i.isLt]
    rfl
  obtain ⟨z,t,hdecode,ht,_,hzd,hzl,hz8,hz11,hvalues,_⟩ :=
    decode_loop_runs w xs s first d (by unfold d; omega) (by omega) (by omega)
      le_rfl h12 h13 h14 h19 h8 h20 hStream
  have hz0 : z 15 = xs.length := by simpa [h15] using hzl
  have hzB : z 11 = first := hz11.trans h11
  let ops : List Op := [.const 7 0, .add 0 15 7, .const 21 24, .const 22 (23*d), .add 22 22 11]
  let p := execAtoms z ops
  have hinitC : Runs (initCopyTail d) z p 5 := runs_atoms z ops
  have hp0 : p 0 = xs.length := by simp [p,ops,execAtoms,Op.effect,hz0]
  have hp7 : p 7 = 0 := by simp [p,ops,execAtoms,Op.effect]
  have hp8 : p 8 = 1 := by simp [p,ops,execAtoms,Op.effect,hz8]
  have hp11 : p 11 = first := by simp [p,ops,execAtoms,Op.effect,hzB]
  have hp13 : p 13 = d := by simp [p,ops,execAtoms,Op.effect,hzd]
  have hp21 : p 21 = 24 := by simp [p,ops,execAtoms,Op.effect]
  have hp22 : p 22 = first+23*d := by simp [p,ops,execAtoms,Op.effect,hzB,Nat.add_comm]
  have hpval (i : Fin xs.length) : p (first+i.val*d) = xs[i] := by
    have hi : 23 < first+i.val*d := by omega
    simp [p,ops,execAtoms,Op.effect,show first+i.val*d ≠ 22 by omega,
      show first+i.val*d ≠ 21 by omega,show first+i.val*d ≠ 0 by omega,
      show first+i.val*d ≠ 7 by omega]
    rw [Function.update_of_ne (show first+i.val*d ≠ 0 by omega),
      Function.update_of_ne (show first+i.val*d ≠ 7 by omega)]
    exact hvalues i
  obtain ⟨v,c,hcopy,hc,hrest,hbelow,habove⟩ :=
    copyTail_runs xs first d (by omega) (by unfold d; omega) (xs.length-23) 23 p le_rfl
      rfl hp0 hp8 hp13 hp21 hp22 (fun i _ => hpval i)
  refine ⟨v,u+(t+(5+c)),first,.seq hinit (.seq hdecode (.seq hinitC hcopy)),?_,
    hf,by omega,?_,?_,?_,?_,hrest⟩
  · change t ≤ 13*input.length+2 at ht
    change u+(t+(5+c)) ≤ k+20+19*input.length
    omega
  · rw [hbelow _ (by decide) (by decide) (by decide) (by decide), hp0]
  · rw [hbelow _ (by decide) (by decide) (by decide) (by decide), hp7]
  · rw [hbelow _ (by decide) (by decide) (by decide) (by decide), hp11]
  · intro i
    change v (first+i.val*d) = xs[i]
    rw [habove _ (by omega) (by omega), hpval]

end TimeSpaceMA.RAMBlock

open Turing.MultiTapeTM

namespace TimeSpaceMA

/-- Exact raw input received by the simulated binary machine. -/
theorem widthUnaryTriple_bits (n k v : ℕ) :
    encPair encUnary (encPair encNat encNat) (n,k,v) =
      frame (List.replicate n true) ++ frame k.bits ++ v.bits := by
  simp [List.append_assoc]

/-- Valid TUZ triples are encoded in linear length in the left vertex width. -/
theorem widthUnaryTriple_length_le (n k v : ℕ) (hk : k ≤ n) (hv : v < 2^n) :
    (encPair encUnary (encPair encNat encNat) (n,k,v)).length ≤ 5*n+2 := by
  rw [widthUnaryTriple_bits]
  simp only [List.length_append, length_frame, List.length_replicate]
  have hs : v.size ≤ n := Nat.size_le.mpr hv
  have hks : k.size ≤ n := Nat.size_le.mpr (hk.trans_lt (Nat.lt_two_pow_self (n := n)))
  rw [← Nat.size_eq_bits_len v] at hs
  rw [← Nat.size_eq_bits_len k] at hks
  omega

end TimeSpaceMA

namespace TimeSpaceMA

/-- A fixed polynomial in the unary-triple length is dominated by the log-cost
RAM's canonical width-dependent clock. -/
theorem widthUnaryTriple_polyClock (c d : ℕ) : ∃ e : ℕ,
    ∀ n k v : ℕ, 1 ≤ n → k ≤ n → v < 2^n →
      c * ((encPair encUnary (encPair encNat encNat) (n,k,v)).length + 1)^d ≤ n^e+e := by
  let C := c * 8^d
  let e := C+d
  refine ⟨e, ?_⟩
  intro n k v hn hk hv
  have hlen := widthUnaryTriple_length_le n k v hk hv
  have h : (encPair encUnary (encPair encNat encNat) (n,k,v)).length + 1 ≤ 8*n := by omega
  calc
    _ ≤ c * (8*n)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = C*n^d := by rw [Nat.mul_pow, Nat.mul_assoc]
    _ ≤ n^e+e := by
      by_cases he : n = 1
      · subst n; simp only [Nat.one_pow, Nat.mul_one]; dsimp [e]; omega
      · have h₂ : 2 ≤ n := by omega
        have hC : C ≤ (2:ℕ)^C := (Nat.lt_two_pow_self (n := C)).le
        calc
          C*n^d ≤ 2^C*n^d := Nat.mul_le_mul_right _ hC
          _ ≤ n^C*n^d := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h₂ _)
          _ = n^e := by rw [← Nat.pow_add]
          _ ≤ n^e+e := Nat.le_add_right _ _

end TimeSpaceMA

namespace TimeSpaceMA

open Turing Turing.MultiTapeTM Cslib

/-- On valid width triples, a native polynomial-time list computation has a fixed
polynomial clock in the numerical width. At that clock its output is exact and short. -/
theorem widthList_native_clock (listing : ℕ × ℕ × ℕ → List ℕ)
    (h : ComputableInPolyTime listing (encPair encUnary (encPair encNat encNat))
      (encList encNat)) :
    ∃ (κ : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM κ Bool Q) (c d : ℕ),
      ∀ n k v : ℕ, 1 ≤ n → k ≤ n → v < 2^n →
        let input := encPair encUnary (encPair encNat encNat) (n,k,v)
        let bound := c*(n+1)^d
        let cfg := tm.runFrom (tm.initCfg input) bound
        cfg.Halted ∧ cfg.output = encList encNat (listing (n,k,v)) ∧ cfg.output.length ≤ bound := by
  obtain ⟨t,s,hTime,_,κ,Q,hQ,tm,htm⟩ := h
  obtain ⟨c,d,hc⟩ := polynomiallyBounded_iff_le.mp hTime
  refine ⟨κ,Q,hQ,tm,c*8^d,d,?_⟩
  intro n k v hn hk hv
  let input := encPair encUnary (encPair encNat encNat) (n,k,v)
  let bound := c*8^d*(n+1)^d
  have hsize := widthUnaryTriple_length_le n k v hk hv
  have hsize' : input.length+1 ≤ 8*(n+1) := by
    change input.length ≤ 5*n+2 at hsize
    omega
  have hTB : t input.length ≤ bound := by
    calc
      _ ≤ c*(input.length+1)^d := hc _
      _ ≤ c*(8*(n+1))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize' _)
      _ = _ := by dsimp only [bound]; rw [Nat.mul_pow,Nat.mul_assoc]
  obtain ⟨hh,he⟩ := (htm (n,k,v)).runFrom_of_le hTB
  refine ⟨hh,he,?_⟩
  change (tm.runFrom (tm.initCfg input) bound).output.length ≤ bound
  have hLen := tm.length_output_runFrom_le (tm.initCfg input) bound
  change (tm.runFrom (tm.initCfg input) bound).output.length ≤ 0 + bound at hLen
  rw [Nat.zero_add] at hLen
  exact hLen

end TimeSpaceMA

namespace TimeSpaceMA.RAMBlock

/-- A fixed polynomial bound on unit steps gives the required canonical width-based charge.
The program itself is exactly the compiled block followed by a halt instruction. -/
theorem programRuns_poly (code : Code) (c d : ℕ) :
    let P := code.compile 0 ++ [.halt]
    ∃ e, P.CoinFree ∧ ∀ n k v : ℕ, 1 ≤ n → k ≤ n → v < 2^n →
      ∀ m t, Runs code (memOf [n,k,v]) m t → t ≤ c*(n+1)^d →
      ∃ st, P.RunsTo zeroTape (memOf [n,k,v]) st ∧ st.mem = m ∧ st.work ≤ n^e+e := by
  dsimp only
  let P := code.compile 0 ++ [.halt]
  let A := c*2^d
  let E := 2*d+1
  let C := A*(8*(code.width+2+A))*(P.length.size+1)+1
  let e := C+E
  have hCoinFree : P.CoinFree := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact code.compile_coinFree 0 r hr
    · simp at hr
  refine ⟨e,hCoinFree,?_⟩
  intro n k v hn hk hv m t hrun ht
  have hfixed : code.width ≤ code.width+n := Nat.le_add_right _ _
  have hkbits : k.size ≤ n := Nat.size_le.mpr (hk.trans_lt (Nat.lt_two_pow_self (n := n)))
  have hvbits : v.size ≤ n := Nat.size_le.mpr hv
  have hnbits : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hinit : Mem.WidthLE (memOf [n,k,v]) (code.width+n) := by
    intro r
    match r with
    | 0 => change n.size ≤ code.width+n; omega
    | 1 => change k.size ≤ code.width+n; omega
    | 2 => change v.size ≤ code.width+n; omega
    | r+3 => change (0:ℕ).size ≤ code.width+n; simp
  obtain ⟨_,w,hw,hW⟩ := hrun.toExecutes (code.width+n) hfixed hinit
  obtain ⟨st,hs,hm,hwork⟩ := hw.programRuns
  refine ⟨st,hs,hm,?_⟩
  have hstep : t ≤ A*n^d := by
    calc
      _ ≤ c*(n+1)^d := ht
      _ ≤ c*(2*n)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by dsimp only [A]; rw [Nat.mul_pow,Nat.mul_assoc]
  have hpow : 1 ≤ n^(d+1) := Nat.pow_pos (by omega)
  have hmon : n^d ≤ n^(d+1) := Nat.pow_le_pow_right (by omega : 0<n) (by omega)
  have hmono : n ≤ n^(d+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0<n) (show 1 ≤ d+1 by omega)
  have hsum : code.width+n+t+1 ≤ (code.width+2+A)*n^(d+1) := by
    have hA := Nat.mul_le_mul_left A hmon
    have hB := Nat.mul_le_mul_left code.width hpow
    rw [Nat.add_mul,Nat.add_mul,Nat.two_mul]
    omega
  have hbound : t*(8*(code.width+n+t+1)) ≤ A*(8*(code.width+2+A))*n^E := by
    calc
      _ ≤ (A*n^d) * (8*((code.width+2+A)*n^(d+1))) :=
        Nat.mul_le_mul hstep (Nat.mul_le_mul_left _ hsum)
      _ = _ := by
        dsimp only [E]
        rw [show 2*d+1=d+(d+1) by omega, Nat.pow_add]
        ring
  have habs : st.work ≤ C*n^E := by
    have he : 1 ≤ n^E := Nat.pow_pos (by omega)
    calc
      _ ≤ w*(P.length.size+1)+1 := hwork
      _ ≤ (A*(8*(code.width+2+A))*n^E)*(P.length.size+1)+1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ (hW.trans hbound)) _
      _ ≤ _ := by
        dsimp only [C]
        rw [Nat.add_mul,Nat.one_mul]
        have heq : A*(8*(code.width+2+A))*n^E*(P.length.size+1) =
            A*(8*(code.width+2+A))*(P.length.size+1)*n^E := by ring
        omega
  by_cases h1 : n=1
  · subst n
    simp only [Nat.one_pow,Nat.mul_one] at habs ⊢
    dsimp only [e]
    omega
  · have h2 : 2 ≤ n := by omega
    calc
      _ ≤ C*n^E := habs
      _ ≤ 2^C*n^E := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := C)).le
      _ ≤ n^C*n^E := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 _)
      _ = n^e := by rw [← Nat.pow_add]
      _ ≤ n^e+e := Nat.le_add_right _ _

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA.RAMBlock

private def copyLowOne (i d : ℕ) : Code :=
  .ifLE 23 0 (.chain [.const 23 (i*d),.add 23 22 23,.load (i+1) 23]) .skip

private def copyLowCheck (i d : ℕ) : Code := .seq (.const 23 (i+1)) (copyLowOne i d)

private def copyPairOps (d : ℕ) : List Op :=
  [.const 23 (21*d),.add 22 22 23,.const 23 d,.add 23 22 23,.load 22 22,.load 23 23]

private def copySingleOps (d : ℕ) : List Op := [.const 23 (21*d),.add 22 22 23,.load 22 22]

private def copyLowTail (d : ℕ) : Code :=
  .seq (.const 23 22) (.ifLE 23 0
    (.seq (.const 23 23) (.ifLE 23 0 (.chain ((copyPairOps d).map Code.atom))
      (.chain ((copySingleOps d).map Code.atom))))
    .skip)

/-- Copy the first at most 23 staged outputs to consecutive RAM cells. Addresses at
and above 24 have already been finalized and are left alone. -/
def copyLow (d : ℕ) : Code :=
  .seq (.add 22 11 7) (.seq (Code.chain ((List.range 21).map (copyLowCheck · d))) (copyLowTail d))

private theorem copyLowCheck_run (xs : List ℕ) (m : Mem) (first d i : ℕ) (_hi : i < 21)
    (hf : 23 < first) (h0 : m 0 = xs.length) (h22 : m 22 = first)
    (hstage : ∀ j : Fin xs.length, m (first+j.val*d) = xs[j]) :
    ∃ out t, Runs (copyLowCheck i d) m out t ∧ t ≤ 5 ∧
      (∀ j : Fin xs.length, j.val = i → out (j.val+1) = xs[j]) ∧
      ∀ r, r ≠ 23 → r ≠ i+1 → out r = m r := by
  let mid := Function.update m 23 (i+1)
  have hm : Runs (.const 23 (i+1)) m mid 1 := .atom (.const 23 (i+1)) m
  by_cases h : i < xs.length
  · let ops : List Op := [.const 23 (i*d),.add 23 22 23,.load (i+1) 23]
    let out := execAtoms mid ops
    have he : out = Function.update (Function.update m 23 (first+i*d)) (i+1) (xs[i]) := by
      have hne : first+i*d ≠ 23 := by omega
      have hb : m (first+i*d) = xs[i] := hstage ⟨i,h⟩
      simp [out,mid,ops,execAtoms,Op.effect,h22,hne,hb]
    have hc : mid 23 ≤ mid 0 := by simp [mid,h0]; omega
    refine ⟨out,5,.seq hm (.yes hc (runs_atoms mid ops)),by decide,?_,?_⟩
    · intro j hj
      rw [show j.val+1 = i+1 by omega,he,Function.update_self]
      have heq : (⟨i,h⟩ : Fin xs.length) = j := Fin.ext hj.symm
      exact congrArg (fun a : Fin xs.length => xs[a]) heq
    · intro r h23 hr
      rw [he,Function.update_of_ne hr,Function.update_of_ne h23]
  · have hn : ¬mid 23 ≤ mid 0 := by simp [mid,h0]; omega
    exact ⟨mid,3,.seq hm (.no hn (.skip _)),by decide,fun j hj => by have := j.isLt; omega,
      fun r h23 _ => Function.update_of_ne h23 _ _⟩

private theorem copyLowChecks_runs (xs : List ℕ) (m : Mem) (first d : ℕ) (is : List ℕ)
    (his : ∀ i ∈ is, i < 21) (hf : 23 < first) (h0 : m 0 = xs.length) (h22 : m 22 = first)
    (hstage : ∀ j : Fin xs.length, m (first+j.val*d) = xs[j]) :
    ∃ out t, Runs (Code.chain (is.map (copyLowCheck · d))) m out t ∧ t ≤ 5*is.length ∧
      (∀ j : Fin xs.length, j.val ∈ is → out (j.val+1) = xs[j]) ∧
      ∀ r, r ≠ 23 → (∀ i ∈ is, r ≠ i+1) → out r = m r := by
  induction is generalizing m with
  | nil => exact ⟨m,0,.skip _,by simp,fun _ h => False.elim (List.not_mem_nil h),fun _ _ _ => rfl⟩
  | cons i is ih =>
    have hi := his i List.mem_cons_self
    have hs (j : ℕ) (hj : j ∈ is) : j < 21 := his j (List.mem_cons_of_mem i hj)
    obtain ⟨mid,a,ha,hta,hva,hkeep⟩ := copyLowCheck_run xs m first d i hi hf h0 h22 hstage
    have hm0 : mid 0 = xs.length := (hkeep _ (by decide) (by omega)).trans h0
    have hm22 : mid 22 = first := (hkeep _ (by decide) (by omega)).trans h22
    have hmstage (j : Fin xs.length) : mid (first+j.val*d) = xs[j] :=
      (hkeep _ (by omega) (by omega)).trans (hstage j)
    obtain ⟨out,b,hb,htb,hvb,hpres⟩ := ih mid hs hm0 hm22 hmstage
    refine ⟨out,a+b,.seq ha hb,by simp; omega,?_,?_⟩
    · intro j hj
      by_cases h : j.val ∈ is
      · exact hvb j h
      · have hji : j.val = i := by simpa [h] using hj
        have hne23 : j.val+1 ≠ 23 := by omega
        have hne (u : ℕ) (hu : u ∈ is) : j.val+1 ≠ u+1 := by
          intro he
          have heu : j.val = u := by omega
          exact h (by rwa [heu])
        rw [hpres _ hne23 hne,hva j hji]
    · intro r h23 hr
      rw [hpres r h23 (fun u hu => hr u (List.mem_cons_of_mem i hu)), hkeep r h23 (hr i List.mem_cons_self)]

private theorem copyPairEffect (m : Mem) (first d a b : ℕ) (hf : 23 < first)
    (h22 : m 22 = first) (ha : m (first+21*d) = a) (hb : m (first+22*d) = b) :
    execAtoms m (copyPairOps d) = Function.update (Function.update m 22 a) 23 b := by
  have he : first+21*d+d=first+22*d := by
    rw [show 22*d = (21+1)*d by rfl, Nat.add_mul,Nat.one_mul,Nat.add_assoc]
  have ne22 (i : ℕ) : first+i*d ≠ 22 := by omega
  have ne23 (i : ℕ) : first+i*d ≠ 23 := by omega
  simp [copyPairOps,execAtoms,Op.effect,h22,he,ha,hb,ne22,ne23,Function.update_idem]
  funext r
  by_cases h22 : r=22 <;> by_cases h23 : r=23 <;> simp [h22,h23]

private theorem copySingleEffect (m : Mem) (first d a : ℕ) (hf : 23 < first)
    (h22 : m 22 = first) (ha : m (first+21*d) = a) :
    execAtoms m (copySingleOps d) = Function.update (Function.update m 23 (21*d)) 22 a := by
  have ne22 : first+21*d ≠ 22 := by omega
  have ne23 : first+21*d ≠ 23 := by omega
  simp [copySingleOps,execAtoms,Op.effect,h22,ha,ne22,ne23,Function.update_idem]

private theorem copyLowTail_runs (xs : List ℕ) (m : Mem) (first d : ℕ) (hf : 23 < first)
    (h0 : m 0 = xs.length) (h22 : m 22 = first)
    (hstage : ∀ j : Fin xs.length, m (first+j.val*d) = xs[j]) :
    ∃ out t, Runs (copyLowTail d) m out t ∧ t ≤ 10 ∧
      (∀ j : Fin xs.length, 21 ≤ j.val → j.val < 23 → out (j.val+1) = xs[j]) ∧
      ∀ r, r ≠ 22 → r ≠ 23 → out r = m r := by
  let m₁ := Function.update m 23 22
  have h₁ : Runs (.const 23 22) m m₁ 1 := .atom _ _
  have hm22 : m₁ 22 = first := by simpa [m₁] using h22
  by_cases hbig : 22 ≤ xs.length
  · have hy : m₁ 23 ≤ m₁ 0 := by simpa [m₁,h0] using hbig
    let m₂ := Function.update m₁ 23 23
    have h₂ : Runs (.const 23 23) m₁ m₂ 1 := .atom _ _
    have hm22' : m₂ 22 = first := by simpa [m₂] using hm22
    have hmstage (j : Fin xs.length) : m₂ (first+j.val*d) = xs[j] := by
      have hne : first+j.val*d ≠ 23 := by omega
      simpa [m₂,m₁,Function.update_of_ne hne] using hstage j
    let a : Fin xs.length := ⟨21,by omega⟩
    by_cases hhuge : 23 ≤ xs.length
    · have hy₂ : m₂ 23 ≤ m₂ 0 := by simpa [m₂,m₁,h0] using hhuge
      let b : Fin xs.length := ⟨22,by omega⟩
      let out := execAtoms m₂ (copyPairOps d)
      have ha : m₂ (first+21*d) = xs[a] := hmstage a
      have hb : m₂ (first+22*d) = xs[b] := hmstage b
      have hfout : out = Function.update (Function.update m₂ 22 xs[a]) 23 xs[b] :=
        copyPairEffect m₂ first d xs[a] xs[b] hf hm22' ha hb
      refine ⟨out,10,.seq h₁ (.yes hy (.seq h₂ (.yes hy₂ (runs_atoms m₂ (copyPairOps d))))),by decide,?_,?_⟩
      · intro j hj₁ hj₂
        by_cases he : j.val = 21
        · have hja : j = a := Fin.ext he
          subst j
          simp [hfout,a]
        · have hjb : j = b := Fin.ext (by dsimp [b]; omega)
          subst j
          simp [hfout,b]
      · intro r h22' h23'
        simp [hfout,m₂,m₁,Function.update_of_ne h22',Function.update_of_ne h23']
    · have hn₂ : ¬m₂ 23 ≤ m₂ 0 := by simpa [m₂,m₁,h0] using hhuge
      let out := execAtoms m₂ (copySingleOps d)
      have ha : m₂ (first+21*d) = xs[a] := hmstage a
      have hfout : out = Function.update (Function.update m₂ 23 (21*d)) 22 xs[a] :=
        copySingleEffect m₂ first d xs[a] hf hm22' ha
      refine ⟨out,8,.seq h₁ (.yes hy (.seq h₂ (.no hn₂ (runs_atoms m₂ (copySingleOps d))))),by decide,?_,?_⟩
      · intro j hj₁ hj₂
        have hjlt := j.isLt
        have hja : j = a := Fin.ext (by dsimp [a]; omega)
        subst j
        simp [hfout,a]
      · intro r h22' h23'
        simp [hfout,m₂,m₁,Function.update_of_ne h22',Function.update_of_ne h23']
  · have hn : ¬m₁ 23 ≤ m₁ 0 := by simpa [m₁,h0] using hbig
    refine ⟨m₁,3,.seq h₁ (.no hn (.skip _)),by decide,?_,?_⟩
    · intro j h _
      have hj := j.isLt
      omega
    · intro r _ hr
      exact Function.update_of_ne hr _ _

/-- Finalize the low RAM output cells from a disjoint staging interval. The branch and
statically unrolled copies use at most 116 primitive instructions for every output length. -/
theorem copyLow_runs (xs : List ℕ) (first d : ℕ) (m : Mem)
    (hf : 23 < first) (h0 : m 0 = xs.length) (h7 : m 7 = 0) (h11 : m 11 = first)
    (hstage : ∀ j : Fin xs.length, m (first+j.val*d) = xs[j]) :
    ∃ out t, Runs (copyLow d) m out t ∧ t ≤ 116 ∧ out 0 = xs.length ∧
      (∀ j : Fin xs.length, j.val < 23 → out (j.val+1) = xs[j]) ∧
      ∀ r, 24 ≤ r → out r = m r := by
  let mid := Function.update m 22 (m 11 + m 7)
  have hs : Runs (.add 22 11 7) m mid 1 := .atom _ _
  have hm22 : mid 22 = first := by simp [mid,h11,h7]
  have hm0 : mid 0 = xs.length := by simpa [mid] using h0
  have hmstage (j : Fin xs.length) : mid (first+j.val*d) = xs[j] := by
    have hne : first+j.val*d ≠ 22 := by omega
    simpa [mid,Function.update_of_ne hne] using hstage j
  have hrange (i : ℕ) (hi : i ∈ List.range 21) : i < 21 := List.mem_range.mp hi
  obtain ⟨pre,u,hu,hbu,hlo,hpres⟩ := copyLowChecks_runs xs mid first d (List.range 21) hrange hf hm0 hm22 hmstage
  have hc0 : pre 0 = xs.length := (hpres _ (by decide) (by intro i _; omega)).trans hm0
  have hc22 : pre 22 = first := (hpres _ (by decide) (by intro i hi; have := hrange i hi; omega)).trans hm22
  have hcstage (j : Fin xs.length) : pre (first+j.val*d) = xs[j] :=
    (hpres _ (by omega) (by intro i hi; have := hrange i hi; omega)).trans (hmstage j)
  obtain ⟨out,t,ht,hbt,hvals,hkeep⟩ := copyLowTail_runs xs pre first d hf hc0 hc22 hcstage
  refine ⟨out,1+(u+t),.seq hs (.seq hu ht),by simp at hbu; omega,
    (hkeep 0 (by decide) (by decide)).trans hc0,?_,?_⟩
  · intro j hj
    by_cases h : j.val < 21
    · rw [hkeep _ (by omega) (by omega)]
      exact hlo j (List.mem_range.mpr h)
    · exact hvals j (by omega) hj
  · intro r hr
    rw [hkeep _ (by omega) (by omega),hpres _ (by omega) (by intro i hi; have := hrange i hi; omega)]
    exact Function.update_of_ne (by omega) _ _

end TimeSpaceMA.RAMBlock

namespace TimeSpaceMA

open RAMBlock Turing.MultiTapeTM

/-- Compile a polynomial-time list computation to a deterministic log-cost RAM. The
serializer pays for the unary width and binary input fields, the simulated machine
pays for each tape transition, and the output decoder supplies the contiguous layout. -/
theorem widthListComputable_to_coinFreeRAM
    (listing : ℕ × ℕ × ℕ → List ℕ)
    (hlisting : ComputableInPolyTime listing (encPair encUnary (encPair encNat encNat))
      (encList encNat)) :
    ∃ (e : ℕ) (P : Program), P.CoinFree ∧
      ∀ n k v : ℕ, 1 ≤ n → k ≤ n → v < 2^n →
        ∃ st, P.RunsTo zeroTape (memOf [n,k,v]) st ∧ st.work ≤ n^e+e ∧
          st.mem 0 = (listing (n,k,v)).length ∧
          ∀ i : Fin (listing (n,k,v)).length, st.mem (1+i.val) = (listing (n,k,v))[i] := by
  classical
  obtain ⟨κ,Q,hQ,tm,c,d,hClock⟩ := widthList_native_clock listing hlisting
  letI : Finite Q := hQ
  letI : Fintype Q := Fintype.ofFinite Q
  let q := Fintype.card Q
  let ids : Q ≃ Fin q := Fintype.equivFin Q
  let code : Code := .seq (ramWidthInputInit κ ids tm.q₀)
    (.seq (RAMMiddle.code ids tm) (.seq (ramDecodeHigh κ) (copyLow (κ+2))))
  let C : ℕ := 112+((RAMMiddle.stepCount κ q+21)*c+(κ+22+116))
  let D : ℕ := max 3 d
  obtain ⟨e,hfree,hCompile⟩ := programRuns_poly code C D
  refine ⟨e,code.compile 0 ++ [.halt],hfree,?_⟩
  intro n k v hn hk hv
  let xs := listing (n,k,v)
  let B := c*(n+1)^d
  obtain ⟨hHalt,hOutput,hLen⟩ := hClock n k v hn hk hv
  have hl : (encList encNat xs).length ≤ B := by
    simpa only [hOutput] using hLen
  obtain ⟨m₁,u,hr₁,hu,hrep⟩ := ramWidthInputInit_runs κ n k v hk hv ids tm.q₀
  obtain ⟨m₂,t,hr₂,ht,h5,h7,hLane⟩ := RAMMiddle.runs tm B hrep hHalt hOutput
  obtain ⟨m₃,w,first,hr₃,hw,hfirst,hsafe,h0,h7',h11,hstage,htail⟩ :=
    ramDecodeHigh_runs κ xs m₂ h5 h7 hLane
  obtain ⟨m₄,z,hr₄,hz,hCount,hLow,hHigher⟩ :=
    copyLow_runs xs first (κ+2) m₃ hsafe h0 h7' h11 hstage
  have hItems (i : Fin xs.length) : m₄ (i.val+1) = xs[i] := by
    by_cases hi : i.val < 23
    · exact hLow i hi
    · rw [hHigher _ (by omega)]
      exact htail i (by omega)
  have hr : Runs code (memOf [n,k,v]) m₄ (u+(t+(w+z))) :=
    .seq hr₁ (.seq hr₂ (.seq hr₃ hr₄))
  have hD : 1 ≤ (n+1)^D := Nat.pow_pos (by omega)
  have hdD : (n+1)^d ≤ (n+1)^D := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have h3D : (n+1)^3 ≤ (n+1)^D := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hb : B ≤ c*(n+1)^D := Nat.mul_le_mul_left c hdD
  have hlinear : (RAMMiddle.stepCount κ q+2)*B+19*(encList encNat xs).length ≤
      ((RAMMiddle.stepCount κ q+21)*c)*(n+1)^D := by
    calc
      _ ≤ (RAMMiddle.stepCount κ q+2)*(c*(n+1)^D)+19*(c*(n+1)^D) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ (hl.trans hb))
      _ = _ := by ring
  have hConst : κ+22+116 ≤ (κ+22+116)*(n+1)^D := by
    simpa using Nat.mul_le_mul_left (κ+22+116) hD
  have htotal : u+(t+(w+z)) ≤ C*(n+1)^D := by
    unfold C
    rw [Nat.add_mul 112, Nat.add_mul ((RAMMiddle.stepCount κ q+21)*c)]
    change w ≤ κ+20+19*(encList encNat xs).length at hw
    have hu' : u ≤ 112*(n+1)^D := hu.trans (Nat.mul_le_mul_left _ h3D)
    change t ≤ (RAMMiddle.stepCount κ q+2)*B+2 at ht
    omega
  obtain ⟨st,hrun,hm,hwork⟩ := hCompile n k v hn hk hv m₄ _ hr htotal
  refine ⟨st,hrun,hwork,?_,?_⟩
  · rw [hm]
    exact hCount
  · intro i
    rw [hm, Nat.add_comm]
    exact hItems i

end TimeSpaceMA

open Turing.MultiTapeTM

theorem solution
    (listing : ℕ × ℕ × ℕ → List ℕ)
    (hlisting : ComputableInPolyTime listing (encPair encUnary (encPair encNat encNat))
      (encList encNat)) :
    ∃ (e : ℕ) (P : TimeSpaceMA.Program), P.CoinFree ∧
      ∀ n k v : ℕ, 1 ≤ n → k ≤ n → v < 2^n →
        ∃ st, P.RunsTo TimeSpaceMA.zeroTape (TimeSpaceMA.memOf [n,k,v]) st ∧ st.work ≤ n^e+e ∧
          st.mem 0 = (listing (n,k,v)).length ∧
          ∀ i : Fin (listing (n,k,v)).length, st.mem (1+i.val) = (listing (n,k,v))[i] :=
  TimeSpaceMA.widthListComputable_to_coinFreeRAM listing hlisting
