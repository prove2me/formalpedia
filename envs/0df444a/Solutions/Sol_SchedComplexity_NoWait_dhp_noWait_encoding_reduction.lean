-- Prove2me | solution 1 for SchedComplexity.NoWait.dhp_noWait_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:13:27.105187+00:00
-- url     : https://prove2.me/submissions/89e15320-2149-4dd4-8b4d-f6670677b3a1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackCompare
import Definitions.Def_CookPvsNP_StackRepeat
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Definitions.Def_SchedComplexity_NoWait_Construction
import Theorems.Thm_SchedComplexity_NoWait_theorem_5a_equiv
import Theorems.Thm_SchedComplexity_NoWait_theorem_5b_equiv


set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## Registers of the stack machine -/

inductive Key
  | inp | out | bad | A | Pd | Bn | Bt | F | N | M | R | T | W | X | Z | sc | L | JB | S | J | RC | KL | KJ | RF | CC | X0 | X1 | X2 | E1 | E2 | Um | Bm | Uy | By | U | Bp | G1 | G2
  deriving DecidableEq

instance : Fintype Key :=
  ⟨⟨([.inp, .out, .bad, .A, .Pd, .Bn, .Bt, .F, .N, .M, .R, .T, .W, .X, .Z, .sc, .L, .JB, .S, .J, .RC, .KL, .KJ, .RF, .CC, .X0, .X1, .X2, .E1, .E2, .Um, .Bm, .Uy, .By, .U, .Bp, .G1, .G2] : List Key), by decide⟩, by intro x; cases x <;> decide⟩

structure Regs where
  inp : List BSym
  out : List BSym
  bad : List BSym
  A : List BSym
  Pd : List BSym
  Bn : List BSym
  Bt : List BSym
  F : List BSym
  N : List BSym
  M : List BSym
  R : List BSym
  T : List BSym
  W : List BSym
  X : List BSym
  Z : List BSym
  sc : List BSym
  L : List BSym
  JB : List BSym
  S : List BSym
  J : List BSym
  RC : List BSym
  KL : List BSym
  KJ : List BSym
  RF : List BSym
  CC : List BSym
  X0 : List BSym
  X1 : List BSym
  X2 : List BSym
  E1 : List BSym
  E2 : List BSym
  Um : List BSym
  Bm : List BSym
  Uy : List BSym
  By : List BSym
  U : List BSym
  Bp : List BSym
  G1 : List BSym
  G2 : List BSym

namespace Regs

def get (σ : Regs) : Key → List BSym
  | .inp => σ.inp
  | .out => σ.out
  | .bad => σ.bad
  | .A => σ.A
  | .Pd => σ.Pd
  | .Bn => σ.Bn
  | .Bt => σ.Bt
  | .F => σ.F
  | .N => σ.N
  | .M => σ.M
  | .R => σ.R
  | .T => σ.T
  | .W => σ.W
  | .X => σ.X
  | .Z => σ.Z
  | .sc => σ.sc
  | .L => σ.L
  | .JB => σ.JB
  | .S => σ.S
  | .J => σ.J
  | .RC => σ.RC
  | .KL => σ.KL
  | .KJ => σ.KJ
  | .RF => σ.RF
  | .CC => σ.CC
  | .X0 => σ.X0
  | .X1 => σ.X1
  | .X2 => σ.X2
  | .E1 => σ.E1
  | .E2 => σ.E2
  | .Um => σ.Um
  | .Bm => σ.Bm
  | .Uy => σ.Uy
  | .By => σ.By
  | .U => σ.U
  | .Bp => σ.Bp
  | .G1 => σ.G1
  | .G2 => σ.G2

def set (σ : Regs) : Key → List BSym → Regs
  | .inp, l => { σ with inp := l }
  | .out, l => { σ with out := l }
  | .bad, l => { σ with bad := l }
  | .A, l => { σ with A := l }
  | .Pd, l => { σ with Pd := l }
  | .Bn, l => { σ with Bn := l }
  | .Bt, l => { σ with Bt := l }
  | .F, l => { σ with F := l }
  | .N, l => { σ with N := l }
  | .M, l => { σ with M := l }
  | .R, l => { σ with R := l }
  | .T, l => { σ with T := l }
  | .W, l => { σ with W := l }
  | .X, l => { σ with X := l }
  | .Z, l => { σ with Z := l }
  | .sc, l => { σ with sc := l }
  | .L, l => { σ with L := l }
  | .JB, l => { σ with JB := l }
  | .S, l => { σ with S := l }
  | .J, l => { σ with J := l }
  | .RC, l => { σ with RC := l }
  | .KL, l => { σ with KL := l }
  | .KJ, l => { σ with KJ := l }
  | .RF, l => { σ with RF := l }
  | .CC, l => { σ with CC := l }
  | .X0, l => { σ with X0 := l }
  | .X1, l => { σ with X1 := l }
  | .X2, l => { σ with X2 := l }
  | .E1, l => { σ with E1 := l }
  | .E2, l => { σ with E2 := l }
  | .Um, l => { σ with Um := l }
  | .Bm, l => { σ with Bm := l }
  | .Uy, l => { σ with Uy := l }
  | .By, l => { σ with By := l }
  | .U, l => { σ with U := l }
  | .Bp, l => { σ with Bp := l }
  | .G1, l => { σ with G1 := l }
  | .G2, l => { σ with G2 := l }

lemma update_get (σ : Regs) (k : Key) (l : List BSym) :
    Function.update σ.get k l = (σ.set k l).get := by
  funext j
  cases k <;> cases j <;> rfl

lemma get_set (σ : Regs) (k j : Key) (l : List BSym) :
    (σ.set k l).get j = if j = k then l else σ.get j := by
  rw [← update_get]; simp [Function.update_apply]

@[simp] lemma get_set_self (σ : Regs) (k : Key) (l : List BSym) : (σ.set k l).get k = l := by
  simp [get_set]

lemma ext_get {σ τ : Regs} (h : σ.get = τ.get) : σ = τ := by
  cases σ; cases τ
  simp only [Regs.mk.injEq]
  exact ⟨congrFun h .inp, congrFun h .out, congrFun h .bad, congrFun h .A, congrFun h .Pd, congrFun h .Bn, congrFun h .Bt, congrFun h .F, congrFun h .N, congrFun h .M, congrFun h .R, congrFun h .T, congrFun h .W, congrFun h .X, congrFun h .Z, congrFun h .sc, congrFun h .L, congrFun h .JB, congrFun h .S, congrFun h .J, congrFun h .RC, congrFun h .KL, congrFun h .KJ, congrFun h .RF, congrFun h .CC, congrFun h .X0, congrFun h .X1, congrFun h .X2, congrFun h .E1, congrFun h .E2, congrFun h .Um, congrFun h .Bm, congrFun h .Uy, congrFun h .By, congrFun h .U, congrFun h .Bp, congrFun h .G1, congrFun h .G2⟩

lemma set_set (σ : Regs) (k : Key) (u v : List BSym) : (σ.set k u).set k v = σ.set k v := by
  apply ext_get; funext j; simp only [get_set]; split_ifs <;> rfl

lemma set_comm (σ : Regs) {k j : Key} (h : k ≠ j) (u v : List BSym) :
    (σ.set k u).set j v = (σ.set j v).set k u := by
  apply ext_get; funext i; simp only [get_set]
  split_ifs with h1 h2 <;> first | rfl | (subst h1; subst h2; exact absurd rfl h)

lemma set_get (σ : Regs) (k : Key) : σ.set k (σ.get k) = σ := by
  apply ext_get; funext j; simp only [get_set]; split_ifs with h <;> first | rfl | (subst h; rfl)

end Regs

abbrev Prog := StackProg Key BSym

/-- the tops of a register file -/
def hd (σ : Regs) : Key → Option BSym := fun k => (σ.get k).head?

/-- `p` runs from `σ` to `τ` within `B` steps. -/
def Runs (p : Prog) (σ τ : Regs) (B : ℕ) : Prop := ∃ n ≤ B, p.Exec σ.get τ.get n

/-! ## Combinators -/

lemma Runs.mono {p : Prog} {σ τ : Regs} {B B' : ℕ} (h : Runs p σ τ B) (hB : B ≤ B') :
    Runs p σ τ B' := by
  obtain ⟨n, hn, e⟩ := h; exact ⟨n, le_trans hn hB, e⟩

lemma Runs.seq {p q : Prog} {σ τ υ : Regs} {B1 B2 : ℕ} (h1 : Runs p σ τ B1)
    (h2 : Runs q τ υ B2) : Runs (.seq p q) σ υ (B1 + 1 + B2) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, e'⟩ := h2
  exact ⟨n + 1 + m, by omega, StackProg.Exec.seq e e'⟩

lemma Runs.seq' {p q : Prog} {σ τ υ : Regs} {B1 B2 B : ℕ} (h1 : Runs p σ τ B1)
    (h2 : Runs q τ υ B2) (hB : B1 + 1 + B2 ≤ B) : Runs (.seq p q) σ υ B :=
  (h1.seq h2).mono hB

lemma Runs.brT {t : (Key → Option BSym) → Bool} {p q : Prog} {σ τ : Regs} {B : ℕ}
    (ht : t (hd σ) = true) (h : Runs p σ τ B) : Runs (.branch t p q) σ τ (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchTrue ht e⟩

lemma Runs.brF {t : (Key → Option BSym) → Bool} {p q : Prog} {σ τ : Regs} {B : ℕ}
    (ht : t (hd σ) = false) (h : Runs q σ τ B) : Runs (.branch t p q) σ τ (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchFalse ht e⟩

/-- a loop driven by an explicit sequence of register files -/
lemma Runs.loopU (t : (Key → Option BSym) → Bool) (body : Prog) (h : ℕ → Regs) (B m : ℕ)
    (hstep : ∀ j < m, t (hd (h j)) = true ∧ Runs body (h j) (h (j + 1)) B)
    (hstop : t (hd (h m)) = false) :
    Runs (.loop t body) (h 0) (h m) (m * (B + 2) + 1) := by
  have key : ∀ i, i ≤ m → Runs (.loop t body) (h (m - i)) (h m) (i * (B + 2) + 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨1, by simp, by simpa using StackProg.Exec.loopFalse hstop⟩
    | succ i ih =>
      intro hi
      obtain ⟨ht, n, hn, e⟩ := hstep (m - (i + 1)) (by omega)
      obtain ⟨n', hn', e'⟩ := ih (by omega)
      have hidx : m - (i + 1) + 1 = m - i := by omega
      rw [hidx] at e
      refine ⟨1 + n + 1 + n', ?_, StackProg.Exec.loopTrue ht e e'⟩
      have : (i + 1) * (B + 2) + 1 = i * (B + 2) + 1 + (B + 2) := by ring
      omega
  simpa using key m le_rfl

/-! ## Primitive programs -/

def mvProg (a b : Key) : Prog := transferProg a (fun k => decide (k = b))

lemma runs_push (k : Key) (a : BSym) (σ : Regs) :
    Runs (pushProg k a) σ (σ.set k (a :: σ.get k)) 1 :=
  ⟨1, le_rfl, by rw [← Regs.update_get]; exact (stack_basic_macros k σ.get).1 a⟩

lemma runs_pop (k : Key) (σ : Regs) : Runs (popProg k) σ (σ.set k (σ.get k).tail) 1 :=
  ⟨1, le_rfl, by rw [← Regs.update_get]; exact (stack_basic_macros k σ.get).2.1⟩

lemma runs_clear (k : Key) (σ : Regs) :
    Runs (clearProg k) σ (σ.set k []) (3 * (σ.get k).length + 1) :=
  ⟨_, le_rfl, by rw [← Regs.update_get]; exact (stack_basic_macros k σ.get).2.2⟩

lemma runs_copy (a b c : Key) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (σ : Regs)
    (hc : σ.get c = []) :
    Runs (copyProg a b c) σ (σ.set b (σ.get a ++ σ.get b)) (6 * (σ.get a).length + 3) :=
  ⟨_, le_rfl, by rw [← Regs.update_get]; exact stack_copy a b c hab hac hbc σ.get hc⟩

lemma runs_mv (a b : Key) (hab : a ≠ b) (σ : Regs) :
    Runs (mvProg a b) σ ((σ.set a []).set b ((σ.get a).reverse ++ σ.get b))
      (3 * (σ.get a).length + 1) := by
  refine ⟨_, le_rfl, ?_⟩
  have e := stack_transfer a (fun k => decide (k = b)) σ.get
  unfold mvProg
  convert e using 1
  funext k
  rw [Regs.get_set, Regs.get_set]
  simp only [transferStore]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab]
  · by_cases h2 : k = a
    · subst h2; simp [h1]
    · simp [h1, h2]

lemma runs_syncpop (i j : Key) (hij : i ≠ j) (σ : Regs) :
    Runs (syncPopProg i j) σ
      ((σ.set i ((σ.get i).drop (min (σ.get i).length (σ.get j).length))).set j
        ((σ.get j).drop (min (σ.get i).length (σ.get j).length)))
      (3 * min (σ.get i).length (σ.get j).length + 1) := by
  refine ⟨_, le_rfl, ?_⟩
  have e := stack_sync_pop i j hij σ.get
  simp only at e
  convert e using 1
  rw [← Regs.update_get, ← Regs.update_get]

def emb4 (a b c d : Key) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ Key :=
  ⟨![a, b, c, d], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

/-- `b := (src repeated |c| times) ++ b`, consuming `c` -/
def repProg (a b c d : Key) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Prog :=
  repeatCopyProg (emb4 a b c d hab hac had hbc hbd hcd)

lemma runs_rep (a b c d : Key) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (σ : Regs) (hd0 : σ.get d = []) :
    Runs (repProg a b c d hab hac had hbc hbd hcd) σ
      ((σ.set c []).set b ((List.replicate (σ.get c).length (σ.get a)).flatten ++ σ.get b))
      ((6 * (σ.get a).length + 7) * (σ.get c).length + 1) := by
  refine ⟨_, le_rfl, ?_⟩
  have e := stack_repeat_copy (emb4 a b c d hab hac had hbc hbd hcd) σ.get hd0
  rw [← Regs.update_get, ← Regs.update_get]
  exact e

/-- a no-op -/
def skipP : Prog := .act (fun _ _ => .keep)

lemma runs_skip (σ : Regs) : Runs skipP σ σ 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (_ : Key) => (StackAct.keep : StackAct BSym)) σ.get
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (_ : Key) => (StackAct.keep : StackAct BSym)) σ.get = σ.get := by
    funext k; rfl
  rw [this] at e; exact e

/-- move the top of `a` onto `b` (one step) -/
def mv1 (a b : Key) : Prog := .act (transferAct a (fun k => decide (k = b)))

lemma runs_mv1 (a b : Key) (hab : a ≠ b) (σ : Regs) (x : BSym) (l : List BSym)
    (h : σ.get a = x :: l) : Runs (mv1 a b) σ ((σ.set a l).set b (x :: σ.get b)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act (transferAct a (fun k => decide (k = b))) σ.get
  unfold mv1
  convert e using 1
  funext k
  rw [Regs.get_set, Regs.get_set]
  simp only [StackProg.applyAct, transferAct]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab, h, StackAct.apply]
  · by_cases h2 : k = a
    · subst h2; simp [h, StackAct.apply, hab]
    · simp [h1, h2, StackAct.apply]

/-- move the maximal prefix of `a` satisfying `pred` onto `b` (reversed) -/
def mvwProg (a b : Key) (pred : BSym → Bool) : Prog :=
  .loop (fun h => match h a with | some x => pred x | none => false) (mv1 a b)

lemma runs_mvw (a b : Key) (hab : a ≠ b) (pred : BSym → Bool) :
    ∀ (l : List BSym) (σ : Regs), σ.get a = l →
      Runs (mvwProg a b pred) σ
        ((σ.set a (l.dropWhile pred)).set b ((l.takeWhile pred).reverse ++ σ.get b))
        (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro σ hσ
    refine ⟨1, le_rfl, ?_⟩
    simp only [List.dropWhile_nil, List.takeWhile_nil, List.reverse_nil, List.nil_append]
    rw [← hσ, Regs.set_get, Regs.set_get]
    exact StackProg.Exec.loopFalse (by simp [hd, hσ])
  | cons x l ih =>
    intro σ hσ
    by_cases hp : pred x = true
    · have h1 := runs_mv1 a b hab σ x l hσ
      set σ1 := (σ.set a l).set b (x :: σ.get b) with hσ1
      have hσ1a : σ1.get a = l := by
        rw [hσ1, Regs.get_set, if_neg hab, Regs.get_set_self]
      obtain ⟨m, hm, e2⟩ := ih σ1 hσ1a
      obtain ⟨n, hn, e1⟩ := h1
      refine ⟨1 + n + 1 + m, by simp; omega, ?_⟩
      have hres : ((σ1.set a (l.dropWhile pred)).set b ((l.takeWhile pred).reverse ++ σ1.get b)) =
          ((σ.set a ((x :: l).dropWhile pred)).set b (((x :: l).takeWhile pred).reverse ++ σ.get b)) := by
        have hb : σ1.get b = x :: σ.get b := by rw [hσ1, Regs.get_set_self]
        rw [hb]
        simp only [List.dropWhile_cons, List.takeWhile_cons, hp, if_true, List.reverse_cons,
          List.append_assoc, List.singleton_append]
        rw [hσ1]
        apply Regs.ext_get; funext i; simp only [Regs.get_set]
        split_ifs <;> simp_all
      rw [← hres]
      exact StackProg.Exec.loopTrue (by simp [hσ, hp]) e1 e2
    · refine ⟨1, by omega, ?_⟩
      have hpf : pred x = false := by simpa using hp
      simp only [List.dropWhile_cons, List.takeWhile_cons, hpf, Bool.false_eq_true, if_false,
        List.reverse_nil, List.nil_append]
      rw [← hσ, Regs.set_get, Regs.set_get]
      exact StackProg.Exec.loopFalse (by simp [hσ, hpf])

/-! ## size bounds -/

lemma pw_mono {X a b : ℕ} (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right hX h

end NWRed


set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## Binary counters (least significant bit first) -/

def toB (b : Bool) : BSym := if b then .one else .zero
def enc (x : List Bool) : List BSym := x.map toB

@[simp] lemma enc_nil : enc [] = [] := rfl
@[simp] lemma enc_cons (b : Bool) (l : List Bool) : enc (b :: l) = toB b :: enc l := rfl
@[simp] lemma enc_append (l l' : List Bool) : enc (l ++ l') = enc l ++ enc l' := by
  simp [enc]
@[simp] lemma enc_replicate (c : ℕ) (b : Bool) : enc (List.replicate c b) = List.replicate c (toB b) := by
  simp [enc]
@[simp] lemma length_enc (l : List Bool) : (enc l).length = l.length := by simp [enc]
@[simp] lemma toB_true : toB true = .one := rfl
@[simp] lemma toB_false : toB false = .zero := rfl

def incL : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: incL r

def decL : List Bool → List Bool
  | [] => []
  | true :: r => if r = [] then [] else false :: r
  | false :: r => true :: decL r

lemma bit_ne_zero_aux (b : Bool) (n : ℕ) (h : n = 0 → b = true) : Nat.bit b n ≠ 0 := by
  cases b
  · have : n ≠ 0 := fun h0 => by simpa using h h0
    simp [Nat.bit]; omega
  · simp [Nat.bit]

lemma incL_bits (k : ℕ) : incL (Nat.bits k) = Nat.bits (k + 1) := by
  induction k using Nat.binaryRec' with
  | zero => simp [incL]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b
    · have hn0 : n ≠ 0 := fun h => by simpa using hn h
      simp only [incL]
      have : Nat.bit false n + 1 = Nat.bit true n := by
        first | (simp [Nat.bit]; done) | (simp [Nat.bit]; omega)
      rw [this]; exact (Nat.bits_append_bit n true (fun _ => rfl)).symm
    · simp only [incL, ih]
      have : Nat.bit true n + 1 = Nat.bit false (n + 1) := by
        first | (simp [Nat.bit]; done) | (simp [Nat.bit]; omega)
      rw [this]; exact (Nat.bits_append_bit (n + 1) false (fun h => absurd h (Nat.succ_ne_zero n))).symm

lemma bits_eq_nil_iff' (k : ℕ) : Nat.bits k = [] ↔ k = 0 := by
  induction k using Nat.binaryRec' with
  | zero => simp
  | bit b n hn _ =>
    rw [Nat.bits_append_bit _ _ hn]
    simp only [reduceCtorEq, false_iff]
    exact bit_ne_zero_aux b n hn

lemma decL_bits (k : ℕ) : decL (Nat.bits k) = Nat.bits (k - 1) := by
  induction k using Nat.binaryRec' with
  | zero => simp [decL]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b
    · have hn0 : n ≠ 0 := fun h => by simpa using hn h
      simp only [decL, ih]
      have : Nat.bit false n - 1 = Nat.bit true (n - 1) := by simp [Nat.bit]; omega
      rw [this, Nat.bits_append_bit _ _ (fun _ => rfl)]
    · simp only [decL]
      by_cases h0 : n = 0
      · subst h0; simp
      · rw [if_neg (by rw [bits_eq_nil_iff']; exact h0)]
        have : Nat.bit true n - 1 = Nat.bit false n := by simp [Nat.bit]
        rw [this, Nat.bits_append_bit _ _ (by simp [h0])]

lemma len_bits_le (x : ℕ) : (Nat.bits x).length ≤ x := by
  induction x using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    have : n ≠ 0 ∨ b = true := by
      by_cases h : n = 0
      · exact Or.inr (hn h)
      · exact Or.inl h
    cases b <;> simp [Nat.bit] at this ⊢ <;> omega

lemma bits_double (n : ℕ) (hn : n ≠ 0) : Nat.bits (2 * n) = false :: Nat.bits n := by
  have := Nat.bits_append_bit n false (fun h => absurd h hn)
  simpa [Nat.bit] using this

/-- a canonical nonempty bit list has a `true` after its leading zeros -/
lemma bits_split_false (k : ℕ) (hk : k ≠ 0) :
    ∃ c r, Nat.bits k = List.replicate c false ++ true :: r := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨b, n, rfl⟩ : ∃ b n, k = Nat.bit b n := ⟨k.bodd, k.div2, (Nat.bit_bodd_div2 k).symm⟩
    by_cases hc : n = 0 → b = true
    · rw [Nat.bits_append_bit _ _ hc]
      cases b
      · have hn0 : n ≠ 0 := fun h => by simpa using hc h
        obtain ⟨c, r, hr⟩ := ih n (by simp [Nat.bit]; omega) hn0
        exact ⟨c + 1, r, by rw [hr]; simp [List.replicate_succ]⟩
      · exact ⟨0, Nat.bits n, by simp⟩
    · push Not at hc
      obtain ⟨rfl, hb⟩ := hc
      simp at hb; subst hb; simp [Nat.bit] at hk

/-- split off the maximal block of leading `true`s -/
lemma split_true (l : List Bool) :
    ∃ c rest, l = List.replicate c true ++ rest ∧ rest.head? ≠ some true := by
  induction l with
  | nil => exact ⟨0, [], by simp⟩
  | cons b l ih =>
    cases b
    · exact ⟨0, false :: l, by simp⟩
    · obtain ⟨c, rest, h1, h2⟩ := ih
      exact ⟨c + 1, rest, by rw [h1]; simp [List.replicate_succ], h2⟩

lemma incL_rep (c : ℕ) (rest : List Bool) :
    incL (List.replicate c true ++ rest) = List.replicate c false ++ incL rest := by
  induction c with
  | zero => simp
  | succ c ih => simp [List.replicate_succ, incL, ih]

lemma decL_rep (c : ℕ) (r : List Bool) :
    decL (List.replicate c false ++ true :: r) =
      List.replicate c true ++ (if r = [] then [] else false :: r) := by
  induction c with
  | zero => simp [decL]
  | succ c ih => simp [List.replicate_succ, decL, ih]

/-! ## pop-and-push loops -/

def ppAct (a b : Key) (y : BSym) : (Key → Option BSym) → Key → StackAct BSym :=
  fun _ k => if k = a then .pop else if k = b then .push y else .keep

lemma runs_pp (a b : Key) (hab : a ≠ b) (y : BSym) (σ : Regs) :
    Runs (.act (ppAct a b y)) σ ((σ.set a (σ.get a).tail).set b (y :: σ.get b)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act (ppAct a b y) σ.get
  convert e using 1
  funext k
  rw [Regs.get_set, Regs.get_set]
  simp only [StackProg.applyAct, ppAct]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab, StackAct.apply]
  · by_cases h2 : k = a
    · subst h2; simp [StackAct.apply, hab]
    · simp [h1, h2, StackAct.apply]

/-- while the top of `a` is `x`: pop `a`, push `y` onto `b` -/
def whilePP (a b : Key) (x y : BSym) : Prog :=
  .loop (fun h => decide (h a = some x)) (.act (ppAct a b y))

lemma runs_whilePP (a b : Key) (hab : a ≠ b) (x y : BSym) :
    ∀ (c : ℕ) (r : List BSym) (σ : Regs), σ.get a = List.replicate c x ++ r → r.head? ≠ some x →
      Runs (whilePP a b x y) σ ((σ.set a r).set b (List.replicate c y ++ σ.get b)) (3 * c + 1) := by
  intro c
  induction c with
  | zero =>
    intro r σ ha hr
    simp only [List.replicate_zero, List.nil_append] at ha ⊢
    rw [← ha, Regs.set_get, Regs.set_get]
    exact ⟨1, le_rfl, StackProg.Exec.loopFalse (by simp [hd, ha, hr])⟩
  | succ c ih =>
    intro r σ ha hr
    obtain ⟨n, hn, e1⟩ := runs_pp a b hab y σ
    set σ1 := (σ.set a (σ.get a).tail).set b (y :: σ.get b) with hσ1
    have h1 : σ1.get a = List.replicate c x ++ r := by
      rw [hσ1, Regs.get_set, if_neg hab, Regs.get_set_self, ha]; simp [List.replicate_succ]
    obtain ⟨m, hm, e2⟩ := ih r σ1 h1 hr
    refine ⟨1 + n + 1 + m, by omega, ?_⟩
    have hres : (σ1.set a r).set b (List.replicate c y ++ σ1.get b) =
        (σ.set a r).set b (List.replicate (c + 1) y ++ σ.get b) := by
      have hb : σ1.get b = y :: σ.get b := by rw [hσ1, Regs.get_set_self]
      rw [hb, hσ1]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs <;> simp_all [List.replicate_succ']
    rw [← hres]
    exact StackProg.Exec.loopTrue (by simp [hd, ha, List.replicate_succ]) e1 e2

/-! ## increment, decrement, emission -/

/-- increment the counter `X` (scratch `T`, empty before and after) -/
def incProg (X T : Key) : Prog :=
  .seq (whilePP X T .one .zero)
    (.seq (.branch (fun h => decide (h X = some .zero)) (popProg X) skipP)
      (.seq (pushProg X .one) (mvProg T X)))

lemma runs_inc (X T : Key) (hXT : X ≠ T) (σ : Regs) (l : List Bool)
    (hX : σ.get X = enc l) (hT : σ.get T = []) :
    Runs (incProg X T) σ (σ.set X (enc (incL l))) (6 * l.length + 10) := by
  obtain ⟨c, rest, hl, hrest⟩ := split_true l
  subst hl
  have hX' : σ.get X = List.replicate c BSym.one ++ enc rest := by rw [hX]; simp
  have hr : (enc rest).head? ≠ some BSym.one := by
    cases rest with
    | nil => simp
    | cons b r => cases b <;> simp_all
  have e1 := runs_whilePP X T hXT .one .zero c (enc rest) σ hX' hr
  set σ1 := (σ.set X (enc rest)).set T (List.replicate c BSym.zero ++ σ.get T) with hσ1
  have hσ1X : σ1.get X = enc rest := by rw [hσ1, Regs.get_set, if_neg hXT, Regs.get_set_self]
  have hσ1T : σ1.get T = List.replicate c BSym.zero := by rw [hσ1, Regs.get_set_self, hT]; simp
  -- the branch: pop a leading zero
  obtain ⟨σ2, rest', e2, hσ2, hrest'⟩ : ∃ σ2 rest', Runs (.branch (fun h => decide (h X = some .zero)) (popProg X) skipP) σ1 σ2 2 ∧
      σ2 = σ1.set X (enc rest') ∧ incL rest = true :: rest' := by
    cases rest with
    | nil =>
      refine ⟨σ1, [], (runs_skip σ1).brF (by simp [hd, hσ1X]), ?_, by simp [incL]⟩
      rw [← hσ1X, Regs.set_get]
    | cons b r =>
      cases b
      · have hb : Runs (.branch (fun h => decide (h X = some .zero)) (popProg X) skipP) σ1
            (σ1.set X (σ1.get X).tail) 2 := (runs_pop X σ1).brT (by simp [hd, hσ1X])
        have ht : (σ1.get X).tail = enc r := by rw [hσ1X]; rfl
        rw [ht] at hb
        exact ⟨σ1.set X (enc r), r, hb, rfl, by simp [incL]⟩
      · simp at hrest
  have e3 := runs_push X .one σ2
  set σ3 := σ2.set X (BSym.one :: σ2.get X) with hσ3
  have e4 := runs_mv T X (Ne.symm hXT) σ3
  have hfin : (σ3.set T []).set X ((σ3.get T).reverse ++ σ3.get X) =
      σ.set X (enc (incL (List.replicate c true ++ rest))) := by
    rw [incL_rep, hrest']
    have h3T : σ3.get T = List.replicate c BSym.zero := by
      rw [hσ3, Regs.get_set, if_neg (Ne.symm hXT), hσ2, Regs.get_set, if_neg (Ne.symm hXT), hσ1T]
    have h3X : σ3.get X = BSym.one :: enc rest' := by
      rw [hσ3, Regs.get_set_self, hσ2, Regs.get_set_self]
    rw [h3T, h3X, hσ3, hσ2, hσ1]
    apply Regs.ext_get; funext i; simp only [Regs.get_set]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  rw [← hfin]
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  have : (σ3.get T).length = c := by
    rw [hσ3, Regs.get_set, if_neg (Ne.symm hXT), hσ2, Regs.get_set, if_neg (Ne.symm hXT), hσ1T]
    simp
  rw [this]; simp; omega

/-- decrement the counter `X` holding a nonzero canonical value (scratch `T`) -/
def decProg (X T : Key) : Prog :=
  .seq (whilePP X T .zero .one)
    (.seq (popProg X)
      (.seq (.branch (fun h => (h X).isSome) (pushProg X .zero) skipP) (mvProg T X)))

lemma runs_dec (X T : Key) (hXT : X ≠ T) (σ : Regs) (c : ℕ) (r : List Bool)
    (hX : σ.get X = enc (List.replicate c false ++ true :: r)) (hT : σ.get T = []) :
    Runs (decProg X T) σ (σ.set X (enc (decL (List.replicate c false ++ true :: r))))
      (6 * c + 10) := by
  have hX' : σ.get X = List.replicate c BSym.zero ++ enc (true :: r) := by rw [hX]; simp
  have e1 := runs_whilePP X T hXT .zero .one c (enc (true :: r)) σ hX' (by simp)
  set σ1 := (σ.set X (enc (true :: r))).set T (List.replicate c BSym.one ++ σ.get T) with hσ1
  have hσ1X : σ1.get X = BSym.one :: enc r := by
    rw [hσ1, Regs.get_set, if_neg hXT, Regs.get_set_self]; simp
  have e2 := runs_pop X σ1
  set σ2 := σ1.set X (σ1.get X).tail with hσ2
  have hσ2X : σ2.get X = enc r := by rw [hσ2, Regs.get_set_self, hσ1X]; rfl
  obtain ⟨σ3, e3, hσ3⟩ : ∃ σ3, Runs (.branch (fun h => (h X).isSome) (pushProg X .zero) skipP) σ2 σ3 2 ∧
      σ3 = σ2.set X (enc (if r = [] then [] else false :: r)) := by
    by_cases hr : r = []
    · subst hr
      refine ⟨σ2, (runs_skip σ2).brF (by simp [hd, hσ2X]), ?_⟩
      simp only [if_true]; rw [← hσ2X, Regs.set_get]
    · have hb : Runs (.branch (fun h => (h X).isSome) (pushProg X .zero) skipP) σ2
          (σ2.set X (BSym.zero :: σ2.get X)) 2 := (runs_push X .zero σ2).brT (by
          cases r with
          | nil => exact absurd rfl hr
          | cons b r => simp [hd, hσ2X])
      refine ⟨_, hb, ?_⟩
      rw [if_neg hr, hσ2X]; rfl
  have e4 := runs_mv T X (Ne.symm hXT) σ3
  have h3T : σ3.get T = List.replicate c BSym.one := by
    rw [hσ3, Regs.get_set, if_neg (Ne.symm hXT), hσ2, Regs.get_set, if_neg (Ne.symm hXT), hσ1,
      Regs.get_set_self, hT]; simp
  have hfin : (σ3.set T []).set X ((σ3.get T).reverse ++ σ3.get X) =
      σ.set X (enc (decL (List.replicate c false ++ true :: r))) := by
    rw [decL_rep, h3T]
    have h3X : σ3.get X = enc (if r = [] then [] else false :: r) := by
      rw [hσ3, Regs.get_set_self]
    rw [h3X, hσ3, hσ2, hσ1]
    apply Regs.ext_get; funext i; simp only [Regs.get_set]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  rw [← hfin]
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  rw [h3T]; simp; omega

/-- append `encNat` of the counter `X` to the reversed output `W` (scratch `T`, `sc`) -/
def emitProg (X : Key) : Prog :=
  .seq (copyProg X .T .sc) (.seq (mvProg .T .W) (pushProg .W .sep))

lemma runs_emit (X : Key) (h1 : X ≠ .T) (h2 : X ≠ .sc) (h3 : X ≠ .W) (σ : Regs)
    (hT : σ.T = []) (hsc : σ.sc = []) :
    Runs (emitProg X) σ { σ with W := BSym.sep :: (σ.get X).reverse ++ σ.W }
      (9 * (σ.get X).length + 7) := by
  have e1 := runs_copy X .T .sc h1 h2 (by decide) σ hsc
  set σ1 := σ.set .T (σ.get X ++ σ.get .T) with hσ1
  have e2 := runs_mv .T .W (by decide) σ1
  set σ2 := (σ1.set .T []).set .W ((σ1.get .T).reverse ++ σ1.get .W) with hσ2
  have e3 := runs_push .W .sep σ2
  have hfin : σ2.set .W (BSym.sep :: σ2.get .W) = { σ with W := BSym.sep :: (σ.get X).reverse ++ σ.W } := by
    rw [hσ2, hσ1]
    apply Regs.ext_get; funext i
    simp only [Regs.get_set]
    have hXW : σ.get X = σ.get X := rfl
    cases i <;> simp_all [Regs.get] <;> rfl
  rw [← hfin]
  refine (e1.seq (e2.seq e3)).mono ?_
  have hl : (σ1.get .T).length = (σ.get X).length := by
    rw [hσ1, Regs.get_set_self, show σ.get .T = [] from hT]; simp
  rw [hl]; omega

end NWRed


set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## more combinators -/

lemma Runs.congr {p : Prog} {σ τ τ' : Regs} {B : ℕ} (h : Runs p σ τ B) (e : τ = τ') :
    Runs p σ τ' B := e ▸ h

lemma Runs.loopT {t : (Key → Option BSym) → Bool} {body : Prog} {σ σ' τ : Regs} {B1 B2 : ℕ}
    (ht : t (hd σ) = true) (h1 : Runs body σ σ' B1) (h2 : Runs (.loop t body) σ' τ B2) :
    Runs (.loop t body) σ τ (B1 + B2 + 2) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, e'⟩ := h2
  exact ⟨1 + n + 1 + m, by omega, StackProg.Exec.loopTrue ht e e'⟩

lemma Runs.loopF {t : (Key → Option BSym) → Bool} {body : Prog} {σ : Regs}
    (ht : t (hd σ) = false) : Runs (.loop t body) σ σ 1 :=
  ⟨1, le_rfl, StackProg.Exec.loopFalse ht⟩

def Regs.empty : Regs :=
  ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩

def initR (w : List BSym) : Regs := { Regs.empty with inp := w }

def gate (p : Prog) : Prog := .branch (fun h => (h .bad).isNone) p skipP

lemma runs_gate_ok {p : Prog} {σ τ : Regs} {B : ℕ} (hb : σ.bad = []) (h : Runs p σ τ B) :
    Runs (gate p) σ τ (B + 1) :=
  Runs.brT (by simp [hd, Regs.get, hb]) h

lemma runs_gate_skip {p : Prog} {σ : Regs} (hb : σ.bad ≠ []) : Runs (gate p) σ σ 2 :=
  Runs.brF (by
    cases h : σ.bad with
    | nil => exact absurd h hb
    | cons a l => simp [hd, Regs.get, h]) (runs_skip σ)

/-! ## Phase 1-3: the number `n` -/

def isDigB : BSym → Bool
  | .one => true
  | .zero => true
  | _ => false

def pP1 : Prog := mvwProg .inp .A isDigB

def pP2 : Prog :=
  .branch (fun h => decide (h .inp = some .sep) && decide (h .A ≠ some .zero)) (popProg .inp)
    (pushProg .bad .one)

def pP3 : Prog := mvProg .A .Bn

/-- the digits read and the rest -/
def digs (w : List BSym) : List BSym := w.takeWhile isDigB
def rest (w : List BSym) : List BSym := w.dropWhile isDigB

/-- the check of phase 2 -/
def numOK (w : List BSym) : Prop :=
  (rest w).head? = some .sep ∧ (digs w).getLast? ≠ some .zero

instance (w : List BSym) : Decidable (numOK w) := by unfold numOK; infer_instance

def st3 (w : List BSym) : Regs := { Regs.empty with inp := (rest w).tail, Bn := digs w }

lemma runs_P123 (w : List BSym) :
    ∃ τ, Runs (.seq pP1 (.seq pP2 pP3)) (initR w) τ (6 * w.length + 10) ∧
      (numOK w → τ = st3 w) ∧ (¬ numOK w → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_mvw .inp .A (by decide) isDigB w (initR w) rfl
  set σ1 := ((initR w).set .inp (w.dropWhile isDigB)).set .A
    ((w.takeWhile isDigB).reverse ++ (initR w).get .A) with hσ1
  have h1i : σ1.inp = rest w := rfl
  have h1A : σ1.A = (digs w).reverse := by simp [hσ1, Regs.set, Regs.get, initR, Regs.empty, digs]
  by_cases hok : numOK w
  · obtain ⟨hs, hl⟩ := hok
    have e2 : Runs pP2 σ1 (σ1.set .inp (σ1.get .inp).tail) 2 := by
      refine (runs_pop .inp σ1).brT ?_
      simp only [hd, Regs.get, h1i, hs, h1A, List.head?_reverse, decide_true, Bool.true_and,
        decide_eq_true_eq]
      exact hl
    set σ2 := σ1.set .inp (σ1.get .inp).tail with hσ2
    have e3 := runs_mv .A .Bn (by decide) σ2
    refine ⟨_, (e1.seq (e2.seq e3)).mono ?_, fun _ => ?_, fun h => absurd ⟨hs, hl⟩ h⟩
    · have : (σ2.get .A).length ≤ w.length := by
        simp only [hσ2, Regs.set, Regs.get, h1A, List.length_reverse, digs]
        exact (List.takeWhile_sublist _).length_le
      omega
    · simp only [hσ2, Regs.set, Regs.get, h1A, h1i, st3, List.reverse_reverse]
      simp [hσ1, Regs.set, Regs.get, initR, Regs.empty, rest]
  · have e2 : Runs pP2 σ1 (σ1.set .bad (.one :: σ1.get .bad)) 2 := by
      refine (runs_push .bad .one σ1).brF ?_
      simp only [hd, Regs.get, h1i, h1A, List.head?_reverse]
      unfold numOK at hok
      by_cases hs : (rest w).head? = some .sep
      · have hl : (digs w).getLast? = some .zero := by
          by_contra h; exact hok ⟨hs, h⟩
        simp [hs, hl]
      · simp [hs]
    set σ2 := σ1.set .bad (.one :: σ1.get .bad) with hσ2
    have e3 := runs_mv .A .Bn (by decide) σ2
    refine ⟨_, (e1.seq (e2.seq e3)).mono ?_, fun h => absurd h hok, ?_⟩
    · have : (σ2.get .A).length ≤ w.length := by
        simp only [hσ2, Regs.set, Regs.get, h1A, List.length_reverse, digs]
        exact (List.takeWhile_sublist _).length_le
      omega
    · intro _
      simp [hσ2, Regs.set, Regs.get]
      simp [hσ1, Regs.set, Regs.get, initR, Regs.empty]

/-! ## Phase 4: the entries -/

def tokB : Bool → List BSym
  | false => [.sep]
  | true => [.one, .sep]

def tokP : Bool → List BSym → Option (List Bool)
  | false, [] => some []
  | true, [] => none
  | false, .sep :: r => (tokP false r).map (false :: ·)
  | false, .one :: r => tokP true r
  | false, _ :: _ => none
  | true, .sep :: r => (tokP false r).map (true :: ·)
  | true, _ :: _ => none

def pdS : Bool → List BSym
  | false => []
  | true => [.one]

def tokBody : Prog :=
  .branch (fun h => (h .Pd).isNone)
    (.branch (fun h => decide (h .inp = some .sep)) (.seq (popProg .inp) (pushProg .A .zero))
      (.branch (fun h => decide (h .inp = some .one)) (.seq (popProg .inp) (pushProg .Pd .one))
        (pushProg .bad .one)))
    (.branch (fun h => decide (h .inp = some .sep))
      (.seq (popProg .inp) (.seq (popProg .Pd) (pushProg .A .one)))
      (pushProg .bad .one))

def tokLoop : Prog := .loop (fun h => (h .inp).isSome && (h .bad).isNone) tokBody

lemma tb_sep0 (σ : Regs) (r : List BSym) (hi : σ.inp = .sep :: r) (hp : σ.Pd = []) :
    Runs tokBody σ { σ with inp := r, A := .zero :: σ.A } 7 := by
  have e : Runs (.seq (popProg .inp) (pushProg .A .zero)) σ { σ with inp := r, A := .zero :: σ.A } 3 :=
    ((runs_pop .inp σ).seq (runs_push .A .zero _)).congr (by simp [Regs.set, Regs.get, hi])
  unfold tokBody
  refine (Runs.brT ?_ (Runs.brT ?_ e)).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi]

lemma tb_one0 (σ : Regs) (r : List BSym) (hi : σ.inp = .one :: r) (hp : σ.Pd = []) :
    Runs tokBody σ { σ with inp := r, Pd := [.one] } 7 := by
  have e : Runs (.seq (popProg .inp) (pushProg .Pd .one)) σ { σ with inp := r, Pd := [.one] } 3 :=
    ((runs_pop .inp σ).seq (runs_push .Pd .one _)).congr (by simp [Regs.set, Regs.get, hi, hp])
  unfold tokBody
  refine (Runs.brT ?_ (Runs.brF ?_ (Runs.brT ?_ e))).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi]
  · simp [hd, Regs.get, hi]

lemma tb_bad0 (σ : Regs) (x : BSym) (r : List BSym) (hi : σ.inp = x :: r) (hp : σ.Pd = [])
    (hx : x ≠ .sep) (hx' : x ≠ .one) :
    Runs tokBody σ (σ.set .bad (.one :: σ.get .bad)) 7 := by
  unfold tokBody
  refine (Runs.brT ?_ (Runs.brF ?_ (Runs.brF ?_ (runs_push .bad .one σ)))).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi, hx]
  · simp [hd, Regs.get, hi, hx']

lemma tb_sep1 (σ : Regs) (r : List BSym) (hi : σ.inp = .sep :: r) (hp : σ.Pd = [.one]) :
    Runs tokBody σ { σ with inp := r, Pd := [], A := .one :: σ.A } 7 := by
  have e : Runs (.seq (popProg .inp) (.seq (popProg .Pd) (pushProg .A .one))) σ
      { σ with inp := r, Pd := [], A := .one :: σ.A } 5 :=
    ((runs_pop .inp σ).seq ((runs_pop .Pd _).seq (runs_push .A .one _))).congr
      (by simp [Regs.set, Regs.get, hi, hp])
  unfold tokBody
  refine (Runs.brF ?_ (Runs.brT ?_ e)).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi]

lemma tb_bad1 (σ : Regs) (x : BSym) (r : List BSym) (hi : σ.inp = x :: r) (hp : σ.Pd = [.one])
    (hx : x ≠ .sep) :
    Runs tokBody σ (σ.set .bad (.one :: σ.get .bad)) 7 := by
  unfold tokBody
  refine (Runs.brF ?_ (Runs.brF ?_ (runs_push .bad .one σ))).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi, hx]

lemma tok_loop : ∀ (l : List BSym) (pd : Bool) (σ : Regs), σ.inp = l → σ.bad = [] →
    σ.Pd = pdS pd →
    ∃ τ, Runs tokLoop σ τ (10 * l.length + 1) ∧ τ.out = σ.out ∧
      (∀ bs, tokP pd l = some bs →
        τ = { σ with inp := [], Pd := [], A := (enc bs).reverse ++ σ.A }) ∧
      (tokP pd l = none → τ.bad ≠ [] ∨ τ.Pd ≠ []) := by
  intro l
  induction l with
  | nil =>
    intro pd σ hi hb hp
    refine ⟨σ, (Runs.loopF (by simp [hd, Regs.get, hi])), rfl, ?_, ?_⟩
    · intro bs h
      cases pd
      · simp [tokP] at h; subst h; cases σ; simp_all [pdS]
      · simp [tokP] at h
    · intro h; cases pd
      · simp [tokP] at h
      · right; simp [hp, pdS]
  | cons x r ih =>
    intro pd σ hi hb hp
    have ht : (fun h : Key → Option BSym => (h .inp).isSome && (h .bad).isNone) (hd σ) = true := by
      simp [hd, Regs.get, hi, hb]
    -- the bad case
    have badCase : ∀ (hbody : Runs tokBody σ (σ.set .bad (.one :: σ.get .bad)) 7),
        ∃ τ, Runs tokLoop σ τ (10 * (x :: r).length + 1) ∧ τ.out = σ.out ∧
          (tokP pd (x :: r) = none → τ.bad ≠ [] ∨ τ.Pd ≠ []) := by
      intro hbody
      have hstop : (fun h : Key → Option BSym => (h .inp).isSome && (h .bad).isNone)
          (hd (σ.set .bad (.one :: σ.get .bad))) = false := by
        simp [hd, Regs.get, Regs.set]
      refine ⟨_, (Runs.loopT ht hbody (Runs.loopF hstop)).mono (by simp; omega), rfl, ?_⟩
      intro _; left; simp [Regs.set, Regs.get]
    cases pd
    · -- no pending digit
      have hp0 : σ.Pd = [] := hp
      cases x with
      | sep =>
        have hbody := tb_sep0 σ r hi hp0
        obtain ⟨τ, e, ho, hs, hn⟩ := ih false { σ with inp := r, A := .zero :: σ.A } rfl hb hp
        refine ⟨τ, (Runs.loopT ht hbody e).mono (by simp; omega), ho, ?_, ?_⟩
        · intro bs h
          simp only [tokP, Option.map_eq_some_iff] at h
          obtain ⟨bs', h1, rfl⟩ := h
          rw [hs bs' h1]; cases σ; simp_all
        · intro h; simp only [tokP, Option.map_eq_none_iff] at h; exact hn h
      | one =>
        have hbody := tb_one0 σ r hi hp0
        obtain ⟨τ, e, ho, hs, hn⟩ := ih true { σ with inp := r, Pd := [.one] } rfl hb rfl
        refine ⟨τ, (Runs.loopT ht hbody e).mono (by simp; omega), ho, ?_, ?_⟩
        · intro bs h
          rw [hs bs h]
        · intro h; exact hn h
      | zero =>
        obtain ⟨τ, e, ho, hn⟩ := badCase (tb_bad0 σ _ r hi hp0 (by decide) (by decide))
        exact ⟨τ, e, ho, fun bs h => by simp [tokP] at h, hn⟩
      | minus =>
        obtain ⟨τ, e, ho, hn⟩ := badCase (tb_bad0 σ _ r hi hp0 (by decide) (by decide))
        exact ⟨τ, e, ho, fun bs h => by simp [tokP] at h, hn⟩
    · -- a pending digit `1`
      have hp1 : σ.Pd = [.one] := hp
      by_cases hx : x = .sep
      · subst hx
        have hbody := tb_sep1 σ r hi hp1
        obtain ⟨τ, e, ho, hs, hn⟩ :=
          ih false { σ with inp := r, Pd := [], A := .one :: σ.A } rfl hb rfl
        refine ⟨τ, (Runs.loopT ht hbody e).mono (by simp; omega), ho, ?_, ?_⟩
        · intro bs h
          simp only [tokP, Option.map_eq_some_iff] at h
          obtain ⟨bs', h1, rfl⟩ := h
          rw [hs bs' h1]; cases σ; simp_all
        · intro h; simp only [tokP, Option.map_eq_none_iff] at h; exact hn h
      · obtain ⟨τ, e, ho, hn⟩ := badCase (tb_bad1 σ x r hi hp1 hx)
        refine ⟨τ, e, ho, fun bs h => ?_, hn⟩
        cases x <;> simp_all [tokP]

end NWRed


set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## tokens: pure facts -/

lemma tokP_some : ∀ (l : List BSym) (pd : Bool) (bs : List Bool), tokP pd l = some bs →
    (if pd then BSym.one :: l else l) = bs.flatMap tokB := by
  intro l
  induction l with
  | nil => intro pd bs h; cases pd <;> simp_all [tokP]
  | cons x r ih =>
    intro pd bs h
    cases pd with
    | false =>
      cases x with
      | sep =>
        simp only [tokP, Option.map_eq_some_iff] at h
        obtain ⟨bs', h1, rfl⟩ := h
        have := ih false bs' h1
        simp only [Bool.false_eq_true, if_false] at this ⊢
        simp [this, tokB]
      | one =>
        simp only [tokP] at h
        have := ih true bs h
        simpa using this
      | zero => simp [tokP] at h
      | minus => simp [tokP] at h
    | true =>
      cases x with
      | sep =>
        simp only [tokP, Option.map_eq_some_iff] at h
        obtain ⟨bs', h1, rfl⟩ := h
        have := ih false bs' h1
        simp only [Bool.false_eq_true, if_false] at this ⊢
        simp [this, tokB]
      | one => simp [tokP] at h
      | zero => simp [tokP] at h
      | minus => simp [tokP] at h

lemma tokP_flat (bs : List Bool) : tokP false (bs.flatMap tokB) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [tokB, tokP, ih]

lemma length_flat_tokB (bs : List Bool) : bs.length ≤ (bs.flatMap tokB).length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    cases b <;> simp only [tokB, List.length_cons, List.length_nil] <;> omega

lemma tokP_len (l : List BSym) (bs : List Bool) (h : tokP false l = some bs) :
    bs.length ≤ l.length := by
  have := tokP_some l false bs h
  simp at this; rw [this]; exact length_flat_tokB bs

/-! ## Phase 4 -/

def pdCheck : Prog := .branch (fun h => (h .Pd).isSome) (pushProg .bad .one) skipP

def pP4 : Prog := .seq tokLoop (.seq pdCheck (gate (mvProg .A .M)))

lemma runs_P4 (σ : Regs) (hb : σ.bad = []) (hp : σ.Pd = []) (hA : σ.A = []) (hM : σ.M = []) :
    ∃ τ, Runs pP4 σ τ (13 * σ.inp.length + 8) ∧
      (∀ bs, tokP false σ.inp = some bs → τ = { σ with inp := [], M := enc bs }) ∧
      (tokP false σ.inp = none → τ.bad ≠ [] ∧ τ.out = σ.out) := by
  obtain ⟨τ, e, ho, hs, hn⟩ := tok_loop σ.inp false σ rfl hb hp
  by_cases hsome : ∃ bs, tokP false σ.inp = some bs
  · obtain ⟨bs, hbs⟩ := hsome
    have hτ := hs bs hbs
    have e2 : Runs pdCheck τ τ 2 := (runs_skip τ).brF (by simp [hd, Regs.get, hτ])
    have e3 := runs_gate_ok (p := mvProg .A .M) (by rw [hτ]; exact hb) (runs_mv .A .M (by decide) τ)
    refine ⟨_, (e.seq (e2.seq e3)).mono ?_, ?_, ?_⟩
    · have : (τ.get .A).length ≤ σ.inp.length := by
        rw [hτ]; simp only [Regs.get, hA, List.append_nil, List.length_reverse, length_enc]
        exact tokP_len _ _ hbs
      omega
    · intro bs' h'
      rw [hbs] at h'; cases h'
      rw [hτ]; simp [Regs.set, Regs.get, hA, hM, hp]
    · intro h; rw [hbs] at h; cases h
  · have hnone : tokP false σ.inp = none := by
      cases h : tokP false σ.inp with
      | none => rfl
      | some bs => exact absurd ⟨bs, h⟩ hsome
    rcases hn hnone with hbad | hpd
    · have e2 : ∃ τ2, Runs pdCheck τ τ2 2 ∧ τ2.bad ≠ [] ∧ τ2.out = τ.out := by
        by_cases hP : τ.Pd = []
        · exact ⟨τ, (runs_skip τ).brF (by simp [hd, Regs.get, hP]), hbad, rfl⟩
        · refine ⟨_, (runs_push .bad .one τ).brT (by
            cases h : τ.Pd with
            | nil => exact absurd h hP
            | cons a l => simp [hd, Regs.get, h]), by simp [Regs.set], rfl⟩
      obtain ⟨τ2, e2, hb2, ho2⟩ := e2
      refine ⟨τ2, (e.seq (e2.seq (runs_gate_skip hb2))).mono (by omega), ?_, ?_⟩
      · intro bs h; rw [hnone] at h; cases h
      · intro _; exact ⟨hb2, by rw [ho2, ho]⟩
    · have e2 : Runs pdCheck τ (τ.set .bad (.one :: τ.get .bad)) 2 :=
        (runs_push .bad .one τ).brT (by
          cases h : τ.Pd with
          | nil => exact absurd h hpd
          | cons a l => simp [hd, Regs.get, h])
      have hb2 : (τ.set .bad (.one :: τ.get .bad)).bad ≠ [] := by simp [Regs.set]
      refine ⟨_, (e.seq (e2.seq (runs_gate_skip hb2))).mono (by omega), ?_, ?_⟩
      · intro bs h; rw [hnone] at h; cases h
      · intro _; exact ⟨hb2, by simp [Regs.set, ho]⟩

/-! ## Phase 6: the unary form of `n`, with fuel -/

def fuelBody : Prog := .seq (popProg .F) (.seq (pushProg .N .one) (decProg .Bt .T))

def fuelLoop : Prog := .loop (fun h => (h .Bt).isSome && (h .F).isSome) fuelBody

def btCheck : Prog := .branch (fun h => (h .Bt).isSome) (pushProg .bad .one) skipP

def pP6 : Prog :=
  .seq (.seq (copyProg .M .F .sc) (copyProg .Bn .Bt .sc)) (.seq fuelLoop (.seq btCheck (clearProg .F)))

/-- the register file once `n` and the entries are known -/
def st4 (n : ℕ) (bs : List Bool) : Regs := { Regs.empty with Bn := enc (Nat.bits n), M := enc bs }

def st6 (n : ℕ) (bs : List Bool) : Regs :=
  { Regs.empty with Bn := enc (Nat.bits n), M := enc bs, N := List.replicate n .one }

def fuelSt (n : ℕ) (bs : List Bool) (j : ℕ) : Regs :=
  { Regs.empty with
    Bn := enc (Nat.bits n)
    M := enc bs
    F := (enc bs).drop j
    Bt := enc (Nat.bits (n - j))
    N := List.replicate j .one }

lemma len_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

lemma fuel_step (n : ℕ) (bs : List Bool) (j : ℕ) (hj : j < n) (hj' : j < bs.length) :
    Runs fuelBody (fuelSt n bs j) (fuelSt n bs (j + 1)) (6 * (Nat.bits n).length + 20) := by
  obtain ⟨c, r, hcr⟩ := bits_split_false (n - j) (by omega)
  have e1 := runs_pop .F (fuelSt n bs j)
  have e2 := runs_push .N .one ((fuelSt n bs j).set .F ((fuelSt n bs j).get .F).tail)
  set σ2 := ((fuelSt n bs j).set .F ((fuelSt n bs j).get .F).tail).set .N
    (.one :: (((fuelSt n bs j).set .F ((fuelSt n bs j).get .F).tail).get .N)) with hσ2
  have e3 := runs_dec .Bt .T (by decide) σ2 c r (by simp [hσ2, Regs.set, Regs.get, fuelSt, hcr])
    (by simp [hσ2, Regs.set, Regs.get, fuelSt, Regs.empty])
  have hres : σ2.set .Bt (enc (decL (List.replicate c false ++ true :: r))) = fuelSt n bs (j + 1) := by
    rw [← hcr, decL_bits]
    have h1 : n - j - 1 = n - (j + 1) := by omega
    simp only [hσ2, Regs.set, Regs.get, fuelSt, List.tail_drop, List.replicate_succ, h1]
  refine ((e1.seq (e2.seq e3)).congr hres).mono ?_
  have : c ≤ (Nat.bits n).length := by
    have h1 : c ≤ (Nat.bits (n - j)).length := by rw [hcr]; simp
    exact le_trans h1 (len_bits_mono (by omega))
  omega

end NWRed


set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

lemma enc_bits_ne_nil {k : ℕ} (hk : k ≠ 0) : enc (Nat.bits k) ≠ [] := by
  intro h
  have : Nat.bits k = [] := by simpa [enc] using h
  exact hk ((bits_eq_nil_iff' k).1 this)

lemma isSome_head_of_ne_nil {l : List BSym} (h : l ≠ []) : l.head?.isSome = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

lemma runs_fuelLoop (n : ℕ) (bs : List Bool) :
    Runs fuelLoop (fuelSt n bs 0) (fuelSt n bs (min n bs.length))
      (min n bs.length * (6 * (Nat.bits n).length + 22) + 1) := by
  refine Runs.loopU _ fuelBody (fuelSt n bs) _ _ (fun j hj => ⟨?_, fuel_step n bs j ?_ ?_⟩) ?_
  · have h1 : (fuelSt n bs j).Bt ≠ [] := enc_bits_ne_nil (by omega)
    have h2 : (fuelSt n bs j).F ≠ [] := by
      simp only [fuelSt]; intro h; rw [List.drop_eq_nil_iff] at h; simp at h; omega
    simp only [hd, Regs.get, isSome_head_of_ne_nil h1, isSome_head_of_ne_nil h2, Bool.and_true]
  · omega
  · omega
  · by_cases h : n ≤ bs.length
    · rw [min_eq_left h]; simp [hd, Regs.get, fuelSt, enc]
    · rw [min_eq_right (by omega)]; simp [hd, Regs.get, fuelSt]

lemma runs_P6 (n : ℕ) (bs : List Bool) (L : ℕ) (hL1 : bs.length ≤ L) (hL2 : (Nat.bits n).length ≤ L) :
    ∃ τ, Runs pP6 (st4 n bs) τ (60 * (L + 1) ^ 2) ∧
      (n ≤ bs.length → τ = st6 n bs) ∧ (bs.length < n → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_copy .M .F .sc (by decide) (by decide) (by decide) (st4 n bs) rfl
  have e2 := runs_copy .Bn .Bt .sc (by decide) (by decide) (by decide)
    ((st4 n bs).set .F ((st4 n bs).get .M ++ (st4 n bs).get .F)) rfl
  have h0 : ((st4 n bs).set .F ((st4 n bs).get .M ++ (st4 n bs).get .F)).set .Bt
      (((st4 n bs).set .F ((st4 n bs).get .M ++ (st4 n bs).get .F)).get .Bn ++
        ((st4 n bs).set .F ((st4 n bs).get .M ++ (st4 n bs).get .F)).get .Bt) = fuelSt n bs 0 := by
    simp [st4, fuelSt, Regs.set, Regs.get, Regs.empty]
  have e12 := (e1.seq e2).congr h0
  have e3 := runs_fuelLoop n bs
  have hb1 : (6 * ((st4 n bs).get .M).length + 3) = 6 * bs.length + 3 := by simp [st4, Regs.get]
  have hb2 : (6 * (((st4 n bs).set .F ((st4 n bs).get .M ++ (st4 n bs).get .F)).get .Bn).length + 3) =
      6 * (Nat.bits n).length + 3 := by simp [st4, Regs.get, Regs.set]
  rw [hb1, hb2] at e12
  have hm : min n bs.length * (6 * (Nat.bits n).length + 22) ≤ L * (6 * L + 22) :=
    Nat.mul_le_mul (le_trans (min_le_right _ _) hL1) (by omega)
  by_cases h : n ≤ bs.length
  · have hmin : min n bs.length = n := min_eq_left h
    have hBt : (fuelSt n bs (min n bs.length)).Bt = [] := by rw [hmin]; simp [fuelSt, enc]
    have e4 : Runs btCheck (fuelSt n bs (min n bs.length)) (fuelSt n bs (min n bs.length)) 2 :=
      (runs_skip _).brF (by simp [hd, Regs.get, hBt])
    have e5 := runs_clear .F (fuelSt n bs (min n bs.length))
    have hfin : (fuelSt n bs (min n bs.length)).set .F [] = st6 n bs := by
      simp [fuelSt, st6, Regs.set, hmin, enc, Regs.empty]
    refine ⟨_, ((e12.seq (e3.seq (e4.seq e5))).congr hfin).mono ?_, fun _ => rfl, fun h' => by omega⟩
    have hF : ((fuelSt n bs (min n bs.length)).get .F).length ≤ L := by
      simp [fuelSt, Regs.get]; omega
    nlinarith
  · have hmin : min n bs.length = bs.length := min_eq_right (by omega)
    have hne : (fuelSt n bs (min n bs.length)).Bt ≠ [] := enc_bits_ne_nil (by omega)
    have e4 : Runs btCheck (fuelSt n bs (min n bs.length))
        ((fuelSt n bs (min n bs.length)).set .bad (.one :: (fuelSt n bs (min n bs.length)).get .bad)) 2 :=
      (runs_push .bad .one _).brT (by simp only [hd, Regs.get]; exact isSome_head_of_ne_nil hne)
    have e5 := runs_clear .F
      ((fuelSt n bs (min n bs.length)).set .bad (.one :: (fuelSt n bs (min n bs.length)).get .bad))
    refine ⟨_, (e12.seq (e3.seq (e4.seq e5))).mono ?_, fun h' => absurd h' h, fun _ => ?_⟩
    · have hF : (((fuelSt n bs (min n bs.length)).set .bad
          (.one :: (fuelSt n bs (min n bs.length)).get .bad)).get .F).length ≤ L := by
        simp [fuelSt, Regs.get, Regs.set]; omega
      nlinarith
    · simp [Regs.set, Regs.get, fuelSt, Regs.empty]

/-! ## Phase 7: the number of entries is `n * n` -/

def zxCheck : Prog := .branch (fun h => (h .Z).isSome || (h .X).isSome) (pushProg .bad .one) skipP

def pP7a : Prog :=
  .seq (copyProg .N .R .sc)
    (.seq (repProg .N .Z .R .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (.seq (copyProg .M .X .sc) (syncPopProg .Z .X)))

def pP7 : Prog := .seq pP7a (.seq zxCheck (.seq (clearProg .Z) (clearProg .X)))

def st7a (n : ℕ) (bs : List Bool) : Regs :=
  { st6 n bs with
    Z := (List.replicate (n * n) BSym.one).drop (min (n * n) bs.length)
    X := (enc bs).drop (min (n * n) bs.length) }

lemma flatten_rep_rep (n : ℕ) (x : BSym) :
    (List.replicate n (List.replicate n x)).flatten = List.replicate (n * n) x := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [List.length_flatten, List.sum_replicate, Nat.mul_comm], ?_⟩
  intro b hb
  rw [List.mem_flatten] at hb
  obtain ⟨l, hl, hb⟩ := hb
  rw [List.mem_replicate] at hl
  rw [hl.2] at hb
  exact (List.mem_replicate.1 hb).2

lemma runs_P7a (n : ℕ) (bs : List Bool) (L : ℕ) (hL1 : bs.length ≤ L) (hn : n ≤ bs.length) :
    Runs pP7a (st6 n bs) (st7a n bs) (30 * (L + 1) ^ 2) := by
  have e1 := runs_copy .N .R .sc (by decide) (by decide) (by decide) (st6 n bs) rfl
  set σ1 := (st6 n bs).set .R ((st6 n bs).get .N ++ (st6 n bs).get .R) with hσ1
  have e2 := runs_rep .N .Z .R .sc (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ1 rfl
  set σ2 := (σ1.set .R []).set .Z ((List.replicate (σ1.get .R).length (σ1.get .N)).flatten ++ σ1.get .Z)
    with hσ2
  have e3 := runs_copy .M .X .sc (by decide) (by decide) (by decide) σ2 rfl
  set σ3 := σ2.set .X (σ2.get .M ++ σ2.get .X) with hσ3
  have e4 := runs_syncpop .Z .X (by decide) σ3
  have h3Z : σ3.get .Z = List.replicate (n * n) BSym.one := by
    simp [hσ3, hσ2, hσ1, Regs.set, Regs.get, st6, Regs.empty, flatten_rep_rep]
  have h3X : σ3.get .X = enc bs := by
    simp [hσ3, hσ2, hσ1, Regs.set, Regs.get, st6, Regs.empty]
  rw [h3Z, h3X] at e4
  have hfin : (σ3.set .Z ((List.replicate (n * n) BSym.one).drop
      (min (List.replicate (n * n) BSym.one).length (enc bs).length))).set .X
      ((enc bs).drop (min (List.replicate (n * n) BSym.one).length (enc bs).length)) = st7a n bs := by
    simp [hσ3, hσ2, hσ1, Regs.set, Regs.get, st6, st7a, Regs.empty]
  refine ((e1.seq (e2.seq (e3.seq e4))).congr hfin).mono ?_
  have l1 : ((st6 n bs).get .N).length = n := by simp [st6, Regs.get]
  have l2 : (σ1.get .N).length = n := by simp [hσ1, st6, Regs.get, Regs.set]
  have l3 : (σ1.get .R).length = n := by simp [hσ1, st6, Regs.get, Regs.set, Regs.empty]
  have l4 : (σ2.get .M).length = bs.length := by simp [hσ2, hσ1, st6, Regs.get, Regs.set]
  rw [l1, l2, l3, l4]
  simp only [List.length_replicate, length_enc]
  have : min (n * n) bs.length ≤ L := le_trans (min_le_right _ _) hL1
  nlinarith

lemma runs_P7 (n : ℕ) (bs : List Bool) (L : ℕ) (hL1 : bs.length ≤ L) (hn : n ≤ bs.length) :
    ∃ τ, Runs pP7 (st6 n bs) τ (60 * (L + 1) ^ 2) ∧
      (n * n = bs.length → τ = st6 n bs) ∧ (n * n ≠ bs.length → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_P7a n bs L hL1 hn
  by_cases h : n * n = bs.length
  · have hZ : (st7a n bs).Z = [] := by simp [st7a, h]
    have hX : (st7a n bs).X = [] := by simp [st7a, h]
    have e2 : Runs zxCheck (st7a n bs) (st7a n bs) 2 :=
      (runs_skip _).brF (by simp [hd, Regs.get, hZ, hX])
    have e3 := runs_clear .Z (st7a n bs)
    have e4 := runs_clear .X ((st7a n bs).set .Z [])
    have hfin : ((st7a n bs).set .Z []).set .X [] = st6 n bs := by
      simp [st7a, st6, Regs.set, Regs.empty, h]
    refine ⟨_, ((e1.seq (e2.seq (e3.seq e4))).congr hfin).mono ?_, fun _ => rfl, fun h' => absurd h h'⟩
    simp [Regs.get, Regs.set, hZ, hX]; nlinarith
  · have hne : (st7a n bs).Z ≠ [] ∨ (st7a n bs).X ≠ [] := by
      by_cases hle : n * n ≤ bs.length
      · right; simp [st7a, min_eq_left hle]; omega
      · left; simp [st7a, min_eq_right (show bs.length ≤ n * n by omega)]; omega
    have e2 : Runs zxCheck (st7a n bs) ((st7a n bs).set .bad (.one :: (st7a n bs).get .bad)) 2 := by
      refine (runs_push .bad .one _).brT ?_
      rcases hne with h1 | h1
      · simp only [hd, Regs.get, isSome_head_of_ne_nil h1, Bool.true_or]
      · simp only [hd, Regs.get, isSome_head_of_ne_nil h1, Bool.or_true]
    set σ2 := (st7a n bs).set .bad (.one :: (st7a n bs).get .bad) with hσ2
    have e3 := runs_clear .Z σ2
    have e4 := runs_clear .X (σ2.set .Z [])
    refine ⟨_, (e1.seq (e2.seq (e3.seq e4))).mono ?_, fun h' => absurd h' h, fun _ => ?_⟩
    · have hZl : (σ2.get .Z).length ≤ n * n := by simp [hσ2, Regs.get, Regs.set, st7a]
      have hXl : ((σ2.set .Z []).get .X).length ≤ bs.length := by
        simp [hσ2, Regs.get, Regs.set, st7a]
      have : n * n ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · simp [hσ2, Regs.set, Regs.get, st7a, st6, Regs.empty]

end NWRed


set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## the input format: `n` in binary, then the `n * n` entries -/

def code (n : ℕ) (bs : List Bool) : List BSym := enc (Nat.bits n) ++ BSym.sep :: bs.flatMap tokB

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

lemma bval_bits (n : ℕ) : bval (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval]
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval, ih]

lemma bits_bval (l : List Bool) (h : l.getLast? ≠ some false) : Nat.bits (bval l) = l := by
  induction l with
  | nil => simp [bval]
  | cons b t ih =>
    by_cases ht : t = []
    · subst ht
      have hb : b = true := by cases b <;> simp_all
      subst hb
      exact Nat.bits_append_bit 0 true (fun _ => rfl)
    · have h' : t.getLast? ≠ some false := by
        cases t with
        | nil => exact absurd rfl ht
        | cons x t' => simpa [List.getLast?_cons_cons] using h
      have ih' := ih h'
      have hne : bval t ≠ 0 := by
        intro h0; rw [h0] at ih'; simp at ih'; exact absurd ih'.symm (Ne.symm ht)
      simp only [bval]
      rw [Nat.bits_append_bit _ _ (fun h0 => absurd h0 hne), ih']

lemma bits_getLast (n : ℕ) : (Nat.bits n).getLast? ≠ some false := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    by_cases h0 : n = 0
    · subst h0; have := hn rfl; subst this; simp
    · have hne : Nat.bits n ≠ [] := fun h => h0 ((bits_eq_nil_iff' n).1 h)
      rw [List.getLast?_cons, List.getLast?_eq_some_getLast hne] at *
      simpa using ih

def fromB (x : BSym) : Bool := decide (x = .one)

lemma enc_fromB (l : List BSym) (h : ∀ x ∈ l, isDigB x = true) : enc (l.map fromB) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, enc_cons]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have := h x (List.mem_cons_self)
    cases x <;> simp_all [isDigB, fromB, toB]

lemma map_fromB_enc (l : List Bool) : (enc l).map fromB = l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp_all [fromB, toB]

lemma isDigB_enc (l : List Bool) : ∀ x ∈ enc l, isDigB x = true := by
  intro x hx
  simp only [enc, List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  cases b <;> rfl

lemma digs_code (l : List Bool) (r : List BSym) : digs (enc l ++ BSym.sep :: r) = enc l := by
  unfold digs
  rw [List.takeWhile_append_of_pos (isDigB_enc l)]
  simp [List.takeWhile, isDigB]

lemma rest_code (l : List Bool) (r : List BSym) : rest (enc l ++ BSym.sep :: r) = BSym.sep :: r := by
  unfold rest
  rw [List.dropWhile_append_of_pos (isDigB_enc l)]
  simp [List.dropWhile, isDigB]

lemma numOK_code (n : ℕ) (bs : List Bool) : numOK (code n bs) := by
  unfold numOK code
  rw [rest_code, digs_code]
  refine ⟨rfl, ?_⟩
  have := bits_getLast n
  rw [enc, List.getLast?_map]
  intro h
  cases hh : (Nat.bits n).getLast? with
  | none => rw [hh] at h; cases h
  | some b =>
    rw [hh] at h; simp at h
    cases b
    · exact this hh
    · simp [toB] at h

/-- the value read from the digits -/
def nval (w : List BSym) : ℕ := bval ((digs w).map fromB)

lemma digs_eq (w : List BSym) (h : numOK w) : digs w = enc (Nat.bits (nval w)) := by
  have hdig : ∀ x ∈ digs w, isDigB x = true := fun x hx => List.mem_takeWhile_imp hx
  have hl : ((digs w).map fromB).getLast? ≠ some false := by
    rw [List.getLast?_map]
    intro hc
    apply h.2
    cases hh : (digs w).getLast? with
    | none => rw [hh] at hc; cases hc
    | some x =>
      rw [hh] at hc
      have hx := hdig x (List.mem_of_getLast? hh)
      cases x <;> simp_all [fromB, isDigB]
  unfold nval
  rw [bits_bval _ hl, enc_fromB _ hdig]

lemma w_eq (w : List BSym) (h : numOK w) (bs : List Bool) (hb : tokP false (rest w).tail = some bs) :
    w = code (nval w) bs := by
  have h1 := List.takeWhile_append_dropWhile (p := isDigB) (l := w)
  have h2 := tokP_some _ false bs hb
  simp only [Bool.false_eq_true, if_false] at h2
  have h3 : rest w = BSym.sep :: (rest w).tail := by
    have := h.1
    cases hr : rest w with
    | nil => rw [hr] at this; cases this
    | cons a l => rw [hr] at this; simp at this; subst this; rfl
  unfold code
  rw [← digs_eq w h, ← h2, ← h3]
  exact h1.symm

lemma code_unique (w : List BSym) (bs : List Bool) (hb : tokP false (rest w).tail = some bs)
    (n' : ℕ) (bs' : List Bool) (hw : w = code n' bs') : n' = nval w ∧ bs' = bs := by
  subst hw
  constructor
  · unfold nval code; rw [digs_code, map_fromB_enc, bval_bits]
  · unfold code at hb; rw [rest_code] at hb; simp only [List.tail_cons] at hb
    rw [tokP_flat] at hb; exact Option.some.inj hb

/-! ## the parsing program -/

def parseProg : Prog :=
  .seq (.seq pP1 (.seq pP2 pP3)) (.seq (gate pP4) (.seq (gate pP6) (gate pP7)))

lemma digs_len (w : List BSym) : (digs w).length ≤ w.length :=
  (List.takeWhile_sublist _).length_le

lemma rest_len (w : List BSym) : (rest w).length ≤ w.length :=
  (List.dropWhile_sublist _).length_le

theorem parse_spec (w : List BSym) :
    ∃ τ, Runs parseProg (initR w) τ (300 * (w.length + 1) ^ 2) ∧
      ((∃ n bs, bs.length = n * n ∧ w = code n bs ∧ τ = st6 n bs) ∨
        (τ.bad ≠ [] ∧ τ.out = [] ∧ ∀ n bs, bs.length = n * n → w ≠ code n bs)) := by
  obtain ⟨τ1, e1, hok, hnok⟩ := runs_P123 w
  set L := w.length with hL
  have hsq : 0 ≤ (L + 1) ^ 2 := Nat.zero_le _
  have hLsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  by_cases hw : numOK w
  · have hτ1 := hok hw
    subst hτ1
    obtain ⟨τ4, e4, hs4, hn4⟩ := runs_P4 (st3 w) rfl rfl rfl rfl
    have e4' := runs_gate_ok (p := pP4) rfl e4
    have hinpL : (st3 w).inp.length ≤ L := by
      simp only [st3]; have := rest_len w; simp; omega
    cases htok : tokP false (st3 w).inp with
    | none =>
      obtain ⟨hb4, ho4⟩ := hn4 htok
      refine ⟨τ4, (e1.seq (e4'.seq ((runs_gate_skip hb4).seq (runs_gate_skip hb4)))).mono ?_,
        Or.inr ⟨hb4, by rw [ho4]; rfl, ?_⟩⟩
      · nlinarith
      · intro n bs _ hcode
        have : tokP false (rest w).tail = some bs := by
          rw [hcode]; unfold code; rw [rest_code]; exact tokP_flat bs
        simp only [st3] at htok
        rw [this] at htok; cases htok
    | some bs =>
      have hτ4 := hs4 bs htok
      have hst4 : τ4 = st4 (nval w) bs := by
        rw [hτ4]; unfold st4; rw [← digs_eq w hw]; rfl
      have hbsL : bs.length ≤ L := le_trans (tokP_len _ _ htok) hinpL
      have hnL : (Nat.bits (nval w)).length ≤ L := by
        have := digs_len w; rw [digs_eq w hw] at this; simpa using this
      obtain ⟨τ6, e6, h6a, h6b⟩ := runs_P6 (nval w) bs L hbsL hnL
      rw [← hst4] at e6
      have e6' := runs_gate_ok (p := pP6) (by rw [hτ4]; rfl) e6
      have htok' : tokP false (rest w).tail = some bs := htok
      by_cases hle : nval w ≤ bs.length
      · have hτ6 := h6a hle
        subst hτ6
        obtain ⟨τ7, e7, h7a, h7b⟩ := runs_P7 (nval w) bs L hbsL hle
        have e7' := runs_gate_ok (p := pP7) rfl e7
        by_cases hsq' : nval w * nval w = bs.length
        · have hτ7 := h7a hsq'
          subst hτ7
          refine ⟨st6 (nval w) bs, (e1.seq (e4'.seq (e6'.seq e7'))).mono ?_,
            Or.inl ⟨nval w, bs, hsq'.symm, w_eq w hw bs htok', rfl⟩⟩
          nlinarith
        · obtain ⟨hb7, ho7⟩ := h7b hsq'
          refine ⟨τ7, (e1.seq (e4'.seq (e6'.seq e7'))).mono ?_, Or.inr ⟨hb7, ho7, ?_⟩⟩
          · nlinarith
          · intro n' bs' hl hcode
            obtain ⟨h1, h2⟩ := code_unique w bs htok' n' bs' hcode
            rw [h1, h2] at hl; exact hsq' hl.symm
      · obtain ⟨hb6, ho6⟩ := h6b (by omega)
        refine ⟨τ6, (e1.seq (e4'.seq (e6'.seq (runs_gate_skip hb6)))).mono ?_,
          Or.inr ⟨hb6, ho6, ?_⟩⟩
        · nlinarith
        · intro n' bs' hl hcode
          obtain ⟨h1, h2⟩ := code_unique w bs htok' n' bs' hcode
          rw [h1, h2] at hl
          have : nval w ≤ nval w * nval w := Nat.le_mul_self _
          omega
  · obtain ⟨hb, ho⟩ := hnok hw
    refine ⟨τ1, (e1.seq ((runs_gate_skip hb).seq ((runs_gate_skip hb).seq (runs_gate_skip hb)))).mono ?_,
      Or.inr ⟨hb, ho, ?_⟩⟩
    · nlinarith
    · intro n bs _ hcode
      exact hw (hcode ▸ numOK_code n bs)

end NWRed

set_option autoImplicit false

namespace NWRed

open ProjSchedTW.Complexity (BSym)
open SchedComplexity.NoWait

/-! ## The machine assignment: rows `1, …, n-1, 0`, columns ascending, diagonal skipped -/

def posR (n j : ℕ) : ℕ := if j = 0 then n - 1 else j - 1
def cidx (j k : ℕ) : ℕ := if k < j then k else k - 1
def iotaN (n j k : ℕ) : ℕ := 2 + posR n j * (n - 1) + cidx j k

lemma posR_lt {n j : ℕ} (hj : j < n) : posR n j < n := by unfold posR; split_ifs <;> omega

lemma posR_inj {n j j' : ℕ} (hj : j < n) (hj' : j' < n) (h : posR n j = posR n j') : j = j' := by
  unfold posR at h; split_ifs at h <;> omega

lemma cidx_lt {n j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k) : cidx j k < n - 1 := by
  unfold cidx; split_ifs <;> omega

lemma cidx_inj {j k k' : ℕ} (hk : j ≠ k) (hk' : j ≠ k') (h : cidx j k = cidx j k') : k = k' := by
  unfold cidx at h; split_ifs at h <;> omega

lemma divmod_uniq {d p p' c c' : ℕ} (hc : c < d) (hc' : c' < d) (h : p * d + c = p' * d + c') :
    p = p' ∧ c = c' := by
  have hp : p = p' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (p + 1) * d ≤ p' * d := Nat.mul_le_mul_right _ hlt
      nlinarith
    · have : (p' + 1) * d ≤ p * d := Nat.mul_le_mul_right _ hlt
      nlinarith
  subst hp; exact ⟨rfl, by omega⟩

lemma iotaN_inj {n j k j' k' : ℕ} (hj : j < n) (hk : k < n) (hj' : j' < n) (hk' : k' < n)
    (hjk : j ≠ k) (hjk' : j' ≠ k') (h : iotaN n j k = iotaN n j' k') : j = j' ∧ k = k' := by
  unfold iotaN at h
  obtain ⟨h1, h2⟩ := divmod_uniq (p := posR n j) (p' := posR n j') (cidx_lt hj hk hjk)
    (cidx_lt hj' hk' hjk') (by omega)
  have hjj := posR_inj hj hj' h1
  subst hjj
  exact ⟨rfl, cidx_inj hjk hjk' h2⟩

lemma iotaN_range {n j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k) :
    2 ≤ iotaN n j k ∧ iotaN n j k ≤ n * (n - 1) + 1 := by
  have h1 := posR_lt hj
  have h2 := cidx_lt hj hk hjk
  unfold iotaN
  refine ⟨by omega, ?_⟩
  have : posR n j * (n - 1) ≤ (n - 1) * (n - 1) := Nat.mul_le_mul_right _ (by omega)
  have h3 : n * (n - 1) = (n - 1) * (n - 1) + (n - 1) := by
    rcases n with _ | n
    · simp
    · simp [Nat.succ_sub_one]; ring
  omega

lemma iotaN_surj {n i : ℕ} (hi1 : 2 ≤ i) (hi2 : i ≤ n * (n - 1) + 1) :
    ∃ j k, j < n ∧ k < n ∧ j ≠ k ∧ iotaN n j k = i := by
  have hn : 2 ≤ n := by
    by_contra h
    interval_cases n <;> simp at hi2 <;> omega
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hi2 ⊢
  have hd1 : 1 ≤ d := by omega
  have hcd : (i - 2) % d < d := Nat.mod_lt _ (by omega)
  have hdm : d * ((i - 2) / d) + (i - 2) % d = i - 2 := Nat.div_add_mod (i - 2) d
  generalize (i - 2) / d = q at hdm
  generalize (i - 2) % d = c at hdm hcd
  have hqn : q < d + 1 := by
    by_contra hcon
    have : d * (d + 1) ≤ d * q := Nat.mul_le_mul_left _ (by omega)
    have h5 : (d + 1) * d = d * (d + 1) := by ring
    omega
  refine ⟨if q = d then 0 else q + 1, if c < (if q = d then 0 else q + 1) then c else c + 1,
    ?_, ?_, ?_, ?_⟩
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · unfold iotaN posR cidx
    have : q * d = d * q := by ring
    split_ifs <;> simp_all <;> omega

lemma iotaN_noconsec {n j l k : ℕ} (hn : n ≠ 2) (hj : j < n) (hl : l < n) (hk : k < n)
    (hjl : j ≠ l) (hlk : l ≠ k) : iotaN n j l ≠ iotaN n l k + 1 := by
  intro h
  have hpj := posR_lt hj
  have hpl := posR_lt hl
  have hc1 := cidx_lt hj hl hjl
  have hc2 := cidx_lt hl hk hlk
  unfold iotaN at h
  -- compare blocks
  rcases Nat.lt_trichotomy (posR n j) (posR n l) with hlt | heq | hgt
  · have : (posR n j + 1) * (n - 1) ≤ posR n l * (n - 1) := Nat.mul_le_mul_right _ hlt
    nlinarith
  · exact hjl (posR_inj hj hl heq)
  · by_cases hgt2 : posR n l + 2 ≤ posR n j
    · have : (posR n l + 2) * (n - 1) ≤ posR n j * (n - 1) := Nat.mul_le_mul_right _ hgt2
      nlinarith
    · have hp : posR n j = posR n l + 1 := by omega
      rw [hp] at h
      have hcj : cidx j l = 0 ∧ cidx l k = n - 2 := by
        have : (posR n l + 1) * (n - 1) = posR n l * (n - 1) + (n - 1) := by ring
        omega
      obtain ⟨hc0, _⟩ := hcj
      unfold cidx at hc0
      unfold posR at hp
      split_ifs at hc0 hp <;> omega

theorem iotaN_adm (n : ℕ) (hn : n ≠ 2) : Admissible n (fun j k : Fin n => iotaN n j.val k.val) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j k hjk
    exact iotaN_range j.isLt k.isLt (fun h => hjk (Fin.ext h))
  · intro j k j' k' hjk hjk' h
    obtain ⟨h1, h2⟩ := iotaN_inj j.isLt k.isLt j'.isLt k'.isLt (fun h => hjk (Fin.ext h))
      (fun h => hjk' (Fin.ext h)) h
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  · intro i hi1 hi2
    obtain ⟨j, k, hj, hk, hjk, h⟩ := iotaN_surj hi1 hi2
    exact ⟨⟨j, hj⟩, ⟨k, hk⟩, fun h' => hjk (congrArg Fin.val h'), h⟩
  · intro j l k hjl hlk
    exact iotaN_noconsec hn j.isLt l.isLt k.isLt (fun h => hjl (Fin.ext h)) (fun h => hlk (Fin.ext h))

/-! ## Roles of the machines with respect to a job -/

def roleSym (src b : Bool) : BSym :=
  if src then (if b then .zero else .one) else (if b then .minus else .sep)

/-- the role of the pair `(j, k)` (arc bit `a j k`) for job `ℓ` -/
def roleN (a : ℕ → ℕ → Bool) (ℓ j k : ℕ) : Option BSym :=
  if j = ℓ then some (roleSym true (a j k)) else if k = ℓ then some (roleSym false (a j k)) else none

open Classical in
/-- the role of machine `i` for job `ℓ` -/
noncomputable def rlN (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ i : ℕ) : Option BSym :=
  if h : ∃ p : ℕ × ℕ, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2 ∧ i = iotaN n p.1 p.2 then
    roleN a ℓ (Classical.choose h).1 (Classical.choose h).2 else none

lemma rlN_iota (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ j k : ℕ) (hj : j < n) (hk : k < n) (hjk : j ≠ k) :
    rlN n a ℓ (iotaN n j k) = roleN a ℓ j k := by
  have h : ∃ p : ℕ × ℕ, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2 ∧ iotaN n j k = iotaN n p.1 p.2 :=
    ⟨(j, k), hj, hk, hjk, rfl⟩
  unfold rlN; rw [dif_pos h]
  obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec h
  obtain ⟨e1, e2⟩ := iotaN_inj hj hk h1 h2 hjk h3 h4
  rw [← e1, ← e2]

lemma rlN_none (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ i : ℕ) (hi : i < 2 ∨ n * (n - 1) + 1 < i) :
    rlN n a ℓ i = none := by
  unfold rlN
  rw [dif_neg]
  rintro ⟨p, h1, h2, h3, h4⟩
  have := iotaN_range h1 h2 h3
  omega

lemma rlN_some (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ i : ℕ) (s : BSym) (h : rlN n a ℓ i = some s) :
    ∃ j k, j < n ∧ k < n ∧ j ≠ k ∧ i = iotaN n j k ∧ roleN a ℓ j k = some s := by
  unfold rlN at h
  split_ifs at h with hh
  obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec hh
  exact ⟨_, _, h1, h2, h3, h4, h⟩

def Av : Option BSym → ℤ
  | some .zero => 1
  | some .one => 2
  | _ => 0

def Bv : Option BSym → ℤ
  | some .minus => 1
  | some .sep => 2
  | _ => 0

/-- the processing time of a machine from the roles of it and its two neighbours -/
def pv (x y z : Option BSym) : ℕ := (5 + Av y + Bv y - Av x - Bv z).toNat

lemma Av_role (a : ℕ → ℕ → Bool) (ℓ j k : ℕ) :
    Av (roleN a ℓ j k) = if j = ℓ then (if a j k then 1 else 2) else 0 := by
  unfold roleN roleSym; split_ifs <;> simp_all [Av]

lemma Bv_role (a : ℕ → ℕ → Bool) (ℓ j k : ℕ) :
    Bv (roleN a ℓ j k) = if j ≠ ℓ ∧ k = ℓ then (if a j k then 1 else 2) else 0 := by
  unfold roleN roleSym; split_ifs <;> simp_all [Bv]

lemma Av_none_case (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ i : ℕ)
    (h : ¬ ∃ k, k < n ∧ k ≠ ℓ ∧ i = iotaN n ℓ k) : Av (rlN n a ℓ i) = 0 := by
  cases hr : rlN n a ℓ i with
  | none => rfl
  | some s =>
    obtain ⟨j, k, hj, hk, hjk, hi, hs⟩ := rlN_some n a ℓ i s hr
    have := Av_role a ℓ j k
    rw [hs] at this; rw [this]
    by_cases h1 : j = ℓ
    · subst h1; exact absurd ⟨k, hk, fun e => hjk e.symm, hi⟩ h
    · rw [if_neg h1]

lemma Bv_none_case (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ i : ℕ)
    (h : ¬ ∃ j, j < n ∧ j ≠ ℓ ∧ i = iotaN n j ℓ) : Bv (rlN n a ℓ i) = 0 := by
  cases hr : rlN n a ℓ i with
  | none => rfl
  | some s =>
    obtain ⟨j, k, hj, hk, hjk, hi, hs⟩ := rlN_some n a ℓ i s hr
    have := Bv_role a ℓ j k
    rw [hs] at this; rw [this]
    by_cases h1 : j ≠ ℓ ∧ k = ℓ
    · obtain ⟨h1, h2⟩ := h1; subst h2; exact absurd ⟨j, hj, h1, hi⟩ h
    · rw [if_neg h1]

theorem partialSum_eq {n : ℕ} (hn : n ≠ 2) (a : ℕ → ℕ → Bool) (adj : Fin n → Fin n → Bool)
    (hadj : ∀ u v : Fin n, adj u v = a u.val v.val) (ℓ : Fin n) (i : ℕ) :
    partialSum adj (fun j k : Fin n => iotaN n j.val k.val) 1 5 ℓ i =
      5 * (i : ℤ) + Av (rlN n a ℓ.val i) - Bv (rlN n a ℓ.val (i + 1)) := by
  unfold partialSum
  beta_reduce
  by_cases hA : ∃ k : Fin n, k ≠ ℓ ∧ i = iotaN n ℓ.val k.val
  · obtain ⟨k, hkl, hi⟩ := hA
    have hkl' : ℓ.val ≠ k.val := fun e => hkl (Fin.ext e).symm
    have hr : rlN n a ℓ.val i = roleN a ℓ.val ℓ.val k.val := by
      rw [hi]; exact rlN_iota n a _ _ _ ℓ.isLt k.isLt hkl'
    have hB : Bv (rlN n a ℓ.val (i + 1)) = 0 := by
      apply Bv_none_case
      rintro ⟨j, hj, hjl, hj'⟩
      exact iotaN_noconsec hn hj ℓ.isLt k.isLt hjl hkl' (by omega)
    have huniq : ∀ k' : Fin n, k' ≠ ℓ → i = iotaN n ℓ.val k'.val → k' = k := by
      intro k' hk' hi'
      exact Fin.ext (iotaN_inj ℓ.isLt k'.isLt ℓ.isLt k.isLt (fun e => hk' (Fin.ext e).symm) hkl'
        (hi'.symm.trans hi)).2
    rw [hr, hB, Av_role]
    simp only [if_true]
    cases hb : a ℓ.val k.val
    · rw [if_neg, if_pos]
      · norm_num <;> ring
      · exact ⟨k, hkl, hi, by rw [hadj]; exact hb⟩
      · rintro ⟨k', hk', hi', ha⟩
        rw [huniq k' hk' hi', hadj, hb] at ha; cases ha
    · rw [if_pos]
      · norm_num <;> ring
      · exact ⟨k, hkl, hi, by rw [hadj]; exact hb⟩
  · have hA' : ¬ ∃ k, k < n ∧ k ≠ ℓ.val ∧ i = iotaN n ℓ.val k := by
      rintro ⟨k, hk, hkl, hi⟩
      exact hA ⟨⟨k, hk⟩, fun e => hkl (congrArg Fin.val e), hi⟩
    have hAv := Av_none_case n a ℓ.val i hA'
    rw [hAv]
    have n1 : ¬ ∃ k : Fin n, k ≠ ℓ ∧ i = iotaN n ℓ.val k.val ∧ adj ℓ k = true :=
      fun ⟨k, h1, h2, _⟩ => hA ⟨k, h1, h2⟩
    have n2 : ¬ ∃ k : Fin n, k ≠ ℓ ∧ i = iotaN n ℓ.val k.val ∧ adj ℓ k = false :=
      fun ⟨k, h1, h2, _⟩ => hA ⟨k, h1, h2⟩
    rw [if_neg n1, if_neg n2]
    by_cases hB : ∃ j : Fin n, j ≠ ℓ ∧ i + 1 = iotaN n j.val ℓ.val
    · obtain ⟨j, hjl, hi⟩ := hB
      have hjl' : j.val ≠ ℓ.val := fun e => hjl (Fin.ext e)
      have hr : rlN n a ℓ.val (i + 1) = roleN a ℓ.val j.val ℓ.val := by
        rw [hi]; exact rlN_iota n a _ _ _ j.isLt ℓ.isLt hjl'
      have huniq : ∀ j' : Fin n, j' ≠ ℓ → i + 1 = iotaN n j'.val ℓ.val → j' = j := by
        intro j' hj' hi'
        exact Fin.ext (iotaN_inj j'.isLt ℓ.isLt j.isLt ℓ.isLt (fun e => hj' (Fin.ext e)) hjl'
          (hi'.symm.trans hi)).1
      rw [hr, Bv_role, if_pos (show (j.val ≠ ℓ.val ∧ ℓ.val = ℓ.val) from ⟨hjl', rfl⟩)]
      cases hb : a j.val ℓ.val
      · rw [if_neg, if_pos]
        · norm_num <;> ring
        · exact ⟨j, hjl, hi, by rw [hadj]; exact hb⟩
        · rintro ⟨j', hj', hi', ha⟩
          rw [huniq j' hj' hi', hadj, hb] at ha; cases ha
      · rw [if_pos]
        · norm_num <;> ring
        · exact ⟨j, hjl, hi, by rw [hadj]; exact hb⟩
    · have hB' : ¬ ∃ j, j < n ∧ j ≠ ℓ.val ∧ i + 1 = iotaN n j ℓ.val := by
        rintro ⟨j, hj, hjl, hi⟩
        exact hB ⟨⟨j, hj⟩, fun e => hjl (congrArg Fin.val e), hi⟩
      rw [Bv_none_case n a ℓ.val (i + 1) hB']
      rw [if_neg (fun ⟨j, h1, h2, _⟩ => hB ⟨j, h1, h2⟩),
        if_neg (fun ⟨j, h1, h2, _⟩ => hB ⟨j, h1, h2⟩)]
      ring

theorem procTimes_eq {n : ℕ} (hn : n ≠ 2) (a : ℕ → ℕ → Bool) (adj : Fin n → Fin n → Bool)
    (hadj : ∀ u v : Fin n, adj u v = a u.val v.val) (ℓ : Fin n) (r : Fin (numMachines n)) :
    procTimes adj (fun j k : Fin n => iotaN n j.val k.val) 1 5 ℓ r =
      pv (rlN n a ℓ.val r.val) (rlN n a ℓ.val (r.val + 1)) (rlN n a ℓ.val (r.val + 2)) := by
  unfold procTimes procTimeInt pv
  congr 1
  split_ifs with h0
  · rw [partialSum_eq hn a adj hadj, h0, rlN_none n a ℓ.val 0 (by omega),
      rlN_none n a ℓ.val 1 (by omega)]
    simp [Av, Bv] <;> ring
  · rw [partialSum_eq hn a adj hadj, partialSum_eq hn a adj hadj]
    push_cast
    ring

end NWRed



set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## Generic gadgets -/

lemma hd_set_off (σ : Regs) (dst : Key) (l : List BSym) (k : Key) (hk : k ≠ dst) :
    hd (σ.set dst l) k = hd σ k := by simp [hd, Regs.get_set, hk]

/-- `F` ignores the top of `dst` -/
def IndOf (dst : Key) (F : (Key → Option BSym) → List BSym) : Prop :=
  ∀ h h' : Key → Option BSym, (∀ k, k ≠ dst → h k = h' k) → F h = F h'

def ptAct (dst : Key) (F : (Key → Option BSym) → List BSym) :
    (Key → Option BSym) → Key → StackAct BSym :=
  fun h k => if k = dst then (match (F h).head? with | some a => .push a | none => .keep) else .keep

/-- push the list `F (tops)` onto `dst`, one symbol per step, for at most `K` symbols -/
def pt (dst : Key) : ((Key → Option BSym) → List BSym) → ℕ → Prog
  | _, 0 => skipP
  | F, K + 1 => .seq (.act (ptAct dst F)) (pt dst (fun h => (F h).tail) K)

lemma runs_ptAct (dst : Key) (F : (Key → Option BSym) → List BSym) (σ : Regs) :
    Runs (.act (ptAct dst F)) σ (σ.set dst ((F (hd σ)).take 1 ++ σ.get dst)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act (ptAct dst F) σ.get
  convert e using 1
  funext k
  rw [Regs.get_set]
  simp only [StackProg.applyAct, ptAct]
  by_cases h1 : k = dst
  · subst h1
    simp only [if_true]
    have : (fun j => (σ.get j).head?) = hd σ := rfl
    rw [this]
    cases F (hd σ) with
    | nil => simp [StackAct.apply]
    | cons a l => simp [StackAct.apply]
  · simp [h1, StackAct.apply]

lemma runs_pt (dst : Key) : ∀ (K : ℕ) (F : (Key → Option BSym) → List BSym) (σ : Regs),
    IndOf dst F → (F (hd σ)).length ≤ K →
    Runs (pt dst F K) σ (σ.set dst ((F (hd σ)).reverse ++ σ.get dst)) (3 * K + 1) := by
  intro K
  induction K with
  | zero =>
    intro F σ _ hl
    have : F (hd σ) = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this]
    simp only [List.reverse_nil, List.nil_append, Regs.set_get]
    exact runs_skip σ
  | succ K ih =>
    intro F σ hF hl
    have e1 := runs_ptAct dst F σ
    have hFeq : F (hd (σ.set dst ((F (hd σ)).take 1 ++ σ.get dst))) = F (hd σ) :=
      hF _ _ (fun k hk => hd_set_off σ dst _ k hk)
    have hF' : IndOf dst (fun h => (F h).tail) := fun h h' hh => by
      simp only [hF h h' hh]
    have e2 := ih (fun h => (F h).tail) (σ.set dst ((F (hd σ)).take 1 ++ σ.get dst)) hF'
      (by simp only [hFeq, List.length_tail]; omega)
    simp only [hFeq] at e2
    refine ((e1.seq e2).congr ?_).mono (by omega)
    rw [Regs.set_set, Regs.get_set_self]
    congr 1
    cases F (hd σ) with
    | nil => simp
    | cons a l => simp

/-! ## marker counters -/

/-- `t < a`: `a - t` ones; `t = a`: empty; `t > a`: a `zero` marker -/
def mk (a t : ℕ) : List BSym := if t ≤ a then List.replicate (a - t) .one else [.zero]

def mkProg (X : Key) : Prog :=
  .branch (fun h => decide (h X = some .one)) (popProg X)
    (.branch (fun h => (h X).isNone) (pushProg X .zero) skipP)

lemma mk_head_none (a t : ℕ) : (mk a t).head? = none ↔ t = a := by
  unfold mk
  split_ifs with h
  · rcases Nat.lt_or_ge t a with h1 | h1
    · rw [show a - t = (a - t - 1) + 1 by omega, List.replicate_succ]; simp; omega
    · rw [show a - t = 0 by omega]; simp; omega
  · simp; omega

lemma runs_mk (X : Key) (σ : Regs) (a t : ℕ) (h : σ.get X = mk a t) :
    Runs (mkProg X) σ (σ.set X (mk a (t + 1))) 3 := by
  rcases Nat.lt_trichotomy t a with hlt | heq | hgt
  · have hX : σ.get X = .one :: List.replicate (a - t - 1) .one := by
      rw [h, mk, if_pos hlt.le]
      have : a - t = (a - t - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [List.replicate_succ]
    have e := (runs_pop X σ).brT (t := fun h => decide (h X = some .one))
      (q := .branch (fun h => (h X).isNone) (pushProg X .zero) skipP) (by simp [hd, hX])
    refine (e.congr ?_).mono (by omega)
    rw [hX]; congr 1
    simp only [List.tail_cons, mk, if_pos (show t + 1 ≤ a by omega)]
    first | rfl | (congr 1; omega)
  · subst heq
    have hX : σ.get X = [] := by rw [h, mk, if_pos le_rfl]; simp
    have e := ((runs_push X .zero σ).brT (t := fun h => (h X).isNone) (q := skipP)
      (by simp [hd, hX])).brF (t := fun h => decide (h X = some .one)) (p := popProg X)
      (by simp [hd, hX])
    refine e.congr ?_
    rw [hX]; simp [mk]
  · have hX : σ.get X = [.zero] := by rw [h, mk, if_neg (by omega)]
    have e := ((runs_skip σ).brF (t := fun h => (h X).isNone) (p := pushProg X .zero)
      (by simp [hd, hX])).brF (t := fun h => decide (h X = some .one)) (p := popProg X)
      (by simp [hd, hX])
    refine (e.congr ?_).mono (by omega)
    rw [show mk a (t + 1) = [.zero] by rw [mk, if_neg (by omega)], ← hX, Regs.set_get]

/-! ## moving a prefix -/

def mvNProg (C a b : Key) : Prog := .loop (fun h => (h C).isSome) (.seq (popProg C) (mv1 a b))

lemma runs_mvN (C a b : Key) (hCa : C ≠ a) (hCb : C ≠ b) (hab : a ≠ b) : ∀ (c : ℕ) (σ : Regs)
    (l : List BSym), σ.get C = List.replicate c .one → σ.get a = l → c ≤ l.length →
    Runs (mvNProg C a b) σ
      (((σ.set C []).set a (l.drop c)).set b ((l.take c).reverse ++ σ.get b)) (5 * c + 1) := by
  intro c
  induction c with
  | zero =>
    intro σ l hC ha _
    simp only [List.replicate_zero] at hC
    have : ((σ.set C []).set a (l.drop 0)).set b ((l.take 0).reverse ++ σ.get b) = σ := by
      simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append]
      rw [← hC, ← ha, Regs.set_get, Regs.set_get, Regs.set_get]
    rw [this]
    exact Runs.loopF (by simp [hd, hC])
  | succ c ih =>
    intro σ l hC ha hl
    obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      cases l with
      | nil => simp at hl
      | cons x l' => exact ⟨x, l', rfl⟩
    have e1 := runs_pop C σ
    set σ1 := σ.set C (σ.get C).tail with hσ1
    have h1a : σ1.get a = x :: l' := by rw [hσ1, Regs.get_set, if_neg (Ne.symm hCa), ha]
    have e2 := runs_mv1 a b hab σ1 x l' h1a
    set σ2 := (σ1.set a l').set b (x :: σ1.get b) with hσ2
    have h2C : σ2.get C = List.replicate c .one := by
      rw [hσ2, Regs.get_set, if_neg hCb, Regs.get_set, if_neg hCa, hσ1, Regs.get_set_self, hC]
      simp [List.replicate_succ]
    have h2a : σ2.get a = l' := by rw [hσ2, Regs.get_set, if_neg hab, Regs.get_set_self]
    have e3 := ih σ2 l' h2C h2a (by simp at hl; omega)
    refine (Runs.loopT (by simp [hd, hC, List.replicate_succ]) (e1.seq e2) e3).congr ?_ |>.mono (by omega)
    have h2b : σ2.get b = x :: σ.get b := by
      rw [hσ2, Regs.get_set_self, hσ1, Regs.get_set, if_neg (Ne.symm hCb)]
    rw [h2b]
    apply Regs.ext_get; funext k
    simp only [Regs.get_set, hσ2, hσ1]
    split_ifs <;> simp_all

/-! ## unary to binary -/

def u2bProg (U B : Key) : Prog := .loop (fun h => (h U).isSome) (.seq (popProg U) (incProg B .T))

lemma runs_u2b (U B : Key) (hUB : U ≠ B) (hUT : U ≠ .T) (hBT : B ≠ .T) : ∀ (u : ℕ) (σ : Regs)
    (b0 : ℕ), σ.get U = List.replicate u .one → σ.get B = enc (Nat.bits b0) → σ.T = [] →
    Runs (u2bProg U B) σ ((σ.set U []).set B (enc (Nat.bits (b0 + u))))
      (u * (6 * (b0 + u) + 15) + 1) := by
  intro u
  induction u with
  | zero =>
    intro σ b0 hU hB _
    simp only [List.replicate_zero] at hU
    rw [Nat.add_zero, ← hU, ← hB, Regs.set_get, Regs.set_get]
    exact (Runs.loopF (by simp [hd, hU])).mono (by omega)
  | succ u ih =>
    intro σ b0 hU hB hT
    have e1 := runs_pop U σ
    set σ1 := σ.set U (σ.get U).tail with hσ1
    have h1B : σ1.get B = enc (Nat.bits b0) := by rw [hσ1, Regs.get_set, if_neg (Ne.symm hUB), hB]
    have h1T : σ1.get .T = [] := by rw [hσ1, Regs.get_set, if_neg (Ne.symm hUT)]; exact hT
    have e2 := runs_inc B .T hBT σ1 (Nat.bits b0) h1B h1T
    rw [incL_bits] at e2
    set σ2 := σ1.set B (enc (Nat.bits (b0 + 1))) with hσ2
    have h2U : σ2.get U = List.replicate u .one := by
      rw [hσ2, Regs.get_set, if_neg hUB, hσ1, Regs.get_set_self, hU]; simp [List.replicate_succ]
    have h2B : σ2.get B = enc (Nat.bits (b0 + 1)) := by rw [hσ2, Regs.get_set_self]
    have h2T : σ2.T = [] := by
      show σ2.get .T = []
      rw [hσ2, Regs.get_set, if_neg (Ne.symm hBT)]; exact h1T
    have e3 := ih σ2 (b0 + 1) h2U h2B h2T
    have hlen : (Nat.bits b0).length ≤ b0 + (u + 1) := le_trans (len_bits_le b0) (by omega)
    refine (Runs.loopT (by simp [hd, hU, List.replicate_succ]) (e1.seq e2) e3).congr ?_ |>.mono ?_
    · rw [show b0 + 1 + u = b0 + (u + 1) by omega]
      apply Regs.ext_get; funext k
      simp only [Regs.get_set, hσ2, hσ1]
      split_ifs <;> simp_all
    · have : (u * (6 * (b0 + 1 + u) + 15) + 1) = u * (6 * (b0 + (u + 1)) + 15) + 1 := by ring_nf
      rw [this]
      nlinarith

/-! ## halving a unary number -/

def halfProg (X Y : Key) : Prog :=
  .loop (fun h => (h X).isSome) (.seq (popProg X) (.seq (popProg X) (pushProg Y .one)))

lemma runs_half (X Y : Key) (hXY : X ≠ Y) : ∀ (c : ℕ) (σ : Regs),
    σ.get X = List.replicate (2 * c) .one →
    Runs (halfProg X Y) σ ((σ.set X []).set Y (List.replicate c .one ++ σ.get Y)) (7 * c + 1) := by
  intro c
  induction c with
  | zero =>
    intro σ hX
    simp only [Nat.mul_zero, List.replicate_zero] at hX
    simp only [List.replicate_zero, List.nil_append]
    rw [← hX, Regs.set_get, Regs.set_get]
    exact Runs.loopF (by simp [hd, hX])
  | succ c ih =>
    intro σ hX
    have hX' : σ.get X = .one :: .one :: List.replicate (2 * c) .one := by
      rw [hX, show 2 * (c + 1) = 2 * c + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
    have e1 := runs_pop X σ
    set σ1 := σ.set X (σ.get X).tail with hσ1
    have e2 := runs_pop X σ1
    set σ2 := σ1.set X (σ1.get X).tail with hσ2
    have e3 := runs_push Y .one σ2
    set σ3 := σ2.set Y (.one :: σ2.get Y) with hσ3
    have h3X : σ3.get X = List.replicate (2 * c) .one := by
      rw [hσ3, Regs.get_set, if_neg hXY, hσ2, Regs.get_set_self, hσ1, Regs.get_set_self, hX']; rfl
    have e4 := ih σ3 h3X
    refine (Runs.loopT (by simp [hd, hX']) (e1.seq (e2.seq e3)) e4).congr ?_ |>.mono (by omega)
    have h3Y : σ3.get Y = .one :: σ.get Y := by
      rw [hσ3, Regs.get_set_self, hσ2, Regs.get_set, if_neg (Ne.symm hXY), hσ1, Regs.get_set,
        if_neg (Ne.symm hXY)]
    rw [h3Y]
    apply Regs.ext_get; funext k
    simp only [Regs.get_set, hσ3, hσ2, hσ1]
    split_ifs <;> simp_all [List.replicate_succ']

end NWRed



set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## One machine: compute the role, emit a processing time, shift the window -/

def rep (k : ℕ) : List BSym := List.replicate k .one

def roleOf (rf kl : Bool) (b : BSym) : Option BSym :=
  if rf then some (roleSym true (decide (b = .one)))
  else if kl then some (roleSym false (decide (b = .one))) else none

def roleF : (Key → Option BSym) → List BSym :=
  fun h => (roleOf (h .RF).isSome (h .KL).isNone ((h .S).getD .zero)).toList

def emitF : (Key → Option BSym) → List BSym := fun h => encNat (pv (h .X0) (h .X1) (h .X2))

def shiftP : Prog :=
  .seq (clearProg .X0) (.seq (pt .X0 (fun h => (h .X1).toList) 1)
    (.seq (clearProg .X1) (.seq (pt .X1 (fun h => (h .X2).toList) 1) (clearProg .X2))))

lemma toList_len_le (x : Option BSym) : x.toList.length ≤ 1 := by cases x <;> simp

lemma head_toList (x : Option BSym) : x.toList.head? = x := by cases x <;> rfl

lemma clear_le1 (σ : Regs) (k : Key) (x : Option BSym) (hx : σ.get k = x.toList) :
    Runs (clearProg k) σ (σ.set k []) 4 :=
  (runs_clear k σ).mono (by rw [hx]; have := toList_len_le x; omega)

lemma runs_pt1 (dst src : Key) (hne : src ≠ dst) (σ : Regs) :
    Runs (pt dst (fun h : Key → Option BSym => (h src).toList) 1) σ
      (σ.set dst ((σ.get src).head?.toList ++ σ.get dst)) 4 := by
  have e := runs_pt dst 1 (fun h : Key → Option BSym => (h src).toList) σ
    (fun h h' hh => by simp only [hh src hne]) (toList_len_le _)
  refine e.congr ?_
  simp only [hd]
  cases (σ.get src).head? <;> rfl

lemma runs_shift (σ : Regs) (x0 x1 x2 : Option BSym) (h0 : σ.X0 = x0.toList)
    (h1 : σ.X1 = x1.toList) (h2 : σ.X2 = x2.toList) :
    Runs shiftP σ { σ with X0 := x1.toList, X1 := x2.toList, X2 := [] } 30 := by
  have e1 := clear_le1 σ .X0 x0 h0
  have e2 := runs_pt1 .X0 .X1 (by decide) (σ.set .X0 [])
  have e3 := clear_le1 ((σ.set .X0 []).set .X0 ((((σ.set .X0 []).get .X1)).head?.toList ++
    (σ.set .X0 []).get .X0)) .X1 x1 (by simp [Regs.set, Regs.get, h1])
  have e4 := runs_pt1 .X1 .X2 (by decide) (((σ.set .X0 []).set .X0 ((((σ.set .X0 []).get .X1)).head?.toList ++
    (σ.set .X0 []).get .X0)).set .X1 [])
  have e5 := clear_le1 ((((σ.set .X0 []).set .X0 ((((σ.set .X0 []).get .X1)).head?.toList ++
    (σ.set .X0 []).get .X0)).set .X1 []).set .X1 (((((σ.set .X0 []).set .X0 ((((σ.set .X0 []).get .X1)).head?.toList ++
    (σ.set .X0 []).get .X0)).set .X1 []).get .X2).head?.toList ++ (((σ.set .X0 []).set .X0 ((((σ.set .X0 []).get .X1)).head?.toList ++
    (σ.set .X0 []).get .X0)).set .X1 []).get .X1)) .X2 x2 (by simp [Regs.set, Regs.get, h2])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr ?_).mono (by omega)
  simp only [Regs.get, Regs.set, h1, h2, head_toList, List.append_nil]

lemma pv_le (x y z : Option BSym) : pv x y z ≤ 9 := by
  unfold pv
  rcases x with _ | a <;> rcases y with _ | b <;> rcases z with _ | c <;>
    (try cases a) <;> (try cases b) <;> (try cases c) <;> norm_num [Av, Bv]

lemma encNat_len_le (k : ℕ) (hk : k ≤ 9) : (encNat k).length ≤ 5 := by
  have h1 : Nat.size k ≤ 4 := Nat.size_le.2 (by omega)
  have h2 : (Nat.bits k).length ≤ 4 := by rw [Nat.size_eq_bits_len]; exact h1
  simp [encNat]; omega

def emitStep : Prog := .seq (pt .W emitF 5) shiftP

lemma runs_emitStep (σ : Regs) (x0 x1 x2 : Option BSym) (h0 : σ.X0 = x0.toList)
    (h1 : σ.X1 = x1.toList) (h2 : σ.X2 = x2.toList) :
    Runs emitStep σ
      { σ with
        W := (encNat (pv x0 x1 x2)).reverse ++ σ.W,
        X0 := x1.toList, X1 := x2.toList, X2 := [] } 50 := by
  have hInd : IndOf .W emitF := fun h h' hh => by
    simp only [emitF, hh .X0 (by decide), hh .X1 (by decide), hh .X2 (by decide)]
  have hF : emitF (hd σ) = encNat (pv x0 x1 x2) := by
    simp only [emitF, hd, Regs.get, h0, h1, h2, head_toList]
  have e1 := runs_pt .W 5 emitF σ hInd (by rw [hF]; exact encNat_len_le _ (pv_le _ _ _))
  rw [hF] at e1
  simp only [Regs.set, Regs.get] at e1
  have e2 := runs_shift { σ with W := (encNat (pv x0 x1 x2)).reverse ++ σ.W } x0 x1 x2 h0 h1 h2
  exact ((e1.seq e2).congr rfl).mono (by omega)

def advP : Prog := .seq (mkProg .KL) (.seq (mkProg .KJ) (.seq (popProg .S) (popProg .CC)))

lemma runs_adv (σ : Regs) (ℓ j t : ℕ) (b : BSym) (rest cc : List BSym) (hKL : σ.KL = mk ℓ t)
    (hKJ : σ.KJ = mk j t) (hS : σ.S = b :: rest) (hCC : σ.CC = .one :: cc) :
    Runs advP σ { σ with KL := mk ℓ (t + 1), KJ := mk j (t + 1), S := rest, CC := cc } 15 := by
  have e1 := runs_mk .KL σ ℓ t hKL
  simp only [Regs.set] at e1
  have e2 := runs_mk .KJ { σ with KL := mk ℓ (t + 1) } j t hKJ
  simp only [Regs.set] at e2
  have e3 : Runs (popProg .S) { σ with KL := mk ℓ (t + 1), KJ := mk j (t + 1) }
      { σ with KL := mk ℓ (t + 1), KJ := mk j (t + 1), S := rest } 1 :=
    (runs_pop .S _).congr (by simp [Regs.set, Regs.get, hS])
  have e4 : Runs (popProg .CC) { σ with KL := mk ℓ (t + 1), KJ := mk j (t + 1), S := rest }
      { σ with KL := mk ℓ (t + 1), KJ := mk j (t + 1), S := rest, CC := cc } 1 :=
    (runs_pop .CC _).congr (by simp [Regs.set, Regs.get, hCC])
  refine Runs.mono (Runs.congr (e1.seq (e2.seq (e3.seq e4))) ?_) ?_
  · rfl
  · omega

def entryP : Prog :=
  .branch (fun h => (h .KJ).isNone) advP (.seq (pt .X2 roleF 1) (.seq advP emitStep))

lemma runs_entry_diag (σ : Regs) (ℓ j : ℕ) (b : BSym) (rest cc : List BSym)
    (hKL : σ.KL = mk ℓ j) (hKJ : σ.KJ = mk j j) (hS : σ.S = b :: rest)
    (hCC : σ.CC = .one :: cc) :
    Runs entryP σ { σ with KL := mk ℓ (j + 1), KJ := mk j (j + 1), S := rest, CC := cc } 16 :=
  (runs_adv σ ℓ j j b rest cc hKL hKJ hS hCC).brT (by
    simp only [hd, Regs.get, hKJ]; rw [(mk_head_none j j).2 rfl]; rfl)

lemma runs_entry_nd (σ : Regs) (ℓ j t : ℕ) (htj : t ≠ j) (rf : Bool) (b : BSym)
    (rest cc : List BSym) (x0 x1 : Option BSym)
    (hKL : σ.KL = mk ℓ t) (hKJ : σ.KJ = mk j t) (hS : σ.S = b :: rest)
    (hCC : σ.CC = .one :: cc) (hRF : σ.RF = if rf then [.one] else []) (hX2 : σ.X2 = [])
    (h0 : σ.X0 = x0.toList) (h1 : σ.X1 = x1.toList) :
    Runs entryP σ
      { σ with
        KL := mk ℓ (t + 1), KJ := mk j (t + 1), S := rest, CC := cc,
        W := (encNat (pv x0 x1 (roleOf rf (decide (t = ℓ)) b))).reverse ++ σ.W,
        X0 := x1.toList, X1 := (roleOf rf (decide (t = ℓ)) b).toList } 80 := by
  have hInd : IndOf .X2 roleF := fun h h' hh => by
    simp only [roleF, hh .RF (by decide), hh .KL (by decide), hh .S (by decide)]
  have hR : roleF (hd σ) = (roleOf rf (decide (t = ℓ)) b).toList := by
    simp only [roleF, hd, Regs.get, hRF, hKL, hS]
    have : ((mk ℓ t).head?.isNone) = decide (t = ℓ) := by
      by_cases h : t = ℓ
      · rw [(mk_head_none ℓ t).2 h]; simp [h]
      · have : (mk ℓ t).head? ≠ none := fun h' => h ((mk_head_none ℓ t).1 h')
        cases hm : (mk ℓ t).head? with
        | none => exact absurd hm this
        | some _ => simp [h]
    rw [this]
    cases rf <;> rfl
  have e1 := runs_pt .X2 1 roleF σ hInd (by rw [hR]; exact toList_len_le _)
  rw [hR] at e1
  simp only [Regs.set, Regs.get, hX2, List.append_nil] at e1
  have e2 := runs_adv { σ with X2 := (roleOf rf (decide (t = ℓ)) b).toList.reverse } ℓ j t b rest cc
    hKL hKJ hS hCC
  have e3 := runs_emitStep
    { σ with
      X2 := (roleOf rf (decide (t = ℓ)) b).toList.reverse,
      KL := mk ℓ (t + 1), KJ := mk j (t + 1), S := rest, CC := cc } x0 x1
    (roleOf rf (decide (t = ℓ)) b) h0 h1 (by cases roleOf rf (decide (t = ℓ)) b <;> rfl)
  have ht : (fun h : Key → Option BSym => (h .KJ).isNone) (hd σ) = false := by
    simp only [hd, Regs.get, hKJ]
    have : (mk j t).head? ≠ none := fun h' => htj ((mk_head_none j t).1 h')
    cases hm : (mk j t).head? with
    | none => exact absurd hm this
    | some _ => rfl
  refine ((e1.seq (e2.seq e3)).brF ht).congr ?_ |>.mono (by omega)
  cases σ; simp_all

/-! ## The equality flag `RF := [J = L]` -/

def eqJL : Prog :=
  .seq (copyProg .J .E1 .sc) (.seq (copyProg .L .E2 .sc) (.seq (syncPopProg .E1 .E2)
    (.seq (.branch (fun h => (h .E1).isNone && (h .E2).isNone) (pushProg .RF .one) skipP)
      (.seq (clearProg .E1) (clearProg .E2)))))

lemma rep_len (k : ℕ) : (rep k).length = k := by simp [rep]

lemma runs_eqJL (σ : Regs) (j ℓ : ℕ) (hJ : σ.J = rep j) (hL : σ.L = rep ℓ) (hE1 : σ.E1 = [])
    (hE2 : σ.E2 = []) (hsc : σ.sc = []) (hRF : σ.RF = []) :
    Runs eqJL σ { σ with RF := if j = ℓ then [.one] else [] } (12 * (j + ℓ) + 20) := by
  have e1 : Runs (copyProg .J .E1 .sc) σ { σ with E1 := rep j } (6 * j + 3) :=
    ((runs_copy .J .E1 .sc (by decide) (by decide) (by decide) σ hsc).congr
      (by simp [Regs.set, Regs.get, hJ, hE1])).mono (by simp [Regs.get, hJ, rep_len])
  have e2 : Runs (copyProg .L .E2 .sc) { σ with E1 := rep j } { σ with E1 := rep j, E2 := rep ℓ }
      (6 * ℓ + 3) :=
    ((runs_copy .L .E2 .sc (by decide) (by decide) (by decide) { σ with E1 := rep j } hsc).congr
      (by simp [Regs.set, Regs.get, hL, hE2])).mono (by simp [Regs.get, hL, rep_len])
  have e3 : Runs (syncPopProg .E1 .E2) { σ with E1 := rep j, E2 := rep ℓ }
      { σ with E1 := rep (j - min j ℓ), E2 := rep (ℓ - min j ℓ) } (3 * min j ℓ + 1) :=
    ((runs_syncpop .E1 .E2 (by decide) _).congr
      (by simp [Regs.set, Regs.get, rep, List.drop_replicate])).mono
      (by simp [Regs.get, rep_len])
  have e4 : Runs (.branch (fun h => (h .E1).isNone && (h .E2).isNone) (pushProg .RF .one) skipP)
      { σ with E1 := rep (j - min j ℓ), E2 := rep (ℓ - min j ℓ) }
      { σ with E1 := rep (j - min j ℓ), E2 := rep (ℓ - min j ℓ), RF := if j = ℓ then [.one] else [] }
      2 := by
    by_cases h : j = ℓ
    · subst h
      refine ((runs_push .RF .one _).brT ?_).congr ?_
      · simp [hd, Regs.get, rep]
      · simp [Regs.set, Regs.get, hRF]
    · refine ((runs_skip _).brF ?_).congr ?_
      · rcases Nat.lt_or_gt_of_ne h with h1 | h1
        · have : j - min j ℓ = 0 := by omega
          have h2 : ℓ - min j ℓ = (ℓ - min j ℓ - 1) + 1 := by omega
          simp only [hd, Regs.get, this, rep, List.replicate_zero, List.head?_nil, Option.isNone_none,
            Bool.true_and]
          rw [h2, List.replicate_succ]; rfl
        · have h2 : j - min j ℓ = (j - min j ℓ - 1) + 1 := by omega
          simp only [hd, Regs.get, rep]
          rw [h2, List.replicate_succ]; rfl
      · simp [h, hRF]
  have e5 : Runs (clearProg .E1)
      { σ with E1 := rep (j - min j ℓ), E2 := rep (ℓ - min j ℓ), RF := if j = ℓ then [.one] else [] }
      { σ with E1 := [], E2 := rep (ℓ - min j ℓ), RF := if j = ℓ then [.one] else [] }
      (3 * j + 1) :=
    ((runs_clear .E1 _).congr (by simp [Regs.set])).mono (by simp [Regs.get, rep_len] <;> omega)
  have e6 : Runs (clearProg .E2)
      { σ with E1 := [], E2 := rep (ℓ - min j ℓ), RF := if j = ℓ then [.one] else [] }
      { σ with RF := if j = ℓ then [.one] else [] } (3 * ℓ + 1) :=
    ((runs_clear .E2 _).congr (by cases σ; simp_all [Regs.set])).mono
      (by simp [Regs.get, rep_len] <;> omega)
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).congr rfl).mono ?_
  have : min j ℓ ≤ j := min_le_left _ _
  omega

/-! ## One row of the matrix -/

def cnt (j t : ℕ) : ℕ := if t ≤ j then t else t - 1

def colLoop : Prog := .loop (fun h => (h .CC).isSome) entryP

section row

variable (n ℓ j c0 : ℕ) (bt : ℕ → Bool) (rl : ℕ → Option BSym) (Sl : List BSym)
  (Wf : ℕ → List BSym)

def entSt (ρ : Regs) (t : ℕ) : Regs :=
  { ρ with
    KL := mk ℓ t, KJ := mk j t, CC := rep (n - t), S := Sl.drop t,
    X0 := (rl (c0 + cnt j t)).toList, X1 := (rl (c0 + cnt j t + 1)).toList,
    W := Wf (c0 + cnt j t) }

lemma runs_colLoop (ρ : Regs)
    (hS : ∀ t, t < n → Sl.drop t = toB (bt t) :: Sl.drop (t + 1))
    (hrl : ∀ t, t < n → t ≠ j →
      rl (c0 + cnt j t + 2) = roleOf (decide (j = ℓ)) (decide (t = ℓ)) (toB (bt t)))
    (hW : ∀ c, Wf (c + 1) = (encNat (pv (rl c) (rl (c + 1)) (rl (c + 2)))).reverse ++ Wf c)
    (hRF : ρ.RF = if j = ℓ then [.one] else []) (hX2 : ρ.X2 = []) :
    Runs colLoop (entSt n ℓ j c0 rl Sl Wf ρ 0) (entSt n ℓ j c0 rl Sl Wf ρ n) (n * 82 + 1) := by
  refine Runs.loopU _ entryP (entSt n ℓ j c0 rl Sl Wf ρ) 80 n (fun t ht => ⟨?_, ?_⟩) ?_
  · have : n - t = (n - t - 1) + 1 := by omega
    simp only [hd, Regs.get, entSt, rep]; rw [this, List.replicate_succ]; rfl
  · have hCC : (entSt n ℓ j c0 rl Sl Wf ρ t).CC = .one :: rep (n - (t + 1)) := by
      have : n - t = (n - (t + 1)) + 1 := by omega
      simp only [entSt, rep]; rw [this, List.replicate_succ]
    by_cases htj : t = j
    · subst htj
      refine ((runs_entry_diag _ ℓ t (toB (bt t)) (Sl.drop (t + 1)) _ rfl rfl
        (by simp only [entSt]; exact hS t ht) hCC).congr ?_).mono (by omega)
      have h1 : cnt t (t + 1) = cnt t t := by simp [cnt]
      simp only [entSt, h1]
    · have e := runs_entry_nd (entSt n ℓ j c0 rl Sl Wf ρ t) ℓ j t htj (decide (j = ℓ)) (toB (bt t))
        (Sl.drop (t + 1)) (rep (n - (t + 1))) (rl (c0 + cnt j t)) (rl (c0 + cnt j t + 1)) rfl rfl
        (by simp only [entSt]; exact hS t ht) hCC
        (by simp only [entSt, hRF]; by_cases h : j = ℓ <;> simp [h])
        (by simp only [entSt, hX2]) rfl rfl
      refine e.congr ?_
      have h1 : cnt j (t + 1) = cnt j t + 1 := by unfold cnt; split_ifs <;> omega
      rw [← hrl t ht htj]
      simp only [entSt, h1, ← Nat.add_assoc, hW]
  · simp [hd, Regs.get, entSt, rep]

def rowP : Prog :=
  .seq (copyProg .L .KL .sc) (.seq (copyProg .J .KJ .sc) (.seq eqJL (.seq (copyProg .N .CC .sc)
    (.seq colLoop (.seq (clearProg .KL) (.seq (clearProg .KJ) (clearProg .RF)))))))

lemma runs_rowP (ρ : Regs) (hj : j < n) (hℓ : ℓ < n)
    (hS : ∀ t, t < n → Sl.drop t = toB (bt t) :: Sl.drop (t + 1))
    (hrl : ∀ t, t < n → t ≠ j →
      rl (c0 + cnt j t + 2) = roleOf (decide (j = ℓ)) (decide (t = ℓ)) (toB (bt t)))
    (hW : ∀ c, Wf (c + 1) = (encNat (pv (rl c) (rl (c + 1)) (rl (c + 2)))).reverse ++ Wf c)
    (hL : ρ.L = rep ℓ) (hJ : ρ.J = rep j) (hN : ρ.N = rep n) (hKL : ρ.KL = []) (hKJ : ρ.KJ = [])
    (hRF : ρ.RF = []) (hCC : ρ.CC = []) (hE1 : ρ.E1 = []) (hE2 : ρ.E2 = []) (hsc : ρ.sc = [])
    (hX2 : ρ.X2 = []) (hS0 : ρ.S = Sl) (hX0 : ρ.X0 = (rl c0).toList)
    (hX1 : ρ.X1 = (rl (c0 + 1)).toList) (hW0 : ρ.W = Wf c0) :
    Runs rowP ρ
      { ρ with
        S := Sl.drop n, X0 := (rl (c0 + (n - 1))).toList, X1 := (rl (c0 + (n - 1) + 1)).toList,
        W := Wf (c0 + (n - 1)) } (200 * (n + 1)) := by
  have e1 : Runs (copyProg .L .KL .sc) ρ { ρ with KL := rep ℓ } (6 * ℓ + 3) :=
    ((runs_copy .L .KL .sc (by decide) (by decide) (by decide) ρ hsc).congr
      (by simp [Regs.set, Regs.get, hL, hKL])).mono (by simp [Regs.get, hL, rep_len])
  have e2 : Runs (copyProg .J .KJ .sc) { ρ with KL := rep ℓ } { ρ with KL := rep ℓ, KJ := rep j }
      (6 * j + 3) :=
    ((runs_copy .J .KJ .sc (by decide) (by decide) (by decide) { ρ with KL := rep ℓ } hsc).congr
      (by simp [Regs.set, Regs.get, hJ, hKJ])).mono (by simp [Regs.get, hJ, rep_len])
  have e3 := runs_eqJL { ρ with KL := rep ℓ, KJ := rep j } j ℓ hJ hL hE1 hE2 hsc hRF
  have e4 : Runs (copyProg .N .CC .sc)
      { ρ with KL := rep ℓ, KJ := rep j, RF := if j = ℓ then [.one] else [] }
      { ρ with KL := rep ℓ, KJ := rep j, RF := if j = ℓ then [.one] else [], CC := rep n }
      (6 * n + 3) :=
    ((runs_copy .N .CC .sc (by decide) (by decide) (by decide)
      { ρ with KL := rep ℓ, KJ := rep j, RF := if j = ℓ then [.one] else [] } hsc).congr
      (by simp [Regs.set, Regs.get, hN, hCC])).mono (by simp [Regs.get, hN, rep_len])
  have h0 : { ρ with KL := rep ℓ, KJ := rep j, RF := if j = ℓ then [.one] else [], CC := rep n } =
      entSt n ℓ j c0 rl Sl Wf { ρ with RF := if j = ℓ then [.one] else [] } 0 := by
    simp only [entSt, mk, cnt, Nat.zero_le, if_true, Nat.sub_zero, List.drop_zero, Nat.add_zero, rep]
    cases ρ; simp_all
  have e5 := runs_colLoop n ℓ j c0 bt rl Sl Wf { ρ with RF := if j = ℓ then [.one] else [] }
    hS hrl hW rfl hX2
  rw [← h0] at e5
  have hmkl : mk ℓ n = [.zero] := by simp [mk]; omega
  have hmkj : mk j n = [.zero] := by simp [mk]; omega
  have hcn : cnt j n = n - 1 := by simp [cnt]; omega
  have e6 := runs_clear .KL (entSt n ℓ j c0 rl Sl Wf { ρ with RF := if j = ℓ then [.one] else [] } n)
  have e7 := runs_clear .KJ ((entSt n ℓ j c0 rl Sl Wf { ρ with RF := if j = ℓ then [.one] else [] } n).set .KL [])
  have e8 := runs_clear .RF (((entSt n ℓ j c0 rl Sl Wf { ρ with RF := if j = ℓ then [.one] else [] } n).set .KL []).set .KJ [])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).congr ?_).mono ?_
  · simp only [entSt, Regs.set, hcn]
    cases ρ; simp_all [rep]
  · simp only [Regs.get, Regs.set, entSt, hmkl, hmkj, List.length_cons, List.length_nil]
    have : (if j = ℓ then [BSym.one] else []).length ≤ 1 := by split_ifs <;> simp
    nlinarith

end row

/-! ## One job -/

def lab (n q : ℕ) : ℕ := if q + 1 = n then 0 else q + 1

lemma lab_lt {n q : ℕ} (hq : q < n) : lab n q < n := by unfold lab; split_ifs <;> omega

lemma iotaN_lab {n q t : ℕ} (hq : q < n) (htj : t ≠ lab n q) :
    iotaN n (lab n q) t = q * (n - 1) + cnt (lab n q) t + 2 := by
  have hp : posR n (lab n q) = q := by
    unfold lab
    by_cases h : q + 1 = n
    · rw [if_pos h]; simp [posR]; omega
    · rw [if_neg h]; simp [posR]
  have hc : cidx (lab n q) t = cnt (lab n q) t := by unfold cidx cnt; split_ifs <;> omega
  unfold iotaN; rw [hp, hc]; ring

lemma roleN_eq (a : ℕ → ℕ → Bool) (ℓ j t : ℕ) :
    roleN a ℓ j t = roleOf (decide (j = ℓ)) (decide (t = ℓ)) (toB (a j t)) := by
  unfold roleN roleOf
  cases a j t <;> by_cases h1 : j = ℓ <;> by_cases h2 : t = ℓ <;> simp [h1, h2, toB]

def rowsP : Prog := .loop (fun h => (h .RC).isSome) (.seq rowP (.seq (popProg .RC) (pushProg .J .one)))

def jobP : Prog :=
  .seq (copyProg .M .S .sc) (.seq (pushProg .J .one) (.seq (copyProg .N .RC .sc) (.seq (popProg .RC)
    (.seq rowsP (.seq (clearProg .J) (.seq rowP (.seq emitStep (.seq emitStep
      (.seq (clearProg .X0) (clearProg .X1))))))))))

section job

variable (n ℓ : ℕ) (a : ℕ → ℕ → Bool) (Ml : List BSym) (Wf : ℕ → List BSym)

noncomputable def rowSt (ν : Regs) (q : ℕ) : Regs :=
  { ν with
    S := Ml.drop (q * n), J := rep (q + 1), RC := rep (n - 1 - q),
    X0 := (rlN n a ℓ (q * (n - 1))).toList, X1 := (rlN n a ℓ (q * (n - 1) + 1)).toList,
    W := Wf (q * (n - 1)) }

variable {n ℓ a Ml Wf}

lemma row_hyps (hMl : ∀ q t, q < n → t < n → Ml.drop (q * n + t) = toB (a (lab n q) t) :: Ml.drop (q * n + t + 1))
    (q : ℕ) (hq : q < n) :
    (∀ t, t < n → (Ml.drop (q * n)).drop t = toB (a (lab n q) t) :: (Ml.drop (q * n)).drop (t + 1)) ∧
    (∀ t, t < n → t ≠ lab n q → rlN n a ℓ (q * (n - 1) + cnt (lab n q) t + 2) =
      roleOf (decide (lab n q = ℓ)) (decide (t = ℓ)) (toB (a (lab n q) t))) := by
  refine ⟨fun t ht => by rw [List.drop_drop, List.drop_drop, hMl q t hq ht]; congr 1, ?_⟩
  intro t ht htj
  rw [← iotaN_lab hq htj, rlN_iota n a ℓ _ _ (lab_lt hq) ht (Ne.symm htj), roleN_eq]

lemma runs_jobP (ν : Regs) (hℓ : ℓ < n) (hMlen : Ml.length = n * n)
    (hMl : ∀ q t, q < n → t < n → Ml.drop (q * n + t) = toB (a (lab n q) t) :: Ml.drop (q * n + t + 1))
    (hW : ∀ c, Wf (c + 1) = (encNat (pv (rlN n a ℓ c) (rlN n a ℓ (c + 1)) (rlN n a ℓ (c + 2)))).reverse ++ Wf c)
    (hL : ν.L = rep ℓ) (hN : ν.N = rep n) (hM : ν.M = Ml) (hS : ν.S = []) (hJ : ν.J = [])
    (hRC : ν.RC = []) (hKL : ν.KL = []) (hKJ : ν.KJ = [])
    (hRF : ν.RF = []) (hCC : ν.CC = []) (hE1 : ν.E1 = []) (hE2 : ν.E2 = []) (hsc : ν.sc = [])
    (hX0 : ν.X0 = []) (hX1 : ν.X1 = []) (hX2 : ν.X2 = []) (hW0 : ν.W = Wf 0) :
    Runs jobP ν { ν with W := Wf (n * (n - 1) + 2) } (400 * (n + 1) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hrl0 : rlN n a ℓ 0 = none := rlN_none n a ℓ 0 (by omega)
  have hrl1 : rlN n a ℓ 1 = none := rlN_none n a ℓ 1 (by omega)
  -- setup
  have e1 : Runs (copyProg .M .S .sc) ν { ν with S := Ml } (6 * (n * n) + 3) :=
    ((runs_copy .M .S .sc (by decide) (by decide) (by decide) ν hsc).congr
      (by simp [Regs.set, Regs.get, hM, hS])).mono (by simp [Regs.get, hM, hMlen])
  have e2 : Runs (pushProg .J .one) { ν with S := Ml } { ν with S := Ml, J := rep 1 } 1 :=
    (runs_push .J .one _).congr (by simp [Regs.set, Regs.get, hJ, rep])
  have e3 : Runs (copyProg .N .RC .sc) { ν with S := Ml, J := rep 1 }
      { ν with S := Ml, J := rep 1, RC := rep n } (6 * n + 3) :=
    ((runs_copy .N .RC .sc (by decide) (by decide) (by decide) { ν with S := Ml, J := rep 1 } hsc).congr
      (by simp [Regs.set, Regs.get, hN, hRC])).mono (by simp [Regs.get, hN, rep_len])
  have e4 : Runs (popProg .RC) { ν with S := Ml, J := rep 1, RC := rep n }
      (rowSt n ℓ a Ml Wf ν 0) 1 :=
    (runs_pop .RC _).congr (by
      simp only [rowSt, Regs.set, Regs.get, Nat.zero_mul, List.drop_zero, Nat.zero_add, hrl0, hrl1,
        Option.toList_none, rep, List.tail_replicate, hW0]
      cases ν; simp_all)
  -- the rows `0, …, n-2`
  have eR : Runs rowsP (rowSt n ℓ a Ml Wf ν 0) (rowSt n ℓ a Ml Wf ν (n - 1))
      ((n - 1) * (200 * (n + 1) + 6) + 1) := by
    refine Runs.loopU _ _ (rowSt n ℓ a Ml Wf ν) _ (n - 1) (fun q hq => ⟨?_, ?_⟩) ?_
    · have : n - 1 - q = (n - 1 - q - 1) + 1 := by omega
      simp only [hd, Regs.get, rowSt, rep]; rw [this, List.replicate_succ]; rfl
    · have hlab : lab n q = q + 1 := by unfold lab; split_ifs <;> omega
      obtain ⟨hS', hrl'⟩ := row_hyps (ℓ := ℓ) hMl q (by omega)
      rw [hlab] at hS' hrl'
      have eA := runs_rowP n ℓ (q + 1) (q * (n - 1)) (a (q + 1)) (rlN n a ℓ) (Ml.drop (q * n)) Wf
        (rowSt n ℓ a Ml Wf ν q) (by omega) hℓ hS' hrl' hW hL rfl hN hKL hKJ hRF hCC hE1 hE2 hsc hX2
        rfl rfl rfl rfl
      have eB : Runs (popProg .RC) _ _ 1 := runs_pop .RC
        { rowSt n ℓ a Ml Wf ν q with
          S := (Ml.drop (q * n)).drop n, X0 := (rlN n a ℓ (q * (n - 1) + (n - 1))).toList,
          X1 := (rlN n a ℓ (q * (n - 1) + (n - 1) + 1)).toList, W := Wf (q * (n - 1) + (n - 1)) }
      have eC := runs_push .J .one (Regs.set
        { rowSt n ℓ a Ml Wf ν q with
          S := (Ml.drop (q * n)).drop n, X0 := (rlN n a ℓ (q * (n - 1) + (n - 1))).toList,
          X1 := (rlN n a ℓ (q * (n - 1) + (n - 1) + 1)).toList, W := Wf (q * (n - 1) + (n - 1)) }
        .RC (Regs.get { rowSt n ℓ a Ml Wf ν q with
          S := (Ml.drop (q * n)).drop n, X0 := (rlN n a ℓ (q * (n - 1) + (n - 1))).toList,
          X1 := (rlN n a ℓ (q * (n - 1) + (n - 1) + 1)).toList, W := Wf (q * (n - 1) + (n - 1)) } .RC).tail)
      refine ((eA.seq (eB.seq eC)).congr ?_).mono (by omega)
      have h1 : q * (n - 1) + (n - 1) = (q + 1) * (n - 1) := by ring
      have h2 : q * n + n = (q + 1) * n := by ring
      simp only [rowSt, Regs.set, Regs.get, List.drop_drop, h1, h2, rep, List.tail_replicate]
      have h3 : n - 1 - q - 1 = n - 1 - (q + 1) := by omega
      rw [h3]; rfl
    · simp [hd, Regs.get, rowSt, rep]
  -- the last row, `0`
  have eJ : Runs (clearProg .J) (rowSt n ℓ a Ml Wf ν (n - 1))
      { rowSt n ℓ a Ml Wf ν (n - 1) with J := [] } (3 * n + 1) :=
    ((runs_clear .J _).congr (by simp [Regs.set])).mono (by simp [Regs.get, rowSt, rep_len]; omega)
  have hlab : lab n (n - 1) = 0 := by unfold lab; split_ifs <;> omega
  obtain ⟨hS', hrl'⟩ := row_hyps (ℓ := ℓ) hMl (n - 1) (by omega)
  rw [hlab] at hS' hrl'
  have eL := runs_rowP n ℓ 0 ((n - 1) * (n - 1)) (a 0) (rlN n a ℓ) (Ml.drop ((n - 1) * n)) Wf
    { rowSt n ℓ a Ml Wf ν (n - 1) with J := [] } (by omega) hℓ hS' hrl' hW hL rfl hN hKL hKJ hRF
    hCC hE1 hE2 hsc hX2 rfl rfl rfl rfl
  have hm2 : (n - 1) * (n - 1) + (n - 1) = n * (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp; ring
  have hdrop : (Ml.drop ((n - 1) * n)).drop n = [] := by
    rw [List.drop_drop]; apply List.drop_eq_nil_of_le
    rw [hMlen]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp; nlinarith
  rw [hm2, hdrop] at eL
  -- the two final machines
  have hrlm : rlN n a ℓ (n * (n - 1) + 1 + 1) = none := rlN_none n a ℓ _ (by omega)
  have hrlm' : rlN n a ℓ (n * (n - 1) + 1 + 2) = none := rlN_none n a ℓ _ (by omega)
  have eE1 := runs_emitStep
    { { rowSt n ℓ a Ml Wf ν (n - 1) with J := [] } with
      S := [], X0 := (rlN n a ℓ (n * (n - 1))).toList,
      X1 := (rlN n a ℓ (n * (n - 1) + 1)).toList, W := Wf (n * (n - 1)) }
    (rlN n a ℓ (n * (n - 1))) (rlN n a ℓ (n * (n - 1) + 1)) none rfl rfl (by simp [rowSt, hX2])
  have eE2 := runs_emitStep
    { { { rowSt n ℓ a Ml Wf ν (n - 1) with J := [] } with
      S := [], X0 := (rlN n a ℓ (n * (n - 1))).toList,
      X1 := (rlN n a ℓ (n * (n - 1) + 1)).toList, W := Wf (n * (n - 1)) } with
      W := (encNat (pv (rlN n a ℓ (n * (n - 1))) (rlN n a ℓ (n * (n - 1) + 1)) none)).reverse ++
        Wf (n * (n - 1)),
      X0 := (rlN n a ℓ (n * (n - 1) + 1)).toList, X1 := (none : Option BSym).toList, X2 := [] }
    (rlN n a ℓ (n * (n - 1) + 1)) none none rfl rfl rfl
  have eX0 := runs_clear .X0
    { { { { rowSt n ℓ a Ml Wf ν (n - 1) with J := [] } with
      S := [], X0 := (rlN n a ℓ (n * (n - 1))).toList,
      X1 := (rlN n a ℓ (n * (n - 1) + 1)).toList, W := Wf (n * (n - 1)) } with
      W := (encNat (pv (rlN n a ℓ (n * (n - 1))) (rlN n a ℓ (n * (n - 1) + 1)) none)).reverse ++
        Wf (n * (n - 1)),
      X0 := (rlN n a ℓ (n * (n - 1) + 1)).toList, X1 := (none : Option BSym).toList, X2 := [] } with
      W := (encNat (pv (rlN n a ℓ (n * (n - 1) + 1)) none none)).reverse ++
        ((encNat (pv (rlN n a ℓ (n * (n - 1))) (rlN n a ℓ (n * (n - 1) + 1)) none)).reverse ++
        Wf (n * (n - 1))),
      X0 := (none : Option BSym).toList, X1 := (none : Option BSym).toList, X2 := [] }
  have eX1 := runs_clear .X1 (Regs.set
    { { { { rowSt n ℓ a Ml Wf ν (n - 1) with J := [] } with
      S := [], X0 := (rlN n a ℓ (n * (n - 1))).toList,
      X1 := (rlN n a ℓ (n * (n - 1) + 1)).toList, W := Wf (n * (n - 1)) } with
      W := (encNat (pv (rlN n a ℓ (n * (n - 1))) (rlN n a ℓ (n * (n - 1) + 1)) none)).reverse ++
        Wf (n * (n - 1)),
      X0 := (rlN n a ℓ (n * (n - 1) + 1)).toList, X1 := (none : Option BSym).toList, X2 := [] } with
      W := (encNat (pv (rlN n a ℓ (n * (n - 1) + 1)) none none)).reverse ++
        ((encNat (pv (rlN n a ℓ (n * (n - 1))) (rlN n a ℓ (n * (n - 1) + 1)) none)).reverse ++
        Wf (n * (n - 1))),
      X0 := (none : Option BSym).toList, X1 := (none : Option BSym).toList, X2 := [] } .X0 [])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (eR.seq (eJ.seq (eL.seq (eE1.seq (eE2.seq
    (eX0.seq eX1)))))))))).congr ?_).mono ?_
  · have hW1 := hW (n * (n - 1))
    have hW2 := hW (n * (n - 1) + 1)
    rw [hrlm] at hW1
    rw [hrlm, hrlm'] at hW2
    simp only [Regs.set, Regs.get, rowSt, Option.toList_none]
    rw [← hW1, ← hW2]
    cases ν; simp_all [rep]
  · simp only [Regs.get, Regs.set, rowSt, Option.toList_none, List.length_nil]
    have h1 : (n - 1) * (200 * (n + 1) + 6) ≤ n * (206 * (n + 1)) :=
      Nat.mul_le_mul (by omega) (by nlinarith)
    have h2 : ((rlN n a ℓ (n * (n - 1) + 1)).toList).length ≤ 1 := toList_len_le _
    nlinarith

end job

end NWRed



set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity
open SchedComplexity.NoWait (dhpCode)

/-! ## All jobs -/

def jobsP : Prog := .loop (fun h => (h .JB).isSome) (.seq jobP (.seq (popProg .JB) (pushProg .L .one)))

section jobs

variable (n : ℕ) (a : ℕ → ℕ → Bool) (pre : List ℕ)

noncomputable def Pt (ℓ r : ℕ) : ℕ := pv (rlN n a ℓ r) (rlN n a ℓ (r + 1)) (rlN n a ℓ (r + 2))

def mN (n : ℕ) : ℕ := n * (n - 1) + 2

noncomputable def outRows (ℓ : ℕ) : List ℕ :=
  (List.range ℓ).flatMap (fun ℓ' => (List.range (mN n)).map (Pt n a ℓ'))

noncomputable def Wjob (ℓ c : ℕ) : List BSym :=
  (encNats (pre ++ outRows n a ℓ ++ (List.range c).map (Pt n a ℓ))).reverse

lemma encNats_app (l l' : List ℕ) : encNats (l ++ l') = encNats l ++ encNats l' := by
  simp [encNats]

lemma Wjob_succ (ℓ c : ℕ) : Wjob n a pre ℓ (c + 1) =
    (encNat (pv (rlN n a ℓ c) (rlN n a ℓ (c + 1)) (rlN n a ℓ (c + 2)))).reverse ++ Wjob n a pre ℓ c := by
  simp only [Wjob, List.range_succ, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
    encNats_app, List.reverse_append]
  simp [encNats, Pt]

lemma Wjob_end (ℓ : ℕ) : Wjob n a pre ℓ (mN n) = Wjob n a pre (ℓ + 1) 0 := by
  simp [Wjob, outRows, List.range_succ, List.flatMap_append]

noncomputable def jobSt (Γ : Regs) (ℓ : ℕ) : Regs :=
  { Γ with L := rep ℓ, JB := rep (n - ℓ), W := Wjob n a pre ℓ 0 }

variable {n a pre}

lemma runs_jobsP (Γ : Regs) (Ml : List BSym) (hMlen : Ml.length = n * n)
    (hMl : ∀ q t, q < n → t < n → Ml.drop (q * n + t) = toB (a (lab n q) t) :: Ml.drop (q * n + t + 1))
    (hN : Γ.N = rep n) (hM : Γ.M = Ml) (hS : Γ.S = []) (hJ : Γ.J = [])
    (hRC : Γ.RC = []) (hKL : Γ.KL = []) (hKJ : Γ.KJ = [])
    (hRF : Γ.RF = []) (hCC : Γ.CC = []) (hE1 : Γ.E1 = []) (hE2 : Γ.E2 = []) (hsc : Γ.sc = [])
    (hX0 : Γ.X0 = []) (hX1 : Γ.X1 = []) (hX2 : Γ.X2 = []) :
    Runs jobsP (jobSt n a pre Γ 0) (jobSt n a pre Γ n) (n * (400 * (n + 1) ^ 2 + 6) + 1) := by
  refine Runs.loopU _ _ (jobSt n a pre Γ) _ n (fun ℓ hℓ => ⟨?_, ?_⟩) ?_
  · have : n - ℓ = (n - ℓ - 1) + 1 := by omega
    simp only [hd, Regs.get, jobSt, rep]; rw [this, List.replicate_succ]; rfl
  · have e1 := runs_jobP (ℓ := ℓ) (a := a) (Ml := Ml) (Wf := Wjob n a pre ℓ) (jobSt n a pre Γ ℓ) hℓ
      hMlen hMl (Wjob_succ n a pre ℓ) rfl hN hM hS hJ hRC hKL hKJ hRF hCC hE1 hE2 hsc hX0 hX1 hX2 rfl
    have e2 := runs_pop .JB { jobSt n a pre Γ ℓ with W := Wjob n a pre ℓ (n * (n - 1) + 2) }
    have e3 := runs_push .L .one (Regs.set { jobSt n a pre Γ ℓ with W := Wjob n a pre ℓ (n * (n - 1) + 2) }
      .JB (Regs.get { jobSt n a pre Γ ℓ with W := Wjob n a pre ℓ (n * (n - 1) + 2) } .JB).tail)
    refine ((e1.seq (e2.seq e3)).congr ?_).mono (by omega)
    have hm : n * (n - 1) + 2 = mN n := rfl
    rw [hm, Wjob_end]
    simp only [jobSt, Regs.set, Regs.get, rep, List.tail_replicate, List.replicate_succ]
    have : n - ℓ - 1 = n - (ℓ + 1) := by omega
    rw [this]
  · simp [hd, Regs.get, jobSt, rep]

end jobs

/-! ## Facts about the codes (from the rural postman reduction) -/

lemma encNats_cons' (k : ℕ) (l : List ℕ) : encNats (k :: l) = encNat k ++ encNats l := by
  simp [encNats]

lemma encNats_append' (l l' : List ℕ) : encNats (l ++ l') = encNats l ++ encNats l' := by
  simp [encNats]

lemma encNat_eq' (k : ℕ) : encNat k = enc (Nat.bits k) ++ [BSym.sep] := by
  simp [encNat, enc, toB]

def adjB (bs : List Bool) (n s t : ℕ) : Bool := bs.getD (s * n + t) false

lemma code_inj {n n' : ℕ} {bs bs' : List Bool} (h : code n bs = code n' bs') : n = n' ∧ bs = bs' := by
  have hb : tokP false (rest (code n bs)).tail = some bs := by
    unfold code; rw [rest_code]; exact tokP_flat bs
  obtain ⟨h1, h2⟩ := code_unique (code n bs) bs hb n' bs' h
  obtain ⟨h3, _⟩ := code_unique (code n bs) bs hb n bs rfl
  exact ⟨h3.trans h1.symm, h2.symm⟩

lemma length_code (n : ℕ) (bs : List Bool) : bs.length ≤ (code n bs).length := by
  unfold code
  have := length_flat_tokB bs
  simp only [List.length_append, List.length_cons]; omega

/-- the reduction function, read off the code -/
noncomputable def decodeThen (g : ℕ → List Bool → List BSym) (w : List BSym) : List BSym :=
  open Classical in
  if h : ∃ p : ℕ × List Bool, p.2.length = p.1 * p.1 ∧ w = code p.1 p.2 then
    g (Classical.choose h).1 (Classical.choose h).2
  else []

lemma decodeThen_code (g : ℕ → List Bool → List BSym) (n : ℕ) (bs : List Bool)
    (hbs : bs.length = n * n) : decodeThen g (code n bs) = g n bs := by
  have h : ∃ p : ℕ × List Bool, p.2.length = p.1 * p.1 ∧ code n bs = code p.1 p.2 :=
    ⟨(n, bs), hbs, rfl⟩
  unfold decodeThen
  rw [dif_pos h]
  obtain ⟨_, hc⟩ := Classical.choose_spec h
  obtain ⟨h1, h2⟩ := code_inj hc
  rw [← h1, ← h2]

lemma decodeThen_invalid (g : ℕ → List Bool → List BSym) (w : List BSym)
    (h : ∀ n bs, bs.length = n * n → w ≠ code n bs) : decodeThen g w = [] := by
  unfold decodeThen
  rw [dif_neg]
  rintro ⟨p, hp, hc⟩
  exact h p.1 p.2 hp hc


lemma n_le_of_sq {n m : ℕ} (h : m = n * n) : n ≤ m := by
  subst h; rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Nat.le_mul_of_pos_left n h


lemma ofFn_val {α : Type} (n : ℕ) (h : ℕ → α) :
    List.ofFn (fun v : Fin n => h v.val) = (List.range n).map h := by
  apply List.ext_getElem <;> simp

lemma finRange_flatMap {α : Type} (n : ℕ) (G : ℕ → List α) :
    (List.finRange n).flatMap (fun s => G s.val) = (List.range n).flatMap G := by
  rw [List.flatMap, List.flatMap, ← List.ofFn_eq_map, ofFn_val]

lemma finRange_flatMap' {α : Type} (n : ℕ) (G : Fin n → List α) (G' : ℕ → List α)
    (hG : ∀ s : Fin n, G s = G' s.val) :
    (List.finRange n).flatMap G = (List.range n).flatMap G' := by
  rw [← finRange_flatMap]; congr 1; funext s; exact hG s

lemma flat_ofFn {α : Type} (m n : ℕ) (f : ℕ → α) :
    (List.ofFn fun u : Fin m => List.ofFn fun v : Fin n => f (u * n + v)).flatten =
      (List.range (m * n)).map f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.coe_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    congr 1
    rw [ofFn_val n (fun v => f (m * n + v))]
    rfl

/-! ## adjacency matrices versus entry lists -/

def matBits {n : ℕ} (adj : Fin n → Fin n → Bool) : List Bool :=
  (List.ofFn fun u => List.ofFn fun v => adj u v).flatten

def adjOf (n : ℕ) (bs : List Bool) : Fin n → Fin n → Bool := fun u v => adjB bs n u.val v.val

def mf {n : ℕ} (adj : Fin n → Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n * n then
    adj ⟨i / n, Nat.div_lt_of_lt_mul h⟩ ⟨i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
      rintro rfl; simp at h))⟩
  else false

lemma mf_eq {n : ℕ} (adj : Fin n → Fin n → Bool) (u v : Fin n) : mf adj (u.val * n + v.val) = adj u v := by
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact u.elim0)
  have h1 : u.val * n + v.val < n * n := by
    have := u.isLt; have := v.isLt; nlinarith
  unfold mf
  rw [dif_pos h1]
  congr 1
  · ext; simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt v.isLt, zero_add]
  · ext; simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]

lemma matBits_eq {n : ℕ} (adj : Fin n → Fin n → Bool) : matBits adj = (List.range (n * n)).map (mf adj) := by
  rw [← flat_ofFn]; unfold matBits
  exact congrArg List.flatten (congrArg List.ofFn (funext fun u =>
    congrArg List.ofFn (funext fun v => (mf_eq adj u v).symm)))

lemma length_matBits {n : ℕ} (adj : Fin n → Fin n → Bool) : (matBits adj).length = n * n := by
  rw [matBits_eq]; simp

lemma adjOf_matBits {n : ℕ} (adj : Fin n → Fin n → Bool) : adjOf n (matBits adj) = adj := by
  funext u v
  have h1 : u.val * n + v.val < n * n := by
    have := u.isLt; have := v.isLt; nlinarith
  simp only [adjOf, adjB]
  rw [matBits_eq, List.getD_eq_getElem _ _ (by simpa using h1)]
  simp [mf_eq]

lemma matBits_adjOf (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) : matBits (adjOf n bs) = bs := by
  unfold matBits adjOf adjB
  rw [flat_ofFn n n (fun i => bs.getD i false)]
  apply List.ext_getElem
  · simp [hbs]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

lemma encNats_bits (bs : List Bool) :
    encNats (bs.map fun b => if b then 1 else 0) = bs.flatMap tokB := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, encNats_cons', ih, List.flatMap_cons]
    cases b
    · simp [encNat, tokB]
    · simp [encNat, tokB]

lemma dhpCode_eq {n : ℕ} (adj : Fin n → Fin n → Bool) : dhpCode adj = code n (matBits adj) := by
  unfold dhpCode code
  rw [encNats_cons', encNat_eq', List.append_assoc, List.singleton_append, ← encNats_bits]
  congr 3
  unfold matBits
  rw [List.map_flatten, List.map_ofFn]
  exact congrArg List.flatten (congrArg List.ofFn (funext fun u => by simp only [Function.comp_apply, List.map_ofFn]; rfl))


lemma enc_split : ∀ {a b : List Bool} {r r' : List BSym},
    enc a ++ BSym.sep :: r = enc b ++ BSym.sep :: r' → a = b ∧ r = r' := by
  intro a
  induction a with
  | nil =>
    intro b r r' h
    cases b with
    | nil => simpa using h
    | cons y b => cases y <;> simp [toB] at h
  | cons x a ih =>
    intro b r r' h
    cases b with
    | nil => cases x <;> simp [toB] at h
    | cons y b =>
      simp only [enc_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hxy : x = y := by cases x <;> cases y <;> simp_all [toB]
      obtain ⟨h3, h4⟩ := ih h2
      exact ⟨by rw [hxy, h3], h4⟩

lemma encNats_inj : ∀ (l l' : List ℕ), encNats l = encNats l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons y l' => rw [encNats_cons', encNat_eq'] at h; simp [encNats] at h
  | cons x l ih =>
    intro l' h
    cases l' with
    | nil => rw [encNats_cons', encNat_eq'] at h; simp [encNats] at h
    | cons y l' =>
      rw [encNats_cons', encNats_cons', encNat_eq', encNat_eq', List.append_assoc,
        List.append_assoc, List.singleton_append, List.singleton_append] at h
      obtain ⟨h1, h2⟩ := enc_split h
      have hxy : x = y := by rw [← bval_bits x, h1, bval_bits]
      rw [hxy, ih l' h2]


/-! ## Rotating the matrix: row `0` goes to the end -/

def rotP : Prog :=
  .seq (copyProg .N .CC .sc) (.seq (mvNProg .CC .M .X) (.seq (mvProg .M .Z)
    (.seq (mvProg .X .M) (mvProg .Z .M))))

lemma runs_rotP (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs rotP (st6 n bs) { st6 n bs with M := enc (bs.drop n ++ bs.take n) }
      (30 * (n * n + n + 1)) := by
  have hn : n ≤ n * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left n h
  have e1 : Runs (copyProg .N .CC .sc) (st6 n bs) { st6 n bs with CC := rep n } (6 * n + 3) :=
    ((runs_copy .N .CC .sc (by decide) (by decide) (by decide) _ rfl).congr
      (by simp [Regs.set, Regs.get, st6, Regs.empty, rep])).mono (by simp [Regs.get, st6])
  have e2 : Runs (mvNProg .CC .M .X) { st6 n bs with CC := rep n }
      { st6 n bs with M := (enc bs).drop n, X := ((enc bs).take n).reverse } (5 * n + 1) :=
    (runs_mvN .CC .M .X (by decide) (by decide) (by decide) n _ (enc bs) rfl rfl
      (by simp [hbs, hn])).congr (by simp [Regs.set, Regs.get, st6, Regs.empty])
  have e3 : Runs (mvProg .M .Z)
      { st6 n bs with M := (enc bs).drop n, X := ((enc bs).take n).reverse }
      { st6 n bs with M := [], X := ((enc bs).take n).reverse, Z := ((enc bs).drop n).reverse }
      (3 * (n * n) + 1) :=
    ((runs_mv .M .Z (by decide) _).congr (by simp [Regs.set, Regs.get, st6, Regs.empty])).mono
      (by simp [Regs.get, hbs])
  have e4 : Runs (mvProg .X .M)
      { st6 n bs with M := [], X := ((enc bs).take n).reverse, Z := ((enc bs).drop n).reverse }
      { st6 n bs with M := (enc bs).take n, Z := ((enc bs).drop n).reverse } (3 * n + 1) :=
    ((runs_mv .X .M (by decide) _).congr (by simp [Regs.set, Regs.get, st6, Regs.empty])).mono
      (by simp [Regs.get, hbs, hn])
  have e5 : Runs (mvProg .Z .M)
      { st6 n bs with M := (enc bs).take n, Z := ((enc bs).drop n).reverse }
      { st6 n bs with M := enc (bs.drop n ++ bs.take n) } (3 * (n * n) + 1) :=
    ((runs_mv .Z .M (by decide) _).congr (by simp [Regs.set, Regs.get, st6, Regs.empty, enc,
      List.map_drop, List.map_take])).mono (by simp [Regs.get, hbs])
  exact ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr rfl).mono (by nlinarith)

/-- the rotated stream yields the rows `1, …, n-1, 0` -/
lemma rot_stream (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (q t : ℕ) (hq : q < n)
    (ht : t < n) :
    (enc (bs.drop n ++ bs.take n)).drop (q * n + t) =
      toB (adjB bs n (lab n q) t) :: (enc (bs.drop n ++ bs.take n)).drop (q * n + t + 1) := by
  have hlen : (bs.drop n ++ bs.take n).length = n * n := by
    simp [hbs]; have : n ≤ n * n := by nlinarith
    omega
  have hidx : q * n + t < n * n := by nlinarith
  have hi : q * n + t < (enc (bs.drop n ++ bs.take n)).length := by
    simp only [enc, List.length_map, hlen]; exact hidx
  rw [List.drop_eq_getElem_cons hi]
  congr 1
  simp only [enc, List.getElem_map]
  congr 1
  unfold adjB lab
  by_cases hq1 : q + 1 = n
  · rw [if_pos hq1]
    have h1 : n * n - n ≤ q * n + t := by
      have : q * n = n * n - n := by
        rw [← hq1]; ring_nf; omega
      omega
    rw [List.getElem_append_right (by simp [hbs]; omega)]
    simp only [List.getElem_take, List.length_drop, hbs]
    rw [List.getD_eq_getElem _ _ (by omega)]
    congr 1; simp
    have : q * n = n * n - n := by rw [← hq1]; ring_nf; omega
    omega
  · rw [if_neg hq1]
    have h1 : q * n + t < n * n - n := by
      have : (q + 1) * n + t < n * n := by
        have : q + 1 < n := by omega
        nlinarith
      have h2 : (q + 1) * n = q * n + n := by ring
      omega
    rw [List.getElem_append_left (by simp [hbs]; omega)]
    simp only [List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by
      have : (q + 1) * n + t < n * n := by
        have : q + 1 < n := by omega
        nlinarith
      omega)]
    congr 1; ring

/-! ## Unary arithmetic -/

lemma flatten_rep' (c k : ℕ) (x : BSym) :
    (List.replicate c (List.replicate k x)).flatten = List.replicate (c * k) x := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [List.length_flatten, List.sum_replicate], ?_⟩
  intro b hb
  rw [List.mem_flatten] at hb
  obtain ⟨l, hl, hb⟩ := hb
  rw [List.mem_replicate] at hl
  rw [hl.2] at hb
  exact (List.mem_replicate.1 hb).2

lemma rep_add (x y : ℕ) : rep x ++ rep y = rep (x + y) := by unfold rep; rw [← List.replicate_add]

def copyN (a b : Key) : ℕ → Prog
  | 0 => skipP
  | k + 1 => .seq (copyProg a b .sc) (copyN a b k)

lemma runs_copyN (a b : Key) (hab : a ≠ b) (ha : a ≠ .sc) (hb : b ≠ .sc) (x : ℕ) :
    ∀ (k y : ℕ) (σ : Regs), σ.get a = rep x → σ.get b = rep y → σ.sc = [] →
      Runs (copyN a b k) σ (σ.set b (rep (k * x + y))) (k * (6 * x + 4) + 1) := by
  intro k
  induction k with
  | zero =>
    intro y σ _ hB _
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [← hB, Regs.set_get]; exact runs_skip σ
  | succ k ih =>
    intro y σ hA hB hsc
    have e1 := runs_copy a b .sc hab ha hb σ hsc
    rw [hA, hB, rep_add] at e1
    have e2 := ih (x + y) (σ.set b (rep (x + y)))
      (by rw [Regs.get_set, if_neg hab, hA]) (Regs.get_set_self _ _ _)
      (by show (σ.set b (rep (x + y))).get .sc = []; rw [Regs.get_set, if_neg (Ne.symm hb)]; exact hsc)
    refine ((e1.seq e2).congr ?_).mono ?_
    · rw [Regs.set_set]; congr 2; ring
    · rw [rep_len]; nlinarith

/-! ## The number of machines `m = n(n-1) + 2` -/

def repUm : Prog := repProg .U .Um .G1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def mP : Prog :=
  .seq (copyProg .N .U .sc) (.seq (popProg .U) (.seq (copyProg .N .G1 .sc) (.seq repUm
    (.seq (pushProg .Um .one) (.seq (pushProg .Um .one) (.seq (clearProg .U)
      (.seq (copyProg .Um .U .sc) (u2bProg .U .Bm))))))))

lemma runs_mP (σ : Regs) (n : ℕ) (hN : σ.N = rep n) (hU : σ.U = []) (hG1 : σ.G1 = [])
    (hUm : σ.Um = []) (hBm : σ.Bm = []) (hsc : σ.sc = []) (hT : σ.T = []) :
    Runs mP σ { σ with Um := rep (mN n), Bm := enc (Nat.bits (mN n)) } (100 * (n + 1) ^ 4) := by
  have e1 : Runs (copyProg .N .U .sc) σ { σ with U := rep n } (6 * n + 3) :=
    ((runs_copy .N .U .sc (by decide) (by decide) (by decide) σ hsc).congr
      (by simp [Regs.set, Regs.get, hN, hU])).mono (by simp [Regs.get, hN, rep_len])
  have e2 : Runs (popProg .U) { σ with U := rep n } { σ with U := rep (n - 1) } 1 :=
    (runs_pop .U _).congr (by simp [Regs.set, Regs.get, rep, List.tail_replicate])
  have e3 : Runs (copyProg .N .G1 .sc) { σ with U := rep (n - 1) }
      { σ with U := rep (n - 1), G1 := rep n } (6 * n + 3) :=
    ((runs_copy .N .G1 .sc (by decide) (by decide) (by decide) { σ with U := rep (n - 1) } hsc).congr
      (by simp [Regs.set, Regs.get, hN, hG1])).mono (by simp [Regs.get, hN, rep_len])
  have e4 : Runs repUm { σ with U := rep (n - 1), G1 := rep n }
      { σ with U := rep (n - 1), Um := rep (n * (n - 1)) } ((6 * (n - 1) + 7) * n + 1) :=
    ((runs_rep .U .Um .G1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      { σ with U := rep (n - 1), G1 := rep n } hsc).congr
      (by simp [Regs.set, Regs.get, hG1, hUm, rep, flatten_rep'])).mono
      (by simp [Regs.get, rep_len])
  have e5 : Runs (pushProg .Um .one) { σ with U := rep (n - 1), Um := rep (n * (n - 1)) }
      { σ with U := rep (n - 1), Um := rep (n * (n - 1) + 1) } 1 :=
    (runs_push .Um .one _).congr (by simp [Regs.set, Regs.get, rep, List.replicate_succ])
  have e6 : Runs (pushProg .Um .one) { σ with U := rep (n - 1), Um := rep (n * (n - 1) + 1) }
      { σ with U := rep (n - 1), Um := rep (mN n) } 1 :=
    (runs_push .Um .one _).congr (by simp [Regs.set, Regs.get, rep, List.replicate_succ, mN])
  have e7 : Runs (clearProg .U) { σ with U := rep (n - 1), Um := rep (mN n) }
      { σ with Um := rep (mN n) } (3 * n + 1) :=
    ((runs_clear .U _).congr (by simp [Regs.set, hU])).mono (by simp [Regs.get, rep_len] <;> omega)
  have e8 : Runs (copyProg .Um .U .sc) { σ with Um := rep (mN n) }
      { σ with Um := rep (mN n), U := rep (mN n) } (6 * mN n + 3) :=
    ((runs_copy .Um .U .sc (by decide) (by decide) (by decide) { σ with Um := rep (mN n) } hsc).congr
      (by simp [Regs.set, Regs.get, hU])).mono (by simp [Regs.get, rep_len])
  have e9 := runs_u2b .U .Bm (by decide) (by decide) (by decide) (mN n)
    { σ with Um := rep (mN n), U := rep (mN n) } 0 rfl (by simp [Regs.get, hBm, enc]) hT
  rw [Nat.zero_add] at e9
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))).congr ?_).mono ?_
  · simp [Regs.set, hU]
  · try simp only [Nat.zero_add, Regs.get, rep_len]
    have hm : mN n ≤ 2 * (n + 1) ^ 2 := by
      unfold mN
      have : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      nlinarith
    generalize hX : (n + 1) ^ 2 = X at hm
    have hX4 : (n + 1) ^ 4 = X * X := by rw [← hX]; ring
    rw [hX4]
    have hnX : n + 1 ≤ X := by rw [← hX]; nlinarith
    have h1 : (6 * (n - 1) + 7) * n ≤ 7 * X := by
      have : 6 * (n - 1) + 7 ≤ 7 * (n + 1) := by omega
      have h0 : 7 * (n + 1) * n ≤ 7 * X := by rw [← hX]; nlinarith
      nlinarith
    have h2 : mN n * (6 * mN n + 15) ≤ (2 * X) * (6 * (2 * X) + 15) := Nat.mul_le_mul hm (by omega)
    nlinarith

/-! ## The thresholds -/

def YSpec (yP : Prog) (yv : ℕ → ℕ) : Prop :=
  ∀ (σ : Regs) (n : ℕ), σ.N = rep n → σ.Um = rep (mN n) → σ.U = [] → σ.G1 = [] → σ.G2 = [] →
    σ.sc = [] → σ.Uy = [] → Runs yP σ { σ with Uy := rep (yv n) } (1000 * (n + 1) ^ 3)

def yAP : Prog :=
  .seq (copyProg .N .U .sc) (.seq (popProg .U) (.seq (copyN .U .Uy 7) (.seq (clearProg .U)
    (copyN .Um .Uy 5))))

def yAv (n : ℕ) : ℕ := (n - 1) * (5 + 2 * 1) + SchedComplexity.NoWait.numMachines n * 5

lemma mN_le (n : ℕ) : mN n ≤ 2 * (n + 1) ^ 2 := by
  unfold mN
  have : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith

lemma yAP_spec : YSpec yAP yAv := by
  intro σ n hN hUm hU hG1 hG2 hsc hUy
  have e1 : Runs (copyProg .N .U .sc) σ { σ with U := rep n } (6 * n + 3) :=
    ((runs_copy .N .U .sc (by decide) (by decide) (by decide) σ hsc).congr
      (by simp [Regs.set, Regs.get, hN, hU])).mono (by simp [Regs.get, hN, rep_len])
  have e2 : Runs (popProg .U) { σ with U := rep n } { σ with U := rep (n - 1) } 1 :=
    (runs_pop .U _).congr (by simp [Regs.set, Regs.get, rep, List.tail_replicate])
  have e3 : Runs (copyN .U .Uy 7) { σ with U := rep (n - 1) }
      { σ with U := rep (n - 1), Uy := rep (7 * (n - 1)) } (7 * (6 * (n - 1) + 4) + 1) :=
    (runs_copyN .U .Uy (by decide) (by decide) (by decide) (n - 1) 7 0 { σ with U := rep (n - 1) } rfl
      (by simp [Regs.get, hUy, rep]) hsc).congr (by simp [Regs.set])
  have e4 : Runs (clearProg .U) { σ with U := rep (n - 1), Uy := rep (7 * (n - 1)) }
      { σ with Uy := rep (7 * (n - 1)) } (3 * n + 1) :=
    ((runs_clear .U _).congr (by simp [Regs.set, hU])).mono (by simp [Regs.get, rep_len] <;> omega)
  have e5 : Runs (copyN .Um .Uy 5) { σ with Uy := rep (7 * (n - 1)) }
      { σ with Uy := rep (yAv n) } (5 * (6 * mN n + 4) + 1) :=
    (runs_copyN .Um .Uy (by decide) (by decide) (by decide) (mN n) 5 (7 * (n - 1))
      { σ with Uy := rep (7 * (n - 1)) } hUm
      rfl hsc).congr (by
        simp only [Regs.set, yAv, SchedComplexity.NoWait.numMachines]
        congr 2; unfold mN; ring)
  refine ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr rfl).mono ?_
  have := mN_le n
  have h1 : 1 ≤ (n + 1) := by omega
  have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right h1 (by omega)
  have h3 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  omega

def yBP : Prog :=
  .seq (copyProg .N .U .sc) (.seq (popProg .U) (.seq (copyProg .N .G1 .sc)
    (.seq (repProg .U .G2 .G1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (.seq (halfProg .G2 .G1) (.seq (copyN .G1 .Uy 7) (.seq (clearProg .G1) (.seq (clearProg .U)
    (.seq (copyProg .N .G2 .sc)
    (.seq (repProg .Um .G1 .G2 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (.seq (copyN .G1 .Uy 5) (clearProg .G1)))))))))))

def yBv (n : ℕ) : ℕ := 7 * (n * (n - 1) / 2) + 5 * (n * mN n)

lemma even_mul_pred (n : ℕ) : n * (n - 1) = 2 * (n * (n - 1) / 2) := by
  have : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (n - 1), by rw [hk]; ring⟩
    · exact ⟨n * k, by rw [hk]; simp; ring⟩
  omega

lemma yBP_spec : YSpec yBP yBv := by
  intro σ n hN hUm hU hG1 hG2 hsc hUy
  set c := n * (n - 1) / 2 with hc
  have hev := even_mul_pred n
  have e1 : Runs (copyProg .N .U .sc) σ { σ with U := rep n } (6 * n + 3) :=
    ((runs_copy .N .U .sc (by decide) (by decide) (by decide) σ hsc).congr
      (by simp [Regs.set, Regs.get, hN, hU])).mono (by simp [Regs.get, hN, rep_len])
  have e2 : Runs (popProg .U) { σ with U := rep n } { σ with U := rep (n - 1) } 1 :=
    (runs_pop .U _).congr (by simp [Regs.set, Regs.get, rep, List.tail_replicate])
  have e3 : Runs (copyProg .N .G1 .sc) { σ with U := rep (n - 1) }
      { σ with U := rep (n - 1), G1 := rep n } (6 * n + 3) :=
    ((runs_copy .N .G1 .sc (by decide) (by decide) (by decide) { σ with U := rep (n - 1) } hsc).congr
      (by simp [Regs.set, Regs.get, hN, hG1])).mono (by simp [Regs.get, hN, rep_len])
  have e4 : Runs (repProg .U .G2 .G1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      { σ with U := rep (n - 1), G1 := rep n }
      { σ with U := rep (n - 1), G2 := rep (2 * c) } ((6 * (n - 1) + 7) * n + 1) :=
    ((runs_rep .U .G2 .G1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      { σ with U := rep (n - 1), G1 := rep n } hsc).congr
      (by simp [Regs.set, Regs.get, hG1, hG2, rep, flatten_rep']; rw [hc]; exact hev)).mono
      (by simp [Regs.get, rep_len])
  have e5 : Runs (halfProg .G2 .G1) { σ with U := rep (n - 1), G2 := rep (2 * c) }
      { σ with U := rep (n - 1), G1 := rep c } (7 * c + 1) :=
    (runs_half .G2 .G1 (by decide) c _ rfl).congr (by simp [Regs.set, Regs.get, hG1, hG2, rep])
  have e6 : Runs (copyN .G1 .Uy 7) { σ with U := rep (n - 1), G1 := rep c }
      { σ with U := rep (n - 1), G1 := rep c, Uy := rep (7 * c) } (7 * (6 * c + 4) + 1) :=
    (runs_copyN .G1 .Uy (by decide) (by decide) (by decide) c 7 0
      { σ with U := rep (n - 1), G1 := rep c } rfl
      (by simp [Regs.get, hUy, rep]) hsc).congr (by simp [Regs.set])
  have e7 : Runs (clearProg .G1) { σ with U := rep (n - 1), G1 := rep c, Uy := rep (7 * c) }
      { σ with U := rep (n - 1), Uy := rep (7 * c) } (3 * c + 1) :=
    ((runs_clear .G1 _).congr (by simp [Regs.set, hG1])).mono (by simp [Regs.get, rep_len])
  have e8 : Runs (clearProg .U) { σ with U := rep (n - 1), Uy := rep (7 * c) }
      { σ with Uy := rep (7 * c) } (3 * n + 1) :=
    ((runs_clear .U _).congr (by simp [Regs.set, hU])).mono (by simp [Regs.get, rep_len] <;> omega)
  have e9 : Runs (copyProg .N .G2 .sc) { σ with Uy := rep (7 * c) }
      { σ with Uy := rep (7 * c), G2 := rep n } (6 * n + 3) :=
    ((runs_copy .N .G2 .sc (by decide) (by decide) (by decide) { σ with Uy := rep (7 * c) } hsc).congr
      (by simp [Regs.set, Regs.get, hN, hG2])).mono (by simp [Regs.get, hN, rep_len])
  have e10 : Runs (repProg .Um .G1 .G2 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      { σ with Uy := rep (7 * c), G2 := rep n }
      { σ with Uy := rep (7 * c), G1 := rep (n * mN n) } ((6 * mN n + 7) * n + 1) :=
    ((runs_rep .Um .G1 .G2 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      { σ with Uy := rep (7 * c), G2 := rep n } hsc).congr
      (by simp [Regs.set, Regs.get, hG1, hG2, hUm, rep, flatten_rep'])).mono
      (by simp [Regs.get, rep_len, hUm])
  have e11 : Runs (copyN .G1 .Uy 5) { σ with Uy := rep (7 * c), G1 := rep (n * mN n) }
      { σ with Uy := rep (yBv n), G1 := rep (n * mN n) } (5 * (6 * (n * mN n) + 4) + 1) :=
    (runs_copyN .G1 .Uy (by decide) (by decide) (by decide) (n * mN n) 5 (7 * c)
      { σ with Uy := rep (7 * c), G1 := rep (n * mN n) } rfl rfl hsc).congr
      (by simp only [Regs.set, yBv]; congr 2; rw [← hc]; ring)
  have e12 : Runs (clearProg .G1) { σ with Uy := rep (yBv n), G1 := rep (n * mN n) }
      { σ with Uy := rep (yBv n) } (3 * (n * mN n) + 1) :=
    ((runs_clear .G1 _).congr (by simp [Regs.set, hG1])).mono (by simp [Regs.get, rep_len])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
    (e11.seq e12))))))))))).congr rfl).mono ?_
  have hm := mN_le n
  have hc2 : 2 * c ≤ n * n := by rw [← hev]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h1 : 1 ≤ (n + 1) := by omega
  have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right h1 (by omega)
  have h3 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have h4 : n * mN n ≤ 2 * (n + 1) ^ 3 := by
    have : n * mN n ≤ (n + 1) * (2 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) hm
    nlinarith
  have h5 : (6 * (n - 1) + 7) * n ≤ 7 * (n + 1) ^ 2 := by
    have : 6 * (n - 1) + 7 ≤ 7 * (n + 1) := by omega
    nlinarith
  have h6 : (6 * mN n + 7) * n ≤ 6 * (n * mN n) + 7 * (n + 1) := by nlinarith
  have h7 : n * n ≤ (n + 1) ^ 2 := by nlinarith
  omega

lemma length_encNats_le (l : List ℕ) (M : ℕ) (h : ∀ x ∈ l, x ≤ M) :
    (encNats l).length ≤ l.length * (M + 1) := by
  induction l with
  | nil => simp [encNats]
  | cons x l ih =>
    rw [encNats_cons', List.length_append, encNat_eq']
    have hx := h x List.mem_cons_self
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := len_bits_le x
    simp only [List.length_append, length_enc, List.length_cons, List.length_nil]
    nlinarith

/-! ## The whole generation phase -/

def genP (yP : Prog) : Prog :=
  .seq rotP (.seq mP (.seq (emitProg .Bn) (.seq (emitProg .Bm) (.seq (copyProg .N .JB .sc)
    (.seq jobsP (.seq yP (.seq (u2bProg .Uy .By) (.seq (emitProg .By) (mvProg .W .out)))))))))

noncomputable def outList (yv : ℕ → ℕ) (n : ℕ) (bs : List Bool) : List ℕ :=
  [n, mN n] ++ outRows n (adjB bs n) n ++ [yv n]

lemma outRows_le (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ : ℕ) : ∀ x ∈ outRows n a ℓ, x ≤ 9 := by
  intro x hx
  simp only [outRows, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, _, r, _, rfl⟩ := hx
  exact pv_le _ _ _

lemma outRows_len (n : ℕ) (a : ℕ → ℕ → Bool) (ℓ : ℕ) : (outRows n a ℓ).length = ℓ * mN n := by
  simp [outRows, List.length_flatMap, List.sum_replicate]

lemma runs_genP (yP : Prog) (yv : ℕ → ℕ) (hY : YSpec yP yv) (hyv : ∀ n, yv n ≤ 20 * (n + 1) ^ 3)
    (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    ∃ τ, Runs (genP yP) (st6 n bs) τ (10 ^ 6 * (n + 1) ^ 6) ∧ τ.out = encNats (outList yv n bs) := by
  set Ml := enc (bs.drop n ++ bs.take n) with hMl
  set a := adjB bs n with ha
  have hMlen : Ml.length = n * n := by
    simp only [hMl, enc, List.length_map, List.length_append, List.length_drop, List.length_take, hbs]
    have : n ≤ n * n := by nlinarith
    omega
  have e1 := runs_rotP n bs hbs
  have e2 := runs_mP { st6 n bs with M := Ml } n rfl rfl rfl rfl rfl rfl rfl
  set Γ := { { st6 n bs with M := Ml } with Um := rep (mN n), Bm := enc (Nat.bits (mN n)) } with hΓ
  have e3 := runs_emit .Bn (by decide) (by decide) (by decide) Γ rfl rfl
  have e4 := runs_emit .Bm (by decide) (by decide) (by decide)
    { Γ with W := BSym.sep :: (Γ.get .Bn).reverse ++ Γ.W } rfl rfl
  have e5 : Runs (copyProg .N .JB .sc)
      { { Γ with W := BSym.sep :: (Γ.get .Bn).reverse ++ Γ.W } with
        W := BSym.sep :: (Regs.get { Γ with W := BSym.sep :: (Γ.get .Bn).reverse ++ Γ.W } .Bm).reverse ++
          (BSym.sep :: (Γ.get .Bn).reverse ++ Γ.W) }
      (jobSt n a [n, mN n] Γ 0) (6 * n + 3) :=
    ((runs_copy .N .JB .sc (by decide) (by decide) (by decide) _ rfl).congr (by
      simp [Regs.set, Regs.get, jobSt, Wjob, outRows, encNats, encNat_eq', hΓ, st6, Regs.empty, rep])).mono
      (by simp [Regs.get, hΓ, st6])
  have e6 := runs_jobsP (n := n) (a := a) (pre := [n, mN n]) Γ Ml hMlen
    (fun q t hq ht => rot_stream n bs hbs q t hq ht) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl
  have e7 := hY (jobSt n a [n, mN n] Γ n) n rfl rfl rfl rfl rfl rfl rfl
  have e8 := runs_u2b .Uy .By (by decide) (by decide) (by decide) (yv n)
    { jobSt n a [n, mN n] Γ n with Uy := rep (yv n) } 0 rfl rfl rfl
  rw [Nat.zero_add] at e8
  have e9 := runs_emit .By (by decide) (by decide) (by decide)
    ((({ jobSt n a [n, mN n] Γ n with Uy := rep (yv n) }).set .Uy []).set .By (enc (Nat.bits (yv n))))
    rfl rfl
  have e10 := runs_mv .W .out (by decide)
    { ((({ jobSt n a [n, mN n] Γ n with Uy := rep (yv n) }).set .Uy []).set .By
      (enc (Nat.bits (yv n)))) with
      W := BSym.sep :: (Regs.get ((({ jobSt n a [n, mN n] Γ n with Uy := rep (yv n) }).set .Uy []).set
        .By (enc (Nat.bits (yv n)))) .By).reverse ++
        Regs.W ((({ jobSt n a [n, mN n] Γ n with Uy := rep (yv n) }).set .Uy []).set .By
          (enc (Nat.bits (yv n)))) }
  have hX : 1 ≤ n + 1 := by omega
  generalize hX6 : (n + 1) ^ 6 = P
  have hp1 : n + 1 ≤ P := by
    rw [← hX6]; calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right hX (by omega)
  have hp2 : (n + 1) ^ 2 ≤ P := by rw [← hX6]; exact Nat.pow_le_pow_right hX (by omega)
  have hp3 : (n + 1) ^ 3 ≤ P := by rw [← hX6]; exact Nat.pow_le_pow_right hX (by omega)
  have hp4 : (n + 1) ^ 4 ≤ P := by rw [← hX6]; exact Nat.pow_le_pow_right hX (by omega)
  have hp33 : (n + 1) ^ 3 * (n + 1) ^ 3 = P := by rw [← hX6]; ring
  have hy := hyv n
  have hm := mN_le n
  have hbn : (Nat.bits n).length ≤ n := len_bits_le n
  have hbm : (Nat.bits (mN n)).length ≤ mN n := len_bits_le _
  have hby : (Nat.bits (yv n)).length ≤ yv n := len_bits_le _
  have hnm : n * mN n ≤ 2 * (n + 1) ^ 3 := by
    have : n * mN n ≤ (n + 1) * (2 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) hm
    nlinarith
  have e1' := e1.mono (B' := 90 * P) (by nlinarith)
  have e2' := e2.mono (B' := 100 * P) (by omega)
  have e3' := e3.mono (B' := 16 * P) (by simp only [Regs.get, hΓ, st6, length_enc]; omega)
  have e4' := e4.mono (B' := 25 * P) (by simp only [Regs.get, hΓ, length_enc]; omega)
  have e5' := e5.mono (B' := 9 * P) (by omega)
  have e6' := e6.mono (B' := 407 * P) (by
    have : n * (400 * (n + 1) ^ 2 + 6) ≤ (n + 1) * (406 * (n + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
    have h3 : (n + 1) * (406 * (n + 1) ^ 2) = 406 * (n + 1) ^ 3 := by ring
    omega)
  have e7' := e7.mono (B' := 1000 * P) (by omega)
  have e8' := e8.mono (B' := 2800 * P) (by
    have hyy : yv n * (6 * yv n + 15) ≤ 20 * (n + 1) ^ 3 * (120 * (n + 1) ^ 3 + 15) :=
      Nat.mul_le_mul hy (by omega)
    have : 20 * (n + 1) ^ 3 * (120 * (n + 1) ^ 3 + 15) = 2400 * ((n + 1) ^ 3 * (n + 1) ^ 3) +
      300 * (n + 1) ^ 3 := by ring
    rw [hp33] at this
    omega)
  have e9' := e9.mono (B' := 190 * P) (by simp only [Regs.get, Regs.set, length_enc]; omega)
  have hL : ([n, mN n] ++ outRows n a n ++ []).length = n * mN n + 2 := by
    simp [outRows_len] <;> ring
  have hW : (encNats ([n, mN n] ++ outRows n a n ++ [])).length ≤
      (n * mN n + 2) * (2 * (n + 1) ^ 2 + 10) := by
    have := length_encNats_le ([n, mN n] ++ outRows n a n ++ []) (2 * (n + 1) ^ 2 + 9) (by
      intro x hx
      simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil] at hx
      rcases hx with (rfl | rfl | h) | h
      · nlinarith
      · exact hm.trans (by omega)
      · exact h.elim
      · exact le_trans (outRows_le n a n x h) (by omega))
    rw [hL] at this; exact this
  have hW' : (n * mN n + 2) * (2 * (n + 1) ^ 2 + 10) ≤ 48 * P := by
    have : (n * mN n + 2) * (2 * (n + 1) ^ 2 + 10) ≤ (4 * (n + 1) ^ 3) * (12 * (n + 1) ^ 3) := by
      apply Nat.mul_le_mul
      · have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega
      · have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        have : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right hX (by omega)
        omega
    have h2 : (4 * (n + 1) ^ 3) * (12 * (n + 1) ^ 3) = 48 * ((n + 1) ^ 3 * (n + 1) ^ 3) := by ring
    rw [h2, hp33] at this; exact this
  have e10' := e10.mono (B' := 300 * P) (by
    simp only [Regs.get, Regs.set, jobSt, Wjob, List.length_cons, List.length_append,
      List.length_reverse, length_enc, List.range_zero, List.map_nil]
    omega)
  refine ⟨_, ((e1'.seq (e2'.seq (e3'.seq (e4'.seq (e5'.seq (e6'.seq (e7'.seq (e8'.seq (e9'.seq
    e10'))))))))).mono ?_), ?_⟩
  · omega
  · -- the output
    simp only [Regs.get, Regs.set, jobSt, Wjob, hΓ, st6, Regs.empty, List.reverse_append,
      List.reverse_cons, List.reverse_reverse, List.append_nil, List.nil_append, outList,
      List.range_zero, List.map_nil]
    simp [encNats_app, encNats, encNat_eq', List.append_assoc, ha]

end NWRed



set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## The case of two vertices -/

def yesP : Prog := .seq (pushProg .out .sep) (.seq (pushProg .out .sep) (pushProg .out .sep))

def hp2P : Prog :=
  .seq (copyProg .M .Z .sc) (.seq (popProg .Z) (.seq
    (.branch (fun h => decide (h .Z = some .one)) yesP
      (.seq (popProg .Z) (.branch (fun h => decide (h .Z = some .one)) yesP skipP)))
    (.seq (clearProg .Z) (pushProg .bad .one))))

def tstP : Prog :=
  .branch (fun h => decide (h .X = some .zero))
    (.seq (popProg .X) (.branch (fun h => decide (h .X = some .one))
      (.seq (popProg .X) (.branch (fun h => (h .X).isNone) hp2P skipP)) skipP)) skipP

def c2P : Prog := .seq (copyProg .Bn .X .sc) (.seq tstP (clearProg .X))

def sp2 (bs : List Bool) : List BSym :=
  if bs.getD 1 false || bs.getD 2 false then [.sep, .sep, .sep] else []

lemma enc_bits_two (n : ℕ) : enc (Nat.bits n) = [.zero, .one] ↔ n = 2 := by
  constructor
  · intro h
    have h2 : Nat.bits n = [false, true] := by
      have hinj : Function.Injective toB := by intro x y hxy; cases x <;> cases y <;> simp_all [toB]
      apply List.map_injective_iff.2 hinj
      simpa [enc, toB] using h
    have := bval_bits n
    rw [h2] at this
    simpa [bval, Nat.bit] using this.symm
  · rintro rfl
    have : Nat.bits 2 = [false, true] := by decide
    simp [this, enc, toB]

def tstB2 : Prog := .branch (fun h => decide (h .X = some .one))
      (.seq (popProg .X) (.branch (fun h => (h .X).isNone) hp2P skipP)) skipP

lemma tstP_eq : tstP = .branch (fun h => decide (h .X = some .zero)) (.seq (popProg .X) tstB2) skipP := rfl

lemma runs_tst_other (σ : Regs) (hX : σ.X ≠ [.zero, .one]) :
    ∃ l, Runs tstP σ (σ.set .X l) 8 ∧ l.length ≤ σ.X.length := by
  rw [tstP_eq]
  rcases hx : σ.X with _ | ⟨x, l'⟩
  · refine ⟨[], ((runs_skip σ).brF (by simp [hd, Regs.get, hx])).congr ?_ |>.mono (by omega), le_rfl⟩
    rw [← hx]; exact (Regs.set_get σ .X).symm
  · by_cases hx0 : x = .zero
    · subst hx0
      have ep := runs_pop .X σ
      have hxt : (σ.get .X).tail = l' := by simp [Regs.get, hx]
      rw [hxt] at ep
      rcases hl : l' with _ | ⟨y, l''⟩
      · subst hl
        have eB : Runs tstB2 (σ.set .X []) (σ.set .X []) 2 :=
          (runs_skip _).brF (by simp [hd, Regs.get_set])
        exact ⟨[], ((ep.seq eB).brT (by simp [hd, Regs.get, hx])).mono (by omega), by simp⟩
      · subst hl
        by_cases hy : y = .one
        · subst hy
          have ep2 := runs_pop .X (σ.set .X (.one :: l''))
          rw [Regs.get_set_self, List.tail_cons, Regs.set_set] at ep2
          rcases hl2 : l'' with _ | ⟨z, l3⟩
          · subst hl2; exact absurd hx hX
          · subst hl2
            have eC : Runs (.branch (fun h : Key → Option BSym => (h .X).isNone) hp2P skipP)
                (σ.set .X (z :: l3)) (σ.set .X (z :: l3)) 2 :=
              (runs_skip _).brF (by simp [hd, Regs.get_set])
            have eB : Runs tstB2 (σ.set .X (.one :: z :: l3)) (σ.set .X (z :: l3)) 5 :=
              ((ep2.seq eC).brT (by simp [hd, Regs.get_set])).mono (by omega)
            exact ⟨z :: l3, ((ep.seq eB).brT (by simp [hd, Regs.get, hx])).mono (by omega),
              by simp⟩
        · have eB : Runs tstB2 (σ.set .X (y :: l'')) (σ.set .X (y :: l'')) 2 :=
            (runs_skip _).brF (by simp [hd, Regs.get_set, hy])
          exact ⟨y :: l'', ((ep.seq eB).brT (by simp [hd, Regs.get, hx])).mono (by omega),
            by simp⟩
    · refine ⟨x :: l', ((runs_skip σ).brF (by simp [hd, Regs.get, hx, hx0])).congr ?_ |>.mono
        (by omega), le_rfl⟩
      rw [← hx]; exact (Regs.set_get σ .X).symm

lemma runs_yes (σ : Regs) : Runs yesP σ (σ.set .out (.sep :: .sep :: .sep :: σ.out)) 5 :=
  ((runs_push .out .sep σ).seq ((runs_push .out .sep _).seq (runs_push .out .sep _))).congr
    (by simp [Regs.set, Regs.get])

lemma runs_hp2 (σ : Regs) (b0 b1 b2 b3 : Bool) (hM : σ.M = enc [b0, b1, b2, b3]) (hZ : σ.Z = [])
    (hsc : σ.sc = []) :
    ∃ τ, Runs hp2P σ τ 60 ∧ τ.bad ≠ [] ∧
      τ.out = (if b1 || b2 then [.sep, .sep, .sep] else []) ++ σ.out ∧ τ.X = σ.X := by
  have e1 := runs_copy .M .Z .sc (by decide) (by decide) (by decide) σ hsc
  rw [show σ.get .M = enc [b0, b1, b2, b3] from hM, show σ.get .Z = [] from hZ, List.append_nil] at e1
  have e2 := runs_pop .Z (σ.set .Z (enc [b0, b1, b2, b3]))
  rw [Regs.get_set_self, Regs.set_set] at e2
  simp only [enc_cons, enc_nil, List.tail_cons] at e2
  set σ2 := σ.set .Z [toB b1, toB b2, toB b3] with hσ2
  obtain ⟨τ1, eB, hτ1⟩ : ∃ τ1, Runs (.branch (fun h => decide (h .Z = some .one)) yesP
      (.seq (popProg .Z) (.branch (fun h => decide (h .Z = some .one)) yesP skipP))) σ2 τ1 10 ∧
      τ1.out = (if b1 || b2 then [.sep, .sep, .sep] else []) ++ σ.out ∧ τ1.bad = σ.bad ∧
      (τ1.get .Z).length ≤ 3 ∧ τ1.X = σ.X := by
    cases b1
    · have ep := runs_pop .Z σ2
      rw [hσ2, Regs.get_set_self, Regs.set_set] at ep
      simp only [List.tail_cons] at ep
      cases b2
      · refine ⟨_, ((ep.seq ((runs_skip _).brF (by simp [hd, Regs.get_set, toB]))).brF
          (by simp [hd, Regs.get_set, toB])).mono (by omega), ?_, ?_, ?_, ?_⟩ <;> simp [Regs.set, Regs.get]
      · refine ⟨_, ((ep.seq ((runs_yes _).brT (by simp [hd, Regs.get_set, toB]))).brF
          (by simp [hd, Regs.get_set, toB])).mono (by omega), ?_, ?_, ?_, ?_⟩ <;> simp [Regs.set, Regs.get]
    · refine ⟨_, ((runs_yes σ2).brT (by simp [hd, hσ2, Regs.get_set, toB])).mono (by omega), ?_, ?_, ?_, ?_⟩ <;>
        simp [hσ2, Regs.set, Regs.get]
  have e4 := runs_clear .Z τ1
  have e5 := runs_push .bad .one (τ1.set .Z [])
  refine ⟨_, (e1.seq (e2.seq (eB.seq (e4.seq e5)))).mono ?_, by simp [Regs.set], ?_, ?_⟩
  · have := hτ1.2.2.1
    simp only [length_enc, List.length_cons, List.length_nil]; omega
  · simp [Regs.set, Regs.get, hτ1.1]
  · simp [Regs.set, Regs.get, hτ1.2.2.2]

lemma runs_c2_other (n : ℕ) (bs : List Bool) (hn : n ≠ 2) :
    Runs c2P (st6 n bs) (st6 n bs) (20 * n + 20) := by
  have e1 := runs_copy .Bn .X .sc (by decide) (by decide) (by decide) (st6 n bs) rfl
  have hX1 : ((st6 n bs).set .X ((st6 n bs).get .Bn ++ (st6 n bs).get .X)).X = enc (Nat.bits n) := by
    simp [Regs.set, Regs.get, st6, Regs.empty]
  obtain ⟨l, e2, hl⟩ := runs_tst_other ((st6 n bs).set .X ((st6 n bs).get .Bn ++ (st6 n bs).get .X))
    (by rw [hX1]; intro h; exact hn ((enc_bits_two n).1 h))
  have e3 := runs_clear .X (((st6 n bs).set .X ((st6 n bs).get .Bn ++ (st6 n bs).get .X)).set .X l)
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · simp [Regs.set, st6, Regs.empty]
  · rw [hX1] at hl
    simp only [Regs.get, Regs.set, st6, length_enc] at hl ⊢
    have := len_bits_le n
    simp at hl ⊢
    omega

lemma runs_c2_two (bs : List Bool) (hbs : bs.length = 4) :
    ∃ τ, Runs c2P (st6 2 bs) τ 100 ∧ τ.bad ≠ [] ∧ τ.out = sp2 bs := by
  match bs, hbs with
  | [b0, b1, b2, b3], _ =>
    have hb2 : Nat.bits 2 = [false, true] := by decide
    have e1 := runs_copy .Bn .X .sc (by decide) (by decide) (by decide) (st6 2 [b0, b1, b2, b3]) rfl
    set σ1 := (st6 2 [b0, b1, b2, b3]).set .X
      ((st6 2 [b0, b1, b2, b3]).get .Bn ++ (st6 2 [b0, b1, b2, b3]).get .X) with hσ1
    have hX1 : σ1.get .X = [.zero, .one] := by simp [hσ1, Regs.set, Regs.get, st6, Regs.empty, hb2, enc]
    have ep1 := runs_pop .X σ1
    rw [hX1, List.tail_cons] at ep1
    have ep2 := runs_pop .X (σ1.set .X [.one])
    rw [Regs.get_set_self, List.tail_cons, Regs.set_set] at ep2
    obtain ⟨τ1, eh, hb, ho, hxx⟩ := runs_hp2 (σ1.set .X []) b0 b1 b2 b3
      (by simp [hσ1, Regs.set, Regs.get, st6]) (by simp [hσ1, Regs.set, Regs.get, st6, Regs.empty])
      (by simp [hσ1, Regs.set, Regs.get, st6, Regs.empty])
    have eC : Runs (.branch (fun h : Key → Option BSym => (h .X).isNone) hp2P skipP) (σ1.set .X [])
        τ1 61 := eh.brT (by simp [hd, Regs.get_set])
    have eB : Runs tstB2 (σ1.set .X [.one]) τ1 64 :=
      ((ep2.seq eC).brT (by simp [hd, Regs.get_set])).mono (by omega)
    have eT : Runs tstP σ1 τ1 67 := by
      rw [tstP_eq]; exact ((ep1.seq eB).brT (by simp [hd, hX1])).mono (by omega)
    have e3 := runs_clear .X τ1
    refine ⟨_, (e1.seq (eT.seq e3)).mono ?_, by simpa [Regs.set] using hb, ?_⟩
    · have : τ1.get .X = [] := by
        show τ1.X = []; rw [hxx]; simp [Regs.set]
      rw [this]; simp [Regs.get, st6, hb2, enc]
    · simp [Regs.set, ho, hσ1, st6, Regs.empty, sp2]

/-! ## The whole machine -/

def mainP (yP : Prog) : Prog := .seq parseProg (gate (.seq c2P (gate (genP yP))))

noncomputable def gF (yv : ℕ → ℕ) (n : ℕ) (bs : List Bool) : List BSym :=
  if n = 2 then sp2 bs else encNats (outList yv n bs)

noncomputable def fF (yv : ℕ → ℕ) : List BSym → List BSym := decodeThen (gF yv)

lemma st6_bad (n : ℕ) (bs : List Bool) : (st6 n bs).bad = [] := rfl

theorem mainSpec (yP : Prog) (yv : ℕ → ℕ) (hY : YSpec yP yv) (hyv : ∀ n, yv n ≤ 20 * (n + 1) ^ 3)
    (w : List BSym) :
    ∃ τ, Runs (mainP yP) (initR w) τ (2 * 10 ^ 6 * (w.length + 1) ^ 6) ∧ τ.out = fF yv w := by
  obtain ⟨τ, e, h⟩ := parse_spec w
  have hX : 1 ≤ w.length + 1 := by omega
  have h26 : (w.length + 1) ^ 2 ≤ (w.length + 1) ^ 6 := Nat.pow_le_pow_right hX (by omega)
  have h16 : w.length + 1 ≤ (w.length + 1) ^ 6 := by
    calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (w.length + 1) ^ 6 := Nat.pow_le_pow_right hX (by omega)
  rcases h with ⟨n, bs, hbs, hw, hτ⟩ | ⟨hb, ho, hinv⟩
  · subst hτ
    have hbL : bs.length ≤ w.length := hw ▸ length_code n bs
    have hnL : n ≤ w.length := le_trans (n_le_of_sq hbs) hbL
    have hfw : fF yv w = gF yv n bs := by rw [fF, hw, decodeThen_code _ n bs hbs]
    by_cases h2 : n = 2
    · subst h2
      obtain ⟨τ2, e2, hb2, ho2⟩ := runs_c2_two bs (by simpa using hbs)
      refine ⟨τ2, (e.seq (runs_gate_ok (st6_bad 2 bs) (e2.seq (runs_gate_skip hb2)))).mono ?_, ?_⟩
      · nlinarith
      · rw [ho2, hfw, gF, if_pos rfl]
    · have e2 := runs_c2_other n bs h2
      obtain ⟨τ3, e3, ho3⟩ := runs_genP yP yv hY hyv n bs hbs
      refine ⟨τ3, (e.seq (runs_gate_ok (st6_bad n bs) (e2.seq (runs_gate_ok (st6_bad n bs) e3)))).mono ?_, ?_⟩
      · have : (n + 1) ^ 6 ≤ (w.length + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
        nlinarith
      · rw [ho3, hfw, gF, if_neg h2]
  · refine ⟨τ, (e.seq (runs_gate_skip hb)).mono ?_, ?_⟩
    · nlinarith
    · rw [ho, fF, decodeThen_invalid _ w hinv]

lemma initR_get (w : List BSym) : (initR w).get = fun j => if j = .inp then w else [] := by
  funext j; cases j <;> rfl

theorem fF_poly (yP : Prog) (yv : ℕ → ℕ) (hY : YSpec yP yv) (hyv : ∀ n, yv n ≤ 20 * (n + 1) ^ 3) :
    PolyTimeComputable (fF yv) := by
  obtain ⟨k, hk⟩ := polynomial_absorb (2 * 10 ^ 6) 6 0
  refine stack_program_polytime (mainP yP) .inp .out (fF yv) k (fun w => ?_)
  obtain ⟨τ, ⟨m, hm, ex⟩, ho⟩ := mainSpec yP yv hY hyv w
  refine ⟨τ.get, m, le_trans hm (by have := hk w.length; omega), ?_, ho⟩
  rw [← initR_get]; exact ex

lemma yAv_le (n : ℕ) : yAv n ≤ 20 * (n + 1) ^ 3 := by
  unfold yAv SchedComplexity.NoWait.numMachines
  have : n * (n - 1) ≤ (n + 1) ^ 2 := by
    have : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith
  have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  omega

lemma yBv_le (n : ℕ) : yBv n ≤ 20 * (n + 1) ^ 3 := by
  unfold yBv
  have h1 : n * (n - 1) / 2 ≤ n * n := le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hm := mN_le n
  have h4 : n * mN n ≤ 2 * (n + 1) ^ 3 := by
    have : n * mN n ≤ (n + 1) * (2 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) hm
    nlinarith
  have h5 : n * n ≤ (n + 1) ^ 3 := by nlinarith
  omega

end NWRed



set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity
open SchedComplexity.NoWait

/-! ## Instance codes -/

lemma flatten_inj_len (m : ℕ) : ∀ (L L' : List (List ℕ)), L.length = L'.length →
    (∀ x ∈ L, x.length = m) → (∀ x ∈ L', x.length = m) → L.flatten = L'.flatten → L = L' := by
  intro L
  induction L with
  | nil => intro L' h _ _ _; cases L' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a L ih =>
    intro L' h h1 h2 hf
    cases L' with
    | nil => simp at h
    | cons b L' =>
      simp only [List.flatten_cons] at hf
      have ha := h1 a List.mem_cons_self
      have hb := h2 b List.mem_cons_self
      obtain ⟨e1, e2⟩ := List.append_inj hf (by rw [ha, hb])
      rw [e1, ih L' (by simpa using h) (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) e2]

lemma nwCode_eq {n m : ℕ} (p : Fin n → Fin m → ℕ) (y : ℕ) :
    nwCode p y = encNats ([n, m] ++ (List.ofFn fun ℓ : Fin n => List.ofFn fun r : Fin m => p ℓ r).flatten ++ [y]) :=
  rfl

lemma nwCode_ne_nil {n m : ℕ} (p : Fin n → Fin m → ℕ) (y : ℕ) : nwCode p y ≠ [] := by
  rw [nwCode_eq]; simp [encNats, encNat]

lemma nwCode_inj {n m n' m' : ℕ} (p : Fin n → Fin m → ℕ) (p' : Fin n' → Fin m' → ℕ) (y y' : ℕ)
    (h : nwCode p y = nwCode p' y') :
    ∃ (hn : n = n') (hm : m = m'), y = y' ∧ p' = (fun ℓ r => p (hn ▸ ℓ) (hm ▸ r)) := by
  rw [nwCode_eq, nwCode_eq] at h
  have h' := encNats_inj _ _ h
  simp only [List.cons_append, List.cons.injEq] at h'
  obtain ⟨hn, hm, hrest⟩ := h'
  subst hn; subst hm
  have hl : (List.ofFn fun ℓ : Fin n => List.ofFn fun r : Fin m => p ℓ r).flatten.length =
      (List.ofFn fun ℓ : Fin n => List.ofFn fun r : Fin m => p' ℓ r).flatten.length := by
    simp only [List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn]
  obtain ⟨hF, hy⟩ := List.append_inj hrest hl
  simp only [List.cons.injEq, and_true] at hy
  refine ⟨rfl, rfl, hy, ?_⟩
  have := flatten_inj_len m _ _ (by simp) (by simp) (by simp) hF
  rw [List.ofFn_inj] at this
  funext ℓ r
  have h2 := congrFun this ℓ
  rw [List.ofFn_inj] at h2
  exact (congrFun h2 r).symm

lemma mem_cmax_iff {n m : ℕ} (p : Fin n → Fin m → ℕ) (y : ℕ) :
    nwCode p y ∈ cmaxLang ↔ ∃ B, IsNoWaitSchedule p B ∧ ∀ ℓ, completion p B ℓ ≤ y := by
  constructor
  · rintro ⟨n', m', p', y', hc, he⟩
    obtain ⟨hn, hm, hy, hp⟩ := nwCode_inj p p' y y' he
    subst hn; subst hm; subst hy; subst hp
    exact hc
  · intro hc; exact ⟨n, m, p, y, hc, rfl⟩

lemma mem_sumC_iff {n m : ℕ} (p : Fin n → Fin m → ℕ) (y : ℕ) :
    nwCode p y ∈ sumCLang ↔ ∃ B, IsNoWaitSchedule p B ∧ ∑ ℓ, completion p B ℓ ≤ y := by
  constructor
  · rintro ⟨n', m', p', y', hc, he⟩
    obtain ⟨hn, hm, hy, hp⟩ := nwCode_inj p p' y y' he
    subst hn; subst hm; subst hy; subst hp
    exact hc
  · intro hc; exact ⟨n, m, p, y, hc, rfl⟩

lemma nil_not_cmax : ([] : List BSym) ∉ cmaxLang := by
  rintro ⟨n, m, p, y, _, he⟩; exact nwCode_ne_nil p y he.symm

lemma nil_not_sumC : ([] : List BSym) ∉ sumCLang := by
  rintro ⟨n, m, p, y, _, he⟩; exact nwCode_ne_nil p y he.symm

lemma sss_eq : ([.sep, .sep, .sep] : List BSym) = nwCode (fun (_ : Fin 0) (_ : Fin 0) => 0) 0 := by
  rw [nwCode_eq]; simp [encNats, encNat]

lemma sss_cmax : ([.sep, .sep, .sep] : List BSym) ∈ cmaxLang := by
  rw [sss_eq, mem_cmax_iff]
  exact ⟨fun _ => 0, fun j => j.elim0, fun ℓ => ℓ.elim0⟩

lemma sss_sumC : ([.sep, .sep, .sep] : List BSym) ∈ sumCLang := by
  rw [sss_eq, mem_sumC_iff]
  exact ⟨fun _ => 0, fun j => j.elim0, by simp⟩

/-! ## The generated code is the code of the constructed instance -/

lemma outList_eq (yv : ℕ → ℕ) (n : ℕ) (bs : List Bool) (hn : n ≠ 2) :
    encNats (outList yv n bs) =
      nwCode (procTimes (adjOf n bs) (fun j k : Fin n => iotaN n j.val k.val) 1 5) (yv n) := by
  rw [nwCode_eq, outList]
  congr 3
  unfold outRows
  have h1 : (fun ℓ : Fin n => List.ofFn fun r : Fin (numMachines n) =>
      procTimes (adjOf n bs) (fun j k : Fin n => iotaN n j.val k.val) 1 5 ℓ r) =
      (fun ℓ : Fin n => (List.range (mN n)).map (Pt n (adjB bs n) ℓ.val)) := by
    funext ℓ
    rw [← ofFn_val]
    congr 1
    funext r
    exact procTimes_eq hn _ _ (fun u v => rfl) ℓ r
  rw [h1, ofFn_val n (fun ℓ => (List.range (mN n)).map (Pt n (adjB bs n) ℓ))]
  simp [List.flatMap]

end NWRed



set_option autoImplicit false

namespace NWRed

open CookPvsNP ProjSchedTW.Complexity
open SchedComplexity.NoWait

lemma hp2_iff (bs : List Bool) :
    HasHamiltonPath (adjOf 2 bs) ↔ (bs.getD 1 false || bs.getD 2 false) = true := by
  have a01 : adjOf 2 bs 0 1 = bs.getD 1 false := rfl
  have a10 : adjOf 2 bs 1 0 = bs.getD 2 false := rfl
  have a00 : adjOf 2 bs 0 0 = bs.getD 0 false := rfl
  have a11 : adjOf 2 bs 1 1 = bs.getD 3 false := rfl
  constructor
  · rintro ⟨σ, h⟩
    have h0 : adjOf 2 bs (σ 0) (σ 1) = true := h 0 (by norm_num)
    have hne : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
    revert h0 hne
    generalize σ 0 = u
    generalize σ 1 = v
    intro h0 hne
    fin_cases u <;> fin_cases v
    · exact absurd rfl hne
    · have : adjOf 2 bs 0 1 = true := h0
      rw [a01] at this; rw [this]; rfl
    · have : adjOf 2 bs 1 0 = true := h0
      rw [a10] at this; rw [this]; simp
    · exact absurd rfl hne
  · intro h
    rcases Bool.or_eq_true_iff.1 h with h1 | h1
    · refine ⟨Equiv.refl _, fun i hi => ?_⟩
      have : i = 0 := by ext; simp; omega
      subst this
      show adjOf 2 bs 0 1 = true
      rw [a01]; exact h1
    · refine ⟨Equiv.swap 0 1, fun i hi => ?_⟩
      have : i = 0 := by ext; simp; omega
      subst this
      show adjOf 2 bs ((Equiv.swap (0 : Fin 2) 1) 0) ((Equiv.swap (0 : Fin 2) 1) 1) = true
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right, a10]; exact h1

lemma sp2_mem_cmax (bs : List Bool) : sp2 bs ∈ cmaxLang ↔ (bs.getD 1 false || bs.getD 2 false) = true := by
  unfold sp2; split_ifs with h
  · exact ⟨fun _ => h, fun _ => sss_cmax⟩
  · exact ⟨fun hh => absurd hh nil_not_cmax, fun hh => absurd hh h⟩

lemma sp2_mem_sumC (bs : List Bool) : sp2 bs ∈ sumCLang ↔ (bs.getD 1 false || bs.getD 2 false) = true := by
  unfold sp2; split_ifs with h
  · exact ⟨fun _ => h, fun _ => sss_sumC⟩
  · exact ⟨fun hh => absurd hh nil_not_sumC, fun hh => absurd hh h⟩

lemma dhpCode_code {n : ℕ} (bs : List Bool) (hbs : bs.length = n * n) :
    dhpCode (adjOf n bs) = code n bs := by
  rw [dhpCode_eq, matBits_adjOf n bs hbs]

/-- the generic reduction: `P` describes the yes-instances among the constructed ones -/
theorem generic_red (L : CookPvsNP.Lang BSym) (yv : ℕ → ℕ) (f : List BSym → List BSym)
    (hf : f = fF yv)
    (hnil : ([] : List BSym) ∉ L) (hsss : ([.sep, .sep, .sep] : List BSym) ∈ L)
    (Cond : ∀ (n : ℕ), (Fin n → Fin n → Bool) → (Fin n → Fin n → ℕ) → Prop)
    (hcond : ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ), n ≠ 2 → Admissible n ι →
      (HasHamiltonPath adj ↔ Cond n adj ι))
    (hmem : ∀ (n : ℕ) (bs : List Bool), n ≠ 2 → bs.length = n * n →
      (encNats (outList yv n bs) ∈ L ↔ Cond n (adjOf n bs) (fun j k : Fin n => iotaN n j.val k.val)))
    (w : List BSym) :
    ((∃ (n : ℕ) (adj : Fin n → Fin n → Bool), n ≠ 2 ∧
        (∀ ι : Fin n → Fin n → ℕ, Admissible n ι → Cond n adj ι) ∧ w = dhpCode adj) ∨
      (∃ adj : Fin 2 → Fin 2 → Bool, HasHamiltonPath adj ∧ w = dhpCode adj)) ↔ f w ∈ L := by
  subst hf
  by_cases hv : ∃ n bs, bs.length = n * n ∧ w = code n bs
  · obtain ⟨n, bs, hbs, rfl⟩ := hv
    rw [fF, decodeThen_code _ n bs hbs, gF]
    have uniq : ∀ (n' : ℕ) (adj' : Fin n' → Fin n' → Bool), code n bs = dhpCode adj' →
        ∃ h : n = n', adj' = h ▸ adjOf n bs := by
      intro n' adj' h
      obtain ⟨h1, h2⟩ := code_inj (h.trans (dhpCode_eq adj'))
      subst h1
      exact ⟨rfl, by rw [h2, adjOf_matBits]⟩
    by_cases h2 : n = 2
    · subst h2
      rw [if_pos rfl]
      have hsp : sp2 bs ∈ L ↔ (bs.getD 1 false || bs.getD 2 false) = true := by
        unfold sp2; split_ifs with h
        · exact ⟨fun _ => h, fun _ => hsss⟩
        · exact ⟨fun hh => absurd hh hnil, fun hh => absurd hh h⟩
      rw [hsp, ← hp2_iff]
      constructor
      · rintro (⟨n', adj', hn', _, hw⟩ | ⟨adj', hhp, hw⟩)
        · obtain ⟨h, _⟩ := uniq n' adj' hw; exact absurd h.symm hn'
        · obtain ⟨h, ha⟩ := uniq 2 adj' hw
          rw [ha] at hhp; exact hhp
      · intro hhp; exact Or.inr ⟨adjOf 2 bs, hhp, (dhpCode_code bs hbs).symm⟩
    · rw [if_neg h2, hmem n bs h2 hbs]
      have hadm := iotaN_adm n h2
      constructor
      · rintro (⟨n', adj', hn', hall, hw⟩ | ⟨adj', _, hw⟩)
        · obtain ⟨h, ha⟩ := uniq n' adj' hw
          subst h
          rw [ha] at hall
          exact hall _ hadm
        · obtain ⟨h, _⟩ := uniq 2 adj' hw; exact absurd h h2
      · intro hc
        left
        refine ⟨n, adjOf n bs, h2, fun ι hι => ?_, (dhpCode_code bs hbs).symm⟩
        exact (hcond n _ ι h2 hι).1 ((hcond n _ _ h2 hadm).2 hc)
  · have hinv : ∀ n bs, bs.length = n * n → w ≠ code n bs := fun n bs h1 h2 => hv ⟨n, bs, h1, h2⟩
    rw [fF, decodeThen_invalid _ w hinv]
    refine ⟨?_, fun h => absurd h hnil⟩
    rintro (⟨n, adj, _, _, rfl⟩ | ⟨adj, _, rfl⟩)
    · exact absurd (dhpCode_eq adj) (hinv n _ (length_matBits adj))
    · exact absurd (dhpCode_eq adj) (hinv 2 _ (length_matBits adj))

lemma yBv_cast (n : ℕ) : ((yBv n : ℕ) : ℚ) =
    (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((5 : ℚ) + 2 * 1) + (n : ℚ) * (numMachines n : ℚ) * 5 := by
  have hev := even_mul_pred n
  have hc : ((n * (n - 1) / 2 : ℕ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
    have h1 : ((n * (n - 1) : ℕ) : ℚ) = 2 * ((n * (n - 1) / 2 : ℕ) : ℚ) := by
      conv_lhs => rw [hev]
      push_cast; ring
    have h2 : ((n * (n - 1) : ℕ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
    linarith
  unfold yBv
  have hm : (mN n : ℚ) = (numMachines n : ℚ) := rfl
  push_cast
  rw [hc, hm]
  ring

theorem partA : ∃ fA : List BSym → List BSym, CookPvsNP.PolyTimeComputable fA ∧
      ∀ w : List BSym,
        ((∃ (n : ℕ) (adj : Fin n → Fin n → Bool), n ≠ 2 ∧
            (∀ ι : Fin n → Fin n → ℕ, Admissible n ι →
              ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
                ∀ ℓ, completion (procTimes adj ι 1 5) B ℓ ≤
                  (n - 1) * (5 + 2 * 1) + numMachines n * 5) ∧
            w = dhpCode adj) ∨
          (∃ adj : Fin 2 → Fin 2 → Bool, HasHamiltonPath adj ∧ w = dhpCode adj)) ↔
          fA w ∈ cmaxLang :=
  ⟨fF yAv, fF_poly yAP yAv yAP_spec yAv_le, fun w =>
    generic_red cmaxLang yAv _ rfl nil_not_cmax sss_cmax
      (fun n adj ι => ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
        ∀ ℓ, completion (procTimes adj ι 1 5) B ℓ ≤ (n - 1) * (5 + 2 * 1) + numMachines n * 5)
      (fun n adj ι _ hι => theorem_5a_equiv adj ι hι 1 5 (by norm_num) (by norm_num))
      (fun n bs hn _ => by rw [outList_eq yAv n bs hn, mem_cmax_iff]; rfl) w⟩

theorem partB : ∃ fB : List BSym → List BSym, CookPvsNP.PolyTimeComputable fB ∧
      ∀ w : List BSym,
        ((∃ (n : ℕ) (adj : Fin n → Fin n → Bool), n ≠ 2 ∧
            (∀ ι : Fin n → Fin n → ℕ, Admissible n ι →
              ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
                ((∑ ℓ, completion (procTimes adj ι 1 5) B ℓ : ℕ) : ℚ) ≤
                  (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((5 : ℚ) + 2 * 1) +
                    (n : ℚ) * (numMachines n : ℚ) * 5) ∧
            w = dhpCode adj) ∨
          (∃ adj : Fin 2 → Fin 2 → Bool, HasHamiltonPath adj ∧ w = dhpCode adj)) ↔
          fB w ∈ sumCLang :=
  ⟨fF yBv, fF_poly yBP yBv yBP_spec yBv_le, fun w =>
    generic_red sumCLang yBv _ rfl nil_not_sumC sss_sumC
      (fun n adj ι => ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
        ((∑ ℓ, completion (procTimes adj ι 1 5) B ℓ : ℕ) : ℚ) ≤
          (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((5 : ℚ) + 2 * 1) + (n : ℚ) * (numMachines n : ℚ) * 5)
      (fun n adj ι _ hι => by
        have := theorem_5b_equiv adj ι hι 1 5 (by norm_num) (by norm_num)
        simp only [Nat.cast_ofNat, Nat.cast_one] at this
        exact this)
      (fun n bs hn _ => by
        rw [outList_eq yBv n bs hn, mem_sumC_iff]
        refine exists_congr fun B => and_congr_right fun _ => ?_
        rw [← yBv_cast, Nat.cast_le]) w⟩

end NWRed

open SchedComplexity.NoWait in
open ProjSchedTW.Complexity (BSym encNats) in
theorem solution :
    (∃ fA : List BSym → List BSym, CookPvsNP.PolyTimeComputable fA ∧
      ∀ w : List BSym,
        ((∃ (n : ℕ) (adj : Fin n → Fin n → Bool), n ≠ 2 ∧
            (∀ ι : Fin n → Fin n → ℕ, Admissible n ι →
              ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
                ∀ ℓ, completion (procTimes adj ι 1 5) B ℓ ≤
                  (n - 1) * (5 + 2 * 1) + numMachines n * 5) ∧
            w = dhpCode adj) ∨
          (∃ adj : Fin 2 → Fin 2 → Bool, HasHamiltonPath adj ∧ w = dhpCode adj)) ↔
          fA w ∈ cmaxLang) ∧
    (∃ fB : List BSym → List BSym, CookPvsNP.PolyTimeComputable fB ∧
      ∀ w : List BSym,
        ((∃ (n : ℕ) (adj : Fin n → Fin n → Bool), n ≠ 2 ∧
            (∀ ι : Fin n → Fin n → ℕ, Admissible n ι →
              ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
                ((∑ ℓ, completion (procTimes adj ι 1 5) B ℓ : ℕ) : ℚ) ≤
                  (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((5 : ℚ) + 2 * 1) +
                    (n : ℚ) * (numMachines n : ℚ) * 5) ∧
            w = dhpCode adj) ∨
          (∃ adj : Fin 2 → Fin 2 → Bool, HasHamiltonPath adj ∧ w = dhpCode adj)) ↔
          fB w ∈ sumCLang) :=
  ⟨NWRed.partA, NWRed.partB⟩

