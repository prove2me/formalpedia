-- Prove2me | solution 1 for RuralPostman.NPC.uhc_polyReducible_urp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T07:10:20.311536+00:00
-- url     : https://prove2.me/submissions/63bbfb7b-3168-4c4b-a3c7-7f5d66ddd808

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
import Definitions.Def_RuralPostman_NPC_Reductions
import Theorems.Thm_RuralPostman_NPC_claim_directed
import Theorems.Thm_RuralPostman_NPC_claim_undirected

set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## Registers of the stack machine -/

inductive Key
  | inp | out | bad | A | Pd | Bn | Bt | F | N | M | R | C | X | Y | Z | T | T2 | W
  | Cs | Cns | Ct | E | B2 | Us | D | P | Q | sc
  deriving DecidableEq

instance : Fintype Key :=
  ⟨⟨([.inp, .out, .bad, .A, .Pd, .Bn, .Bt, .F, .N, .M, .R, .C, .X, .Y, .Z, .T, .T2, .W,
    .Cs, .Cns, .Ct, .E, .B2, .Us, .D, .P, .Q, .sc] : List Key), by decide⟩, by intro x; cases x <;> decide⟩

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
  C : List BSym
  X : List BSym
  Y : List BSym
  Z : List BSym
  T : List BSym
  T2 : List BSym
  W : List BSym
  Cs : List BSym
  Cns : List BSym
  Ct : List BSym
  E : List BSym
  B2 : List BSym
  Us : List BSym
  D : List BSym
  P : List BSym
  Q : List BSym
  sc : List BSym

namespace Regs

def get (σ : Regs) : Key → List BSym
  | .inp => σ.inp | .out => σ.out | .bad => σ.bad | .A => σ.A | .Pd => σ.Pd | .Bn => σ.Bn
  | .Bt => σ.Bt | .F => σ.F | .N => σ.N | .M => σ.M | .R => σ.R | .C => σ.C | .X => σ.X
  | .Y => σ.Y | .Z => σ.Z | .T => σ.T | .T2 => σ.T2 | .W => σ.W | .Cs => σ.Cs
  | .Cns => σ.Cns | .Ct => σ.Ct | .E => σ.E | .B2 => σ.B2 | .Us => σ.Us | .D => σ.D
  | .P => σ.P | .Q => σ.Q | .sc => σ.sc

def set (σ : Regs) : Key → List BSym → Regs
  | .inp, l => { σ with inp := l } | .out, l => { σ with out := l }
  | .bad, l => { σ with bad := l } | .A, l => { σ with A := l }
  | .Pd, l => { σ with Pd := l } | .Bn, l => { σ with Bn := l }
  | .Bt, l => { σ with Bt := l } | .F, l => { σ with F := l }
  | .N, l => { σ with N := l } | .M, l => { σ with M := l }
  | .R, l => { σ with R := l } | .C, l => { σ with C := l }
  | .X, l => { σ with X := l } | .Y, l => { σ with Y := l }
  | .Z, l => { σ with Z := l } | .T, l => { σ with T := l }
  | .T2, l => { σ with T2 := l } | .W, l => { σ with W := l }
  | .Cs, l => { σ with Cs := l } | .Cns, l => { σ with Cns := l }
  | .Ct, l => { σ with Ct := l } | .E, l => { σ with E := l }
  | .B2, l => { σ with B2 := l } | .Us, l => { σ with Us := l }
  | .D, l => { σ with D := l } | .P, l => { σ with P := l }
  | .Q, l => { σ with Q := l } | .sc, l => { σ with sc := l }

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
  exact ⟨congrFun h .inp, congrFun h .out, congrFun h .bad, congrFun h .A, congrFun h .Pd,
    congrFun h .Bn, congrFun h .Bt, congrFun h .F, congrFun h .N, congrFun h .M, congrFun h .R,
    congrFun h .C, congrFun h .X, congrFun h .Y, congrFun h .Z, congrFun h .T, congrFun h .T2,
    congrFun h .W, congrFun h .Cs, congrFun h .Cns, congrFun h .Ct, congrFun h .E,
    congrFun h .B2, congrFun h .Us, congrFun h .D, congrFun h .P, congrFun h .Q,
    congrFun h .sc⟩

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

end RPPRed


set_option autoImplicit false

namespace RPPRed

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

end RPPRed


set_option autoImplicit false

namespace RPPRed

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
  ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], []⟩

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

end RPPRed


set_option autoImplicit false

namespace RPPRed

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

end RPPRed


set_option autoImplicit false

namespace RPPRed

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

end RPPRed


set_option autoImplicit false

namespace RPPRed

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

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## emitting a list of numbers -/

/-- an emitted item: the counter held by a register, or a constant `0`/`1` -/
abbrev Item := Key ⊕ Bool

def emitItem : Item → Prog
  | .inl k => emitProg k
  | .inr false => pushProg .W .sep
  | .inr true => .seq (pushProg .W .one) (pushProg .W .sep)

def emitSeq : List Item → Prog
  | [] => skipP
  | x :: xs => .seq (emitItem x) (emitSeq xs)

def itemVal (ν : Key → ℕ) : Item → ℕ
  | .inl k => ν k
  | .inr b => if b then 1 else 0

def itemOK (σ : Regs) (ν : Key → ℕ) : Item → Prop
  | .inl k => k ≠ .T ∧ k ≠ .sc ∧ k ≠ .W ∧ σ.get k = enc (Nat.bits (ν k))
  | .inr _ => True

lemma encNats_cons' (k : ℕ) (l : List ℕ) : encNats (k :: l) = encNat k ++ encNats l := by
  simp [encNats]

lemma encNats_append' (l l' : List ℕ) : encNats (l ++ l') = encNats l ++ encNats l' := by
  simp [encNats]

lemma encNat_eq' (k : ℕ) : encNat k = enc (Nat.bits k) ++ [BSym.sep] := by
  simp [encNat, enc, toB]

lemma runs_emitSeq (ν : Key → ℕ) (K : ℕ) (hK : ∀ k, (Nat.bits (ν k)).length ≤ K) :
    ∀ (items : List Item) (σ : Regs), σ.T = [] → σ.sc = [] → (∀ x ∈ items, itemOK σ ν x) →
      Runs (emitSeq items) σ { σ with W := (encNats (items.map (itemVal ν))).reverse ++ σ.W }
        (items.length * (9 * K + 10) + 1) := by
  intro items
  induction items with
  | nil =>
    intro σ _ _ _
    simp only [emitSeq, List.map_nil, List.length_nil, zero_mul, zero_add]
    exact (runs_skip σ).congr rfl
  | cons x xs ih =>
    intro σ hT hsc hok
    have hx := hok x List.mem_cons_self
    obtain ⟨σ1, e1, hσ1, hb⟩ : ∃ σ1, Runs (emitItem x) σ σ1 (9 * K + 8) ∧
        σ1 = { σ with W := (encNat (itemVal ν x)).reverse ++ σ.W } ∧ True := by
      rcases x with k | b
      · obtain ⟨h1, h2, h3, h4⟩ := hx
        refine ⟨_, (runs_emit k h1 h2 h3 σ hT hsc).mono ?_, ?_, trivial⟩
        · rw [h4]; simp only [length_enc]; have := hK k; omega
        · simp [itemVal, encNat_eq', h4]
      · cases b
        · exact ⟨_, (runs_push .W .sep σ).mono (by omega), by simp [Regs.set, Regs.get, itemVal, encNat], trivial⟩
        · refine ⟨_, ((runs_push .W .one σ).seq (runs_push .W .sep _)).mono (by omega), ?_, trivial⟩
          simp [Regs.set, Regs.get, itemVal, encNat]
    subst hσ1
    have hok' : ∀ y ∈ xs, itemOK { σ with W := (encNat (itemVal ν x)).reverse ++ σ.W } ν y := by
      intro y hy
      have := hok y (List.mem_cons_of_mem _ hy)
      rcases y with k | b
      · obtain ⟨h1, h2, h3, h4⟩ := this
        refine ⟨h1, h2, h3, ?_⟩
        rw [← h4]; cases k <;> first | exact absurd rfl h3 | rfl
      · trivial
    have e2 := ih { σ with W := (encNat (itemVal ν x)).reverse ++ σ.W } hT hsc hok'
    simp only [emitSeq]
    refine ((e1.seq e2).congr ?_).mono ?_
    · simp [encNats_cons']
    · simp; nlinarith

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## Directed generation, block A: the arcs `⟨s,0⟩ → ⟨s,1⟩ → ⟨s,0⟩` -/

def blockA (n i : ℕ) : List ℕ := (List.range i).flatMap (fun s => [s, n + s, 0, 1, n + s, s, 0, 0])

def itemsA : List Item :=
  [.inl .Cs, .inl .Cns, .inr false, .inr true, .inl .Cns, .inl .Cs, .inr false, .inr false]

def bodyA : Prog :=
  .seq (popProg .R) (.seq (emitSeq itemsA) (.seq (incProg .Cs .T) (incProg .Cns .T)))

def loopA : Prog := .loop (fun h => (h .R).isSome) bodyA

def gd1 : Prog := .seq (copyProg .Bn .Cns .sc) (copyProg .N .R .sc)

def gA (n : ℕ) (bs : List Bool) (i : ℕ) : Regs :=
  { st6 n bs with
    R := List.replicate (n - i) .one
    Cs := enc (Nat.bits i)
    Cns := enc (Nat.bits (n + i))
    W := (encNats (blockA n i)).reverse }

lemma runs_gd1 (n : ℕ) (bs : List Bool) :
    Runs gd1 (st6 n bs) (gA n bs 0) (12 * n + 7) := by
  have e1 := runs_copy .Bn .Cns .sc (by decide) (by decide) (by decide) (st6 n bs) rfl
  have e2 := runs_copy .N .R .sc (by decide) (by decide) (by decide)
    ((st6 n bs).set .Cns ((st6 n bs).get .Bn ++ (st6 n bs).get .Cns)) rfl
  refine ((e1.seq e2).congr ?_).mono ?_
  · simp [st6, gA, Regs.set, Regs.get, Regs.empty, blockA, encNats]
  · have h1 := len_bits_le n
    simp [st6, Regs.set, Regs.get]; omega

lemma len_bits_le_of_le {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ b :=
  le_trans (len_bits_mono h) (len_bits_le b)

lemma stepA (n : ℕ) (bs : List Bool) (i : ℕ) (hi : i < n) :
    Runs bodyA (gA n bs i) (gA n bs (i + 1)) (100 * (2 * n + 1)) := by
  have e1 := runs_pop .R (gA n bs i)
  set σ1 := (gA n bs i).set .R ((gA n bs i).get .R).tail with hσ1
  let ν : Key → ℕ := fun k => if k = .Cs then i else if k = .Cns then n + i else 0
  have hK : ∀ k, (Nat.bits (ν k)).length ≤ 2 * n := by
    intro k
    by_cases h1 : k = .Cs
    · simp only [ν, h1, if_true]; exact len_bits_le_of_le (by omega)
    · by_cases h2 : k = .Cns
      · simp only [ν, h2, if_true]; simp only [show (Key.Cns = Key.Cs) = False by decide, if_false]
        exact len_bits_le_of_le (by omega)
      · simp only [ν, h1, h2, if_false]; simp
  have e2 := runs_emitSeq ν (2 * n) hK itemsA σ1 rfl rfl (by
    intro x hx
    simp only [itemsA, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [itemOK, ν, hσ1, gA, Regs.set, Regs.get])
  set σ2 := { σ1 with W := (encNats (itemsA.map (itemVal ν))).reverse ++ σ1.W } with hσ2
  have e3 := runs_inc .Cs .T (by decide) σ2 (Nat.bits i) (by simp [hσ2, hσ1, gA, Regs.set, Regs.get])
    (by simp [hσ2, hσ1, gA, Regs.set, Regs.get, st6, Regs.empty])
  set σ3 := σ2.set .Cs (enc (incL (Nat.bits i))) with hσ3
  have e4 := runs_inc .Cns .T (by decide) σ3 (Nat.bits (n + i))
    (by simp [hσ3, hσ2, hσ1, gA, Regs.set, Regs.get])
    (by simp [hσ3, hσ2, hσ1, gA, Regs.set, Regs.get, st6, Regs.empty])
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · rw [hσ3]; simp only [incL_bits]
    have hR : n - i - 1 = n - (i + 1) := by omega
    simp [hσ3, hσ2, hσ1, gA, Regs.set, Regs.get, itemsA, itemVal, ν, blockA, List.range_succ,
      encNats_append', List.replicate_succ, hR, Nat.add_assoc]
  · have h1 : (Nat.bits i).length ≤ 2 * n := len_bits_le_of_le (by omega)
    have h2 : (Nat.bits (n + i)).length ≤ 2 * n := len_bits_le_of_le (by omega)
    simp only [itemsA, List.length_cons, List.length_nil]
    omega

lemma runs_loopA (n : ℕ) (bs : List Bool) :
    Runs loopA (gA n bs 0) (gA n bs n) (n * (100 * (2 * n + 1) + 2) + 1) := by
  refine Runs.loopU _ bodyA (gA n bs) _ _ (fun j hj => ⟨?_, stepA n bs j hj⟩) ?_
  · have : n - j ≠ 0 := by omega
    obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, gA, hk, List.replicate_succ]
  · simp [hd, Regs.get, gA]

/-! ## block B: the edges, row by row -/

def adjB (bs : List Bool) (n s t : ℕ) : Bool := bs.getD (s * n + t) false

def rowE (bs : List Bool) (n s t : ℕ) : List (ℕ × ℕ) :=
  (List.range t).flatMap (fun t' => if adjB bs n s t' then [(s, t')] else [])

def allE (bs : List Bool) (n s : ℕ) : List (ℕ × ℕ) :=
  (List.range s).flatMap (fun s' => rowE bs n s' n)

def quad (p : ℕ × ℕ) : List ℕ := [p.1, p.2, 1, 0]

def WofD (bs : List Bool) (n s t : ℕ) : List BSym :=
  (encNats (blockA n n ++ (allE bs n s ++ rowE bs n s t).flatMap quad)).reverse

/-- before row `s` -/
def gR (n : ℕ) (bs : List Bool) (s : ℕ) : Regs :=
  { st6 n bs with
    W := WofD bs n s 0
    E := enc (Nat.bits (2 * n + (allE bs n s).length))
    B2 := enc (Nat.bits (2 * n))
    R := List.replicate (n - s) .one
    Cs := enc (Nat.bits s)
    M := enc (bs.drop (s * n)) }

/-- in row `s`, before column `t` -/
def gC (n : ℕ) (bs : List Bool) (s t : ℕ) : Regs :=
  { st6 n bs with
    W := WofD bs n s t
    E := enc (Nat.bits (2 * n + (allE bs n s).length + (rowE bs n s t).length))
    B2 := enc (Nat.bits (2 * n))
    R := List.replicate (n - (s + 1)) .one
    Cs := enc (Nat.bits s)
    M := enc (bs.drop (s * n + t))
    C := List.replicate (n - t) .one
    Ct := enc (Nat.bits t) }

def gd3 : Prog :=
  .seq (clearProg .Cs) (.seq (clearProg .Cns) (.seq (copyProg .Bn .E .sc)
    (.seq (.branch (fun h => (h .E).isSome) (pushProg .E .zero) skipP)
      (.seq (copyProg .E .B2 .sc) (copyProg .N .R .sc)))))

lemma enc_bits_double (n : ℕ) :
    enc (Nat.bits (2 * n)) = if n = 0 then [] else BSym.zero :: enc (Nat.bits n) := by
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg h, bits_double n h]; rfl

lemma runs_gd3 (n : ℕ) (bs : List Bool) :
    Runs gd3 (gA n bs n) (gR n bs 0) (100 * (n + 1)) := by
  have e1 := runs_clear .Cs (gA n bs n)
  have e2 := runs_clear .Cns ((gA n bs n).set .Cs [])
  set σ2 := ((gA n bs n).set .Cs []).set .Cns [] with hσ2
  have e3 := runs_copy .Bn .E .sc (by decide) (by decide) (by decide) σ2 rfl
  set σ3 := σ2.set .E (σ2.get .Bn ++ σ2.get .E) with hσ3
  have h3E : σ3.get .E = enc (Nat.bits n) := by simp [hσ3, hσ2, gA, st6, Regs.set, Regs.get, Regs.empty]
  obtain ⟨σ4, e4, h4⟩ : ∃ σ4, Runs (.branch (fun h => (h .E).isSome) (pushProg .E .zero) skipP) σ3 σ4 2 ∧
      σ4 = σ3.set .E (enc (Nat.bits (2 * n))) := by
    by_cases hn : n = 0
    · subst hn
      refine ⟨σ3, (runs_skip σ3).brF (by simp [hd, h3E]), ?_⟩
      rw [show enc (Nat.bits (2 * 0)) = σ3.get .E by rw [h3E], Regs.set_get]
    · refine ⟨_, (runs_push .E .zero σ3).brT ?_, ?_⟩
      · simp only [hd]; rw [h3E]; exact isSome_head_of_ne_nil (enc_bits_ne_nil hn)
      · rw [enc_bits_double, if_neg hn, h3E]
  have e5 := runs_copy .E .B2 .sc (by decide) (by decide) (by decide) σ4 (by rw [h4]; rfl)
  set σ5 := σ4.set .B2 (σ4.get .E ++ σ4.get .B2) with hσ5
  have e6 := runs_copy .N .R .sc (by decide) (by decide) (by decide) σ5 (by rw [hσ5, h4]; rfl)
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).congr ?_).mono ?_
  · rw [hσ5, h4, hσ3, hσ2]
    simp [gA, gR, st6, Regs.set, Regs.get, Regs.empty, WofD, allE, rowE]
  · have l1 : ((gA n bs n).get .Cs).length ≤ n := by simp [gA, Regs.get]; exact len_bits_le n
    have l2 : (((gA n bs n).set .Cs []).get .Cns).length ≤ 2 * n := by
      simp [gA, Regs.get, Regs.set]; exact len_bits_le_of_le (by omega)
    have l3 : (σ2.get .Bn).length ≤ n := by simp [hσ2, gA, st6, Regs.get, Regs.set]; exact len_bits_le n
    have l4 : (σ4.get .E).length ≤ 2 * n := by
      rw [h4]; simp [Regs.get, Regs.set]; exact len_bits_le_of_le (by omega)
    have l5 : (σ5.get .N).length = n := by simp [hσ5, h4, hσ3, hσ2, gA, st6, Regs.get, Regs.set]
    omega

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity

def itemsB : List Item := [.inl .Cs, .inl .Ct, .inr true, .inr false]

def colBody : Prog :=
  .seq (popProg .C)
    (.seq (.branch (fun h => decide (h .M = some .one)) (.seq (emitSeq itemsB) (incProg .E .T)) skipP)
      (.seq (popProg .M) (incProg .Ct .T)))

def colLoop : Prog := .loop (fun h => (h .C).isSome) colBody

def rowBody : Prog :=
  .seq (popProg .R) (.seq (copyProg .N .C .sc) (.seq colLoop (.seq (clearProg .Ct) (incProg .Cs .T))))

def rowLoop : Prog := .loop (fun h => (h .R).isSome) rowBody

lemma drop_eq_cons_getD (bs : List Bool) (k : ℕ) (hk : k < bs.length) :
    bs.drop k = bs.getD k false :: bs.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem _ _ hk]

lemma rowE_succ (bs : List Bool) (n s t : ℕ) :
    rowE bs n s (t + 1) = rowE bs n s t ++ (if adjB bs n s t then [(s, t)] else []) := by
  simp [rowE, List.range_succ, List.flatMap_append]

lemma allE_succ (bs : List Bool) (n s : ℕ) :
    allE bs n (s + 1) = allE bs n s ++ rowE bs n s n := by
  simp [allE, List.range_succ, List.flatMap_append]

lemma len_rowE_le (bs : List Bool) (n s t : ℕ) : (rowE bs n s t).length ≤ t := by
  induction t with
  | zero => simp [rowE]
  | succ t ih => rw [rowE_succ]; split_ifs <;> simp <;> omega

lemma len_allE_le (bs : List Bool) (n s : ℕ) : (allE bs n s).length ≤ s * n := by
  induction s with
  | zero => simp [allE]
  | succ s ih => rw [allE_succ, List.length_append]; have := len_rowE_le bs n s n; nlinarith

lemma stepC (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s t : ℕ) (hs : s < n) (ht : t < n) :
    Runs colBody (gC n bs s t) (gC n bs s (t + 1)) (200 * (n * n + 2 * n + 1)) := by
  have hk : s * n + t < bs.length := by rw [hbs]; nlinarith
  have hM : (gC n bs s t).M = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := by
    simp only [gC]; rw [drop_eq_cons_getD bs _ hk]; rfl
  have e1 := runs_pop .C (gC n bs s t)
  set σ1 := (gC n bs s t).set .C ((gC n bs s t).get .C).tail with hσ1
  have hσ1M : σ1.M = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := hM
  let ν : Key → ℕ := fun k => if k = .Cs then s else if k = .Ct then t else 0
  have hK : ∀ k, (Nat.bits (ν k)).length ≤ n := by
    intro k
    by_cases h1 : k = .Cs
    · simp only [ν, h1, if_true]; exact len_bits_le_of_le (by omega)
    · by_cases h2 : k = .Ct
      · simp only [ν, h2, if_true]; simp only [show (Key.Ct = Key.Cs) = False by decide, if_false]
        exact len_bits_le_of_le (by omega)
      · simp only [ν, h1, h2, if_false]; simp
  have hElen : (Nat.bits (2 * n + (allE bs n s).length + (rowE bs n s t).length)).length ≤
      n * n + 2 * n := by
    apply len_bits_le_of_le
    have := len_allE_le bs n s; have := len_rowE_le bs n s t
    have : s * n + t ≤ n * n := by nlinarith
    omega
  -- the branch
  obtain ⟨σ2, e2, hσ2⟩ : ∃ σ2, Runs (.branch (fun h => decide (h .M = some .one))
      (.seq (emitSeq itemsB) (incProg .E .T)) skipP) σ1 σ2 (100 * (n * n + 2 * n + 1)) ∧
      σ2 = { σ1 with
        W := (encNats ((if adjB bs n s t then [(s, t)] else []).flatMap quad)).reverse ++ σ1.W
        E := enc (Nat.bits (2 * n + (allE bs n s).length + (rowE bs n s (t + 1)).length)) } := by
    cases hadj : adjB bs n s t
    · refine ⟨σ1, ((runs_skip σ1).brF ?_).mono (by omega), ?_⟩
      · simp [hd, Regs.get, hσ1M, hadj, toB]
      · rw [rowE_succ, hadj]; simp [hσ1, gC, Regs.set, Regs.get, encNats]
    · have e21 := runs_emitSeq ν n hK itemsB σ1 rfl rfl (by
        intro x hx
        simp only [itemsB, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [itemOK, ν, hσ1, gC, Regs.set, Regs.get])
      set σ21 := { σ1 with W := (encNats (itemsB.map (itemVal ν))).reverse ++ σ1.W } with hσ21
      have e22 := runs_inc .E .T (by decide) σ21 _ (by simp [hσ21, hσ1, gC, Regs.set, Regs.get]; rfl)
        (by simp [hσ21, hσ1, gC, Regs.set, Regs.get, st6, Regs.empty])
      refine ⟨_, ((e21.seq e22).brT ?_).mono ?_, ?_⟩
      · simp [hd, Regs.get, hσ1M, hadj, toB]
      · simp only [itemsB, List.length_cons, List.length_nil]; nlinarith
      · rw [incL_bits, rowE_succ, hadj]
        simp [hσ21, hσ1, gC, Regs.set, Regs.get, itemsB, itemVal, ν, quad, Nat.add_assoc]
  have e3 := runs_pop .M σ2
  set σ3 := σ2.set .M (σ2.get .M).tail with hσ3
  have e4 := runs_inc .Ct .T (by decide) σ3 (Nat.bits t) (by simp [hσ3, hσ2, hσ1, gC, Regs.set, Regs.get])
    (by simp [hσ3, hσ2, hσ1, gC, Regs.set, Regs.get, st6, Regs.empty])
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · rw [incL_bits]
    have hC : n - t - 1 = n - (t + 1) := by omega
    rw [hσ3, hσ2]
    simp only [Regs.set, Regs.get, hσ1M]
    simp [hσ1, gC, Regs.set, Regs.get, WofD, hC, List.flatMap_append, encNats_append', rowE_succ,
      Nat.add_assoc]
  · have : (Nat.bits t).length ≤ n := len_bits_le_of_le (by omega)
    nlinarith

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity

lemma runs_colLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs colLoop (gC n bs s 0) (gC n bs s n) (n * (200 * (n * n + 2 * n + 1) + 2) + 1) := by
  refine Runs.loopU _ colBody (gC n bs s) _ _ (fun j hj => ⟨?_, stepC n bs hbs s j hs hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, gC, hk, List.replicate_succ]
  · simp [hd, Regs.get, gC]

lemma stepR (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs rowBody (gR n bs s) (gR n bs (s + 1)) (n * (200 * (n * n + 2 * n + 1) + 2) + 30 * n + 30) := by
  have e1 := runs_pop .R (gR n bs s)
  have e2 := runs_copy .N .C .sc (by decide) (by decide) (by decide)
    ((gR n bs s).set .R ((gR n bs s).get .R).tail) rfl
  have h0 : ((gR n bs s).set .R ((gR n bs s).get .R).tail).set .C
      (((gR n bs s).set .R ((gR n bs s).get .R).tail).get .N ++
        ((gR n bs s).set .R ((gR n bs s).get .R).tail).get .C) = gC n bs s 0 := by
    have hR : n - s - 1 = n - (s + 1) := by omega
    simp [gR, gC, st6, Regs.set, Regs.get, Regs.empty, rowE, WofD, hR, List.tail_replicate]
  have e3 := runs_colLoop n bs hbs s hs
  have e4 := runs_clear .Ct (gC n bs s n)
  have e5 := runs_inc .Cs .T (by decide) ((gC n bs s n).set .Ct []) (Nat.bits s)
    (by simp [gC, Regs.set, Regs.get]) (by simp [gC, Regs.set, Regs.get, st6, Regs.empty])
  refine ((e1.seq ((e2.congr h0).seq (e3.seq (e4.seq e5)))).congr ?_).mono ?_
  · rw [incL_bits]
    simp [gR, gC, st6, Regs.set, Regs.get, Regs.empty, WofD, allE_succ, rowE, Nat.succ_mul,
      Nat.add_assoc]
  · have l1 : ((gR n bs s).set .R ((gR n bs s).get .R).tail).get .N = List.replicate n .one := by
      simp [gR, st6, Regs.get, Regs.set]
    have l2 : ((gC n bs s n).get .Ct).length ≤ n := by
      simp [gC, Regs.get]; exact len_bits_le n
    have l3 : (Nat.bits s).length ≤ n := len_bits_le_of_le (by omega)
    rw [l1]; simp only [List.length_replicate]
    omega

lemma runs_rowLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs rowLoop (gR n bs 0) (gR n bs n)
      (n * (n * (200 * (n * n + 2 * n + 1) + 2) + 30 * n + 32) + 1) := by
  refine Runs.loopU _ rowBody (gR n bs) _ _ (fun j hj => ⟨?_, stepR n bs hbs j hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, gR, hk, List.replicate_succ]
  · simp [hd, Regs.get, gR]

/-! ## assembling the output -/

def asm : Prog :=
  .seq (pushProg .out .sep) (.seq (copyProg .Bn .out .sc) (.seq (mvProg .W .out)
    (.seq (pushProg .out .sep) (.seq (copyProg .E .out .sc)
      (.seq (pushProg .out .sep) (copyProg .B2 .out .sc))))))

/-- the numbers written by the directed reduction -/
def outListD (n : ℕ) (bs : List Bool) : List ℕ :=
  [2 * n, 2 * n + (allE bs n n).length] ++ blockA n n ++ (allE bs n n).flatMap quad ++ [n]

lemma runs_asm (n : ℕ) (bs : List Bool) (L : ℕ) (hL : (WofD bs n n 0).length ≤ L) (hn : 2 * n ≤ L)
    (hE : (Nat.bits (2 * n + (allE bs n n).length)).length ≤ L) :
    ∃ τ, Runs asm (gR n bs n) τ (30 * L + 30) ∧ τ.out = encNats (outListD n bs) := by
  have e1 := runs_push .out .sep (gR n bs n)
  set σ1 := (gR n bs n).set .out (.sep :: (gR n bs n).get .out) with hσ1
  have e2 := runs_copy .Bn .out .sc (by decide) (by decide) (by decide) σ1 rfl
  set σ2 := σ1.set .out (σ1.get .Bn ++ σ1.get .out) with hσ2
  have e3 := runs_mv .W .out (by decide) σ2
  set σ3 := (σ2.set .W []).set .out ((σ2.get .W).reverse ++ σ2.get .out) with hσ3
  have e4 := runs_push .out .sep σ3
  set σ4 := σ3.set .out (.sep :: σ3.get .out) with hσ4
  have e5 := runs_copy .E .out .sc (by decide) (by decide) (by decide) σ4 rfl
  set σ5 := σ4.set .out (σ4.get .E ++ σ4.get .out) with hσ5
  have e6 := runs_push .out .sep σ5
  set σ6 := σ5.set .out (.sep :: σ5.get .out) with hσ6
  have e7 := runs_copy .B2 .out .sc (by decide) (by decide) (by decide) σ6 rfl
  refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).mono ?_, ?_⟩
  · have l2 : (σ1.get .Bn).length ≤ L := by
      simp [hσ1, gR, st6, Regs.get, Regs.set]; exact le_trans (len_bits_le n) (by omega)
    have l3 : (σ2.get .W).length ≤ L := by simp [hσ2, hσ1, gR, Regs.get, Regs.set]; exact hL
    have l5 : (σ4.get .E).length ≤ L := by
      simp [hσ4, hσ3, hσ2, hσ1, gR, Regs.get, Regs.set]; exact hE
    have l7 : (σ6.get .B2).length ≤ L := by
      simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, gR, Regs.get, Regs.set]
      exact le_trans (len_bits_le _) hn
    omega
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, gR, st6, Regs.get, Regs.set, Regs.empty, WofD, outListD,
      encNats_append', encNats_cons', encNat_eq', rowE, encNats]

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## the special case `n = 1` of the directed reduction -/

def gd0 : Prog :=
  .seq (copyProg .N .X .sc) (.seq (popProg .X)
    (.seq (.branch (fun h => (h .X).isNone && (h .N).isSome && decide (h .M = some .zero))
      (pushProg .bad .one) skipP) (clearProg .X)))

/-- the excluded case: one vertex without a loop -/
def special (n : ℕ) (bs : List Bool) : Prop := n = 1 ∧ bs = [false]

instance (n : ℕ) (bs : List Bool) : Decidable (special n bs) := by unfold special; infer_instance

lemma runs_gd0 (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    ∃ τ, Runs gd0 (st6 n bs) τ (10 * n + 10) ∧ (¬ special n bs → τ = st6 n bs) ∧
      (special n bs → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_copy .N .X .sc (by decide) (by decide) (by decide) (st6 n bs) rfl
  set σ1 := (st6 n bs).set .X ((st6 n bs).get .N ++ (st6 n bs).get .X) with hσ1
  have e2 := runs_pop .X σ1
  set σ2 := σ1.set .X (σ1.get .X).tail with hσ2
  have h2X : σ2.X = List.replicate (n - 1) .one := by
    simp [hσ2, hσ1, st6, Regs.set, Regs.get, Regs.empty, List.tail_replicate]
  have h2N : σ2.N = List.replicate n .one := by simp [hσ2, hσ1, st6, Regs.set, Regs.get]
  have h2M : σ2.M = enc bs := by simp [hσ2, hσ1, st6, Regs.set, Regs.get]
  have l1 : ((st6 n bs).get .N).length = n := by simp [st6, Regs.get]
  by_cases hsp : special n bs
  · obtain ⟨rfl, rfl⟩ := hsp
    have e3 : Runs (.branch (fun h => (h .X).isNone && (h .N).isSome && decide (h .M = some .zero))
        (pushProg .bad .one) skipP) σ2 (σ2.set .bad (.one :: σ2.get .bad)) 2 :=
      (runs_push .bad .one σ2).brT (by simp [hd, Regs.get, h2X, h2N, h2M, enc])
    have e4 := runs_clear .X (σ2.set .bad (.one :: σ2.get .bad))
    refine ⟨_, (e1.seq (e2.seq (e3.seq e4))).mono ?_, fun h => absurd ⟨rfl, rfl⟩ h, fun _ => ?_⟩
    · rw [l1]; simp [Regs.get, Regs.set, h2X]
    · simp [Regs.set, Regs.get, hσ2, hσ1, st6, Regs.empty]
  · have htest : (fun h : Key → Option BSym => (h .X).isNone && (h .N).isSome &&
        decide (h .M = some .zero)) (hd σ2) = false := by
      simp only [hd, Regs.get, h2X, h2N, h2M]
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        · simp
        · have : bs.length = 1 := by simpa using hbs
          match bs, this with
          | [b], _ =>
            cases b
            · exact absurd ⟨rfl, rfl⟩ hsp
            · simp [enc, toB]
      · obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
        simp [hk, List.replicate_succ]
    have e3 := (runs_skip σ2).brF (t := fun h : Key → Option BSym => (h .X).isNone && (h .N).isSome &&
        decide (h .M = some .zero)) (p := pushProg .bad .one) htest
    have e4 := runs_clear .X σ2
    refine ⟨_, (e1.seq (e2.seq (e3.seq e4))).congr ?_ |>.mono ?_, fun _ => rfl, fun h => absurd h hsp⟩
    · simp [Regs.set, hσ2, hσ1, st6, Regs.empty]
    · rw [l1]; simp only [Regs.get, h2X, List.length_replicate]; omega

/-! ## the whole directed reduction -/

def genD : Prog := .seq gd0 (gate (.seq gd1 (.seq loopA (.seq gd3 (.seq rowLoop asm)))))

def mainD : Prog := .seq parseProg (gate genD)

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

lemma mem_blockA (n x : ℕ) (hx : x ∈ blockA n n) : x ≤ 2 * n := by
  simp only [blockA, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at hx
  obtain ⟨s, hs, h⟩ := hx
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

lemma mem_rowE (bs : List Bool) (n s t : ℕ) (p : ℕ × ℕ) (hp : p ∈ rowE bs n s t) :
    p.1 = s ∧ p.2 < t := by
  simp only [rowE, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨t', ht', h⟩ := hp
  split_ifs at h
  · simp at h; subst h; exact ⟨rfl, ht'⟩
  · simp at h

lemma mem_allE (bs : List Bool) (n s : ℕ) (p : ℕ × ℕ) (hp : p ∈ allE bs n s) :
    p.1 < s ∧ p.2 < n := by
  simp only [allE, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨s', hs', h⟩ := hp
  obtain ⟨h1, h2⟩ := mem_rowE bs n s' n p h
  exact ⟨h1 ▸ hs', h2⟩

lemma len_WofD (bs : List Bool) (n : ℕ) :
    (WofD bs n n 0).length ≤ (8 * n + 4 * (n * n)) * (2 * n + 1) := by
  unfold WofD
  rw [List.length_reverse]
  have hmem : ∀ x ∈ blockA n n ++ (allE bs n n ++ rowE bs n n 0).flatMap quad, x ≤ 2 * n := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact mem_blockA n x h
    · simp only [rowE, List.range_zero, List.flatMap_nil, List.append_nil, List.mem_flatMap] at h
      obtain ⟨p, hp, hx⟩ := h
      have := mem_allE bs n n p hp
      simp only [quad, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> omega
  refine le_trans (length_encNats_le _ _ hmem) (Nat.mul_le_mul_right _ ?_)
  have h1 : (blockA n n).length = 8 * n := by
    simp [blockA, List.length_flatMap, List.sum_replicate, List.map_const', Nat.mul_comm]
  have h2 : ((allE bs n n ++ rowE bs n n 0).flatMap quad).length = 4 * (allE bs n n).length := by
    simp [rowE, quad, List.length_flatMap, List.sum_replicate, List.map_const', Nat.mul_comm]
  have h3 := len_allE_le bs n n
  rw [List.length_append, h1, h2]; omega

lemma runs_genD_body (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (L : ℕ) (hL : n * n ≤ L)
    (hnL : n ≤ L) :
    ∃ τ, Runs (.seq gd1 (.seq loopA (.seq gd3 (.seq rowLoop asm)))) (st6 n bs) τ (4000 * (L + 1) ^ 2) ∧
      τ.out = encNats (outListD n bs) := by
  have e1 := runs_gd1 n bs
  have e2 := runs_loopA n bs
  have e3 := runs_gd3 n bs
  have e4 := runs_rowLoop n bs hbs
  have hW := len_WofD bs n
  have hE : (Nat.bits (2 * n + (allE bs n n).length)).length ≤ 3 * L := by
    apply len_bits_le_of_le; have := len_allE_le bs n n; omega
  have hW' : (WofD bs n n 0).length ≤ 36 * (L + 1) ^ 2 := by
    have : n * n * n ≤ L * L := by nlinarith
    nlinarith
  obtain ⟨τ, e5, h5⟩ := runs_asm n bs (36 * (L + 1) ^ 2) hW' (by nlinarith) (by nlinarith)
  refine ⟨τ, (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_, h5⟩
  have a1 : n * (n * n) ≤ L * L := by nlinarith
  have a2 : n * n * (n * n) ≤ L * L := Nat.mul_le_mul hL hL
  nlinarith

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity

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

def gD (n : ℕ) (bs : List Bool) : List BSym :=
  if special n bs then [] else encNats (outListD n bs)

noncomputable def fD : List BSym → List BSym := decodeThen gD

lemma n_le_of_sq {n m : ℕ} (h : m = n * n) : n ≤ m := by
  subst h; rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Nat.le_mul_of_pos_left n h

theorem mainD_spec (w : List BSym) :
    ∃ τ, Runs mainD (initR w) τ (5000 * (w.length + 1) ^ 2) ∧ τ.out = fD w := by
  obtain ⟨τ, e, h⟩ := parse_spec w
  rcases h with ⟨n, bs, hbs, hw, hτ⟩ | ⟨hb, ho, hinv⟩
  · subst hτ
    have hbL : bs.length ≤ w.length := hw ▸ length_code n bs
    have hL : n * n ≤ w.length := hbs ▸ hbL
    have hnL : n ≤ w.length := le_trans (n_le_of_sq hbs) hbL
    obtain ⟨τ0, e0, h0a, h0b⟩ := runs_gd0 n bs hbs
    by_cases hsp : special n bs
    · obtain ⟨hb0, ho0⟩ := h0b hsp
      refine ⟨τ0, (e.seq (runs_gate_ok rfl (e0.seq (runs_gate_skip hb0)))).mono ?_, ?_⟩
      · have : (w.length + 1) ^ 2 ≥ w.length + 1 := by nlinarith
        nlinarith
      · rw [ho0, fD, hw, decodeThen_code gD n bs hbs, gD, if_pos hsp]
    · have hτ0 := h0a hsp
      subst hτ0
      obtain ⟨τ1, e1, h1⟩ := runs_genD_body n bs hbs w.length hL hnL
      refine ⟨τ1, (e.seq (runs_gate_ok rfl (e0.seq (runs_gate_ok rfl e1)))).mono ?_, ?_⟩
      · have : (w.length + 1) ^ 2 ≥ w.length + 1 := by nlinarith
        nlinarith
      · rw [h1, fD, hw, decodeThen_code gD n bs hbs, gD, if_neg hsp]
  · refine ⟨τ, (e.seq (runs_gate_skip hb)).mono ?_, ?_⟩
    · have : (w.length + 1) ^ 2 ≥ 1 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    · rw [ho, fD, decodeThen_invalid gD w hinv]

lemma initR_get (w : List BSym) : (initR w).get = fun j => if j = .inp then w else [] := by
  funext j; cases j <;> rfl

theorem fD_poly : PolyTimeComputable fD := by
  obtain ⟨k, hk⟩ := polynomial_absorb 5000 2 0
  refine stack_program_polytime mainD .inp .out fD k (fun w => ?_)
  obtain ⟨τ, ⟨m, hm, ex⟩, ho⟩ := mainD_spec w
  refine ⟨τ.get, m, le_trans hm (by have := hk w.length; omega), ?_, ho⟩
  rw [← initR_get]; exact ex

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC
open SchedComplexity.NoWait (HasHamiltonCircuit dhpCode)

/-! ## lists over `Fin n` versus `range n` -/

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

/-! ## the code of the directed instance -/


lemma flatMap_filter_map {α β : Type} (l : List α) (p : α → Bool) (g : α → List β) :
    (l.filter p).flatMap g = l.flatMap (fun x => if p x then g x else []) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [List.filter_cons, h, ih]

def arcFlat {m : ℕ} (a : Fin m × Fin m × ℕ × Bool) : List ℕ :=
  [a.1.val, a.2.1.val, a.2.2.1, if a.2.2.2 then 1 else 0]

lemma rpCode_eq' (I : RPInstance) :
    rpCode I = encNats (I.n :: I.arcs.length :: (I.arcs.flatMap arcFlat) ++ [I.k]) := rfl

lemma drp_flat1 (n : ℕ) :
    ((List.finRange n).flatMap (fun s : Fin n =>
      [((Fin.castAdd n s : Fin (n + n)), (Fin.natAdd n s : Fin (n + n)), (0 : ℕ), true),
       ((Fin.natAdd n s : Fin (n + n)), (Fin.castAdd n s : Fin (n + n)), (0 : ℕ), false)])).flatMap arcFlat =
      blockA n n := by
  rw [List.flatMap_assoc]
  unfold blockA
  apply finRange_flatMap'
  intro s
  simp [arcFlat, Nat.add_comm]

lemma drp_flat2 (n : ℕ) (bs : List Bool) :
    ((List.finRange n).flatMap (fun s : Fin n =>
      ((List.finRange n).filter (fun t => adjOf n bs s t)).map
        (fun t => ((Fin.castAdd n s : Fin (n + n)), (Fin.castAdd n t : Fin (n + n)), (1 : ℕ), false)))).flatMap arcFlat =
      (allE bs n n).flatMap quad := by
  rw [List.flatMap_assoc]
  unfold allE rowE
  rw [List.flatMap_assoc]
  apply finRange_flatMap'
  intro s
  rw [List.flatMap_map, flatMap_filter_map, List.flatMap_assoc]
  apply finRange_flatMap'
  intro t
  simp only [adjOf]
  split_ifs with h <;> simp_all [arcFlat, quad]

lemma rpCode_drp (n : ℕ) (bs : List Bool) :
    rpCode (drpOfGraph (adjOf n bs)) = encNats (outListD n bs) := by
  rw [rpCode_eq']
  have hflat : (drpOfGraph (adjOf n bs)).arcs.flatMap arcFlat = blockA n n ++ (allE bs n n).flatMap quad := by
    simp only [drpOfGraph]
    rw [List.flatMap_append, drp_flat1, drp_flat2]
  have hlen : (drpOfGraph (adjOf n bs)).arcs.length = 2 * n + (allE bs n n).length := by
    have h4 : ∀ {m : ℕ} (l : List (Fin m × Fin m × ℕ × Bool)), (l.flatMap arcFlat).length = 4 * l.length := by
      intro m l; induction l with
      | nil => simp
      | cons a l ih => simp [arcFlat, ih]; ring
    have hq : ∀ l : List (ℕ × ℕ), (l.flatMap quad).length = 4 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp [quad, ih]; ring
    have hb : (blockA n n).length = 8 * n := by
      simp [blockA, List.length_flatMap, List.sum_replicate, List.map_const', Nat.mul_comm]
    have := congrArg List.length hflat
    rw [h4, List.length_append, hb, hq] at this
    omega
  rw [hflat, hlen]
  simp only [outListD, drpOfGraph]
  congr 1
  simp [two_mul, List.append_assoc]

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC
open SchedComplexity.NoWait (HasHamiltonCircuit dhpCode)

/-! ## injectivity of the instance code -/

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

lemma arcFlat_inj {m : ℕ} : ∀ (l l' : List (Fin m × Fin m × ℕ × Bool)),
    l.flatMap arcFlat = l'.flatMap arcFlat → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons a l' => simp [arcFlat] at h
  | cons a l ih =>
    intro l' h
    cases l' with
    | nil => simp [arcFlat] at h
    | cons a' l' =>
      rw [List.flatMap_cons, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp [arcFlat])
      rw [ih l' h2]
      obtain ⟨x1, x2, x3, x4⟩ := a
      obtain ⟨y1, y2, y3, y4⟩ := a'
      simp only [arcFlat, List.cons.injEq, and_true] at h1
      obtain ⟨e1, e2, e3, e4⟩ := h1
      have : x4 = y4 := by cases x4 <;> cases y4 <;> simp_all
      rw [Fin.ext e1, Fin.ext e2, e3, this]

lemma rpCode_inj {I I' : RPInstance} (h : rpCode I = rpCode I') : I = I' := by
  rw [rpCode_eq', rpCode_eq'] at h
  have h' := encNats_inj _ _ h
  simp only [List.cons_append, List.cons.injEq] at h'
  obtain ⟨hn, -, hrest⟩ := h'
  obtain ⟨hf, hk⟩ := List.append_inj' hrest rfl
  simp only [List.cons.injEq, and_true] at hk
  obtain ⟨n, arcs, k⟩ := I
  obtain ⟨n', arcs', k'⟩ := I'
  simp only at hn hf hk
  subst hn; subst hk
  rw [arcFlat_inj arcs arcs' hf]

lemma rpCode_ne_nil (I : RPInstance) : rpCode I ≠ [] := by
  rw [rpCode_eq', List.cons_append, encNats_cons', encNat_eq']; simp

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC
open SchedComplexity.NoWait (HasHamiltonCircuit dhpCode)

/-! ## one vertex -/

lemma hc_one (adj : Fin 1 → Fin 1 → Bool) : HasHamiltonCircuit adj ↔ adj 0 0 = true := by
  constructor
  · rintro ⟨σ, h⟩
    have := h 0
    rwa [Subsingleton.elim (σ 0) 0, Subsingleton.elim (σ (finRotate 1 0)) 0] at this
  · intro h
    refine ⟨Equiv.refl _, fun i => ?_⟩
    rwa [Subsingleton.elim (Equiv.refl (Fin 1) i) 0,
      Subsingleton.elim (Equiv.refl (Fin 1) (finRotate 1 i)) 0]

lemma matBits_one (adj : Fin 1 → Fin 1 → Bool) : matBits adj = [adj 0 0] := by
  rw [matBits_eq]
  have := mf_eq adj 0 0
  simp only [Fin.val_zero, zero_mul, add_zero] at this
  simp [this]

def Rone (adj : Fin 1 → Fin 1 → Bool) : List (Fin (1 + 1) × Fin (1 + 1) × ℕ × Bool) :=
  (List.finRange 1).flatMap (fun s =>
    ((List.finRange 1).filter (fun t => adj s t)).map
      (fun t => ((Fin.castAdd 1 s : Fin (1 + 1)), (Fin.castAdd 1 t : Fin (1 + 1)), (1 : ℕ), false)))

lemma drp_one_arcs (adj : Fin 1 → Fin 1 → Bool) :
    (drpOfGraph adj).arcs = (Fin.castAdd 1 (0 : Fin 1), Fin.natAdd 1 (0 : Fin 1), 0, true) ::
      (Fin.natAdd 1 (0 : Fin 1), Fin.castAdd 1 (0 : Fin 1), 0, false) :: Rone adj := by
  simp [drpOfGraph, Rone, List.finRange_succ]

lemma Rone_bit (adj : Fin 1 → Fin 1 → Bool) : ∀ x ∈ Rone adj, x.2.2.2 = false := by
  intro x hx
  simp only [Rone, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, _, _, _, rfl⟩ := hx
  rfl

lemma drp_one_yes (adj : Fin 1 → Fin 1 → Bool) : (drpOfGraph adj).RPYes true := by
  have harcs := drp_one_arcs adj
  have hleq : (drpOfGraph adj).arcs.length = (Rone adj).length + 1 + 1 := by
    rw [harcs]; rfl
  have hlen : 2 ≤ (drpOfGraph adj).arcs.length := by rw [hleq]; omega
  let i0 : Fin (drpOfGraph adj).arcs.length := ⟨0, by omega⟩
  let i1 : Fin (drpOfGraph adj).arcs.length := ⟨1, by omega⟩
  have g0 : (drpOfGraph adj).arcs.get i0 = (Fin.castAdd 1 (0 : Fin 1), Fin.natAdd 1 (0 : Fin 1), 0, true) := by
    simp only [List.get_eq_getElem, i0]
    rw [List.getElem_of_eq harcs]; rfl
  have g1 : (drpOfGraph adj).arcs.get i1 = (Fin.natAdd 1 (0 : Fin 1), Fin.castAdd 1 (0 : Fin 1), 0, false) := by
    simp only [List.get_eq_getElem, i1]
    rw [List.getElem_of_eq harcs]; rfl
  refine ⟨[(i0, true), (i1, true)], ⟨?_, ?_, ?_⟩, ?_⟩
  · intro _ t ht; simp at ht; rcases ht with rfl | rfl <;> rfl
  · intro i
    fin_cases i
    · show (drpOfGraph adj).trDst (i0, true) = (drpOfGraph adj).trSrc (i1, true)
      simp only [RPInstance.trDst, RPInstance.trSrc, if_true, g0, g1]
    · show (drpOfGraph adj).trDst (i1, true) = (drpOfGraph adj).trSrc (i0, true)
      simp only [RPInstance.trDst, RPInstance.trSrc, if_true, g0, g1]
  · intro e he
    refine ⟨true, ?_⟩
    have he0 : e = i0 := by
      unfold RPInstance.IsRequired at he
      rcases e with ⟨k, hk⟩
      match k, hk with
      | 0, _ => rfl
      | 1, hk1 =>
        exfalso
        have : (drpOfGraph adj).arcs.get ⟨1, hk1⟩ = (drpOfGraph adj).arcs.get i1 := rfl
        rw [this, g1] at he; simp at he
      | k + 2, hk2 =>
        exfalso
        have hk' : k < (Rone adj).length := by
          have := hk2; rw [hleq] at this; omega
        have hmem : (Rone adj)[k] ∈ Rone adj := List.getElem_mem hk'
        simp only [List.get_eq_getElem] at he
        rw [List.getElem_of_eq harcs] at he
        exact absurd (he.symm.trans (Rone_bit adj _ hmem)) (by decide)
    rw [he0]; simp
  · simp only [RPInstance.tourWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [show (drpOfGraph adj).arcs.get (i0, true).1 = _ from g0,
      show (drpOfGraph adj).arcs.get (i1, true).1 = _ from g1]
    simp [drpOfGraph]

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC
open SchedComplexity.NoWait (HasHamiltonCircuit dhpCode)

theorem dhc_red : PolyReducible dhcLang drpLang := by
  refine ⟨fD, fD_poly, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨n, adj, hhc, rfl⟩
    rw [dhpCode_eq]
    have hbs := length_matBits adj
    unfold fD; rw [decodeThen_code gD n (matBits adj) hbs]
    unfold gD
    have hsp : ¬ special n (matBits adj) := by
      rintro ⟨rfl, h⟩
      rw [matBits_one] at h
      have := (hc_one adj).1 hhc
      simp only [List.cons.injEq, and_true] at h
      rw [h] at this; cases this
    rw [if_neg hsp, ← rpCode_drp, adjOf_matBits]
    refine ⟨drpOfGraph adj, ?_, rfl⟩
    by_cases h1 : n = 1
    · subst h1; exact drp_one_yes adj
    · exact (claim_directed adj h1).1 hhc
  · rintro ⟨I, hI, hw⟩
    by_cases hv : ∃ n bs, bs.length = n * n ∧ w = code n bs
    · obtain ⟨n, bs, hbs, rfl⟩ := hv
      unfold fD at hw; rw [decodeThen_code gD n bs hbs] at hw
      unfold gD at hw
      split_ifs at hw with hsp
      · exact absurd hw.symm (rpCode_ne_nil I)
      · rw [← rpCode_drp] at hw
        have hII := rpCode_inj hw
        refine ⟨n, adjOf n bs, ?_, by rw [dhpCode_eq, matBits_adjOf n bs hbs]⟩
        by_cases h1 : n = 1
        · subst h1
          rw [hc_one]
          match bs, hbs with
          | [b], _ =>
            cases b
            · exact absurd ⟨rfl, rfl⟩ hsp
            · rfl
        · exact (claim_directed _ h1).2 (hII ▸ hI)
    · have hv' : ∀ n bs, bs.length = n * n → w ≠ code n bs := by
        intro n bs h1 h2; exact hv ⟨n, bs, h1, h2⟩
      unfold fD at hw; rw [decodeThen_invalid gD w hv'] at hw
      exact absurd hw.symm (rpCode_ne_nil I)

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC

/-! ## Undirected reduction: the check `n ≥ 3` -/

def n3check : Prog :=
  .seq (copyProg .N .X .sc) (.seq (popProg .X) (.seq (popProg .X)
    (.seq (.branch (fun h => (h .X).isNone) (pushProg .bad .one) skipP) (clearProg .X))))

lemma runs_n3check (n : ℕ) (bs : List Bool) :
    ∃ τ, Runs n3check (st6 n bs) τ (10 * n + 20) ∧ (3 ≤ n → τ = st6 n bs) ∧
      (n < 3 → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_copy .N .X .sc (by decide) (by decide) (by decide) (st6 n bs) rfl
  set σ1 := (st6 n bs).set .X ((st6 n bs).get .N ++ (st6 n bs).get .X) with hσ1
  have e2 := runs_pop .X σ1
  set σ2 := σ1.set .X (σ1.get .X).tail with hσ2
  have e3 := runs_pop .X σ2
  set σ3 := σ2.set .X (σ2.get .X).tail with hσ3
  have h3X : σ3.X = List.replicate (n - 2) .one := by
    simp [hσ3, hσ2, hσ1, st6, Regs.set, Regs.get, Regs.empty, List.tail_replicate]; rfl
  have l1 : ((st6 n bs).get .N).length = n := by simp [st6, Regs.get]
  by_cases hn : 3 ≤ n
  · have htest : (fun h : Key → Option BSym => (h .X).isNone) (hd σ3) = false := by
      obtain ⟨k, hk⟩ : ∃ k, n - 2 = k + 1 := ⟨n - 3, by omega⟩
      simp [hd, Regs.get, h3X, hk, List.replicate_succ]
    have e4 := (runs_skip σ3).brF (t := fun h : Key → Option BSym => (h .X).isNone)
      (p := pushProg .bad .one) htest
    have e5 := runs_clear .X σ3
    refine ⟨_, ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr ?_).mono ?_, fun _ => rfl,
      fun h => absurd hn (by omega)⟩
    · simp [Regs.set, hσ3, hσ2, hσ1, st6, Regs.empty]
    · rw [l1]; simp only [Regs.get, h3X, List.length_replicate]; omega
  · have htest : (fun h : Key → Option BSym => (h .X).isNone) (hd σ3) = true := by
      have : n - 2 = 0 := by omega
      simp [hd, Regs.get, h3X, this]
    have e4 := (runs_push .bad .one σ3).brT (t := fun h : Key → Option BSym => (h .X).isNone)
      (q := skipP) htest
    have e5 := runs_clear .X (σ3.set .bad (.one :: σ3.get .bad))
    refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_, fun h => absurd h hn, fun _ => ?_⟩
    · rw [l1]; simp only [Regs.get, Regs.set, h3X, List.length_replicate]; omega
    · simp [Regs.set, Regs.get, hσ3, hσ2, hσ1, st6, Regs.empty]

/-! ## the symmetry check -/

/-- some entry before position `k` (row-major) differs from its transpose -/
def symBad (bs : List Bool) (n k : ℕ) : Prop :=
  ∃ i < k, adjB bs n (i / n) (i % n) ≠ adjB bs n (i % n) (i / n)

instance (bs : List Bool) (n k : ℕ) : Decidable (symBad bs n k) := by
  unfold symBad; infer_instance

def flagL (bs : List Bool) (n k : ℕ) : List BSym := if symBad bs n k then [.one] else []

lemma symBad_succ (bs : List Bool) (n k : ℕ) :
    symBad bs n (k + 1) ↔ symBad bs n k ∨ adjB bs n (k / n) (k % n) ≠ adjB bs n (k % n) (k / n) := by
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hik : i < k
    · exact Or.inl ⟨i, hik, h⟩
    · have : i = k := by omega
      subst this; exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, by omega, h⟩
    · exact ⟨k, by omega, h⟩

def lookT : Prog := .seq (copyProg .M .T .sc) (.seq (copyProg .P .X .sc) (syncPopProg .T .X))
def lookT2 : Prog := .seq (copyProg .M .T2 .sc) (.seq (copyProg .Q .Y .sc) (syncPopProg .T2 .Y))
def cmpP : Prog :=
  .branch (fun h => decide (h .T ≠ h .T2) && (h .bad).isNone) (pushProg .bad .one) skipP

def symColBody : Prog :=
  .seq (popProg .C) (.seq lookT (.seq lookT2 (.seq cmpP (.seq (clearProg .T)
    (.seq (clearProg .T2) (.seq (pushProg .P .one) (copyProg .N .Q .sc)))))))

def symColLoop : Prog := .loop (fun h => (h .C).isSome) symColBody

def symRowBody : Prog :=
  .seq (popProg .R) (.seq (copyProg .Us .Q .sc) (.seq (copyProg .N .C .sc)
    (.seq symColLoop (.seq (clearProg .Q) (pushProg .Us .one)))))

def symRowLoop : Prog := .loop (fun h => (h .R).isSome) symRowBody

def symAll : Prog := .seq (copyProg .N .R .sc) (.seq symRowLoop (.seq (clearProg .Us) (clearProg .P)))

def symSt (n : ℕ) (bs : List Bool) (s t : ℕ) : Regs :=
  { st6 n bs with
    R := List.replicate (n - (s + 1)) .one
    Us := List.replicate s .one
    P := List.replicate (s * n + t) .one
    Q := List.replicate (t * n + s) .one
    C := List.replicate (n - t) .one
    bad := flagL bs n (s * n + t) }

def symRow (n : ℕ) (bs : List Bool) (s : ℕ) : Regs :=
  { st6 n bs with
    R := List.replicate (n - s) .one
    Us := List.replicate s .one
    P := List.replicate (s * n) .one
    bad := flagL bs n (s * n) }

lemma head_drop_enc (bs : List Bool) (k : ℕ) (hk : k < bs.length) :
    ((enc bs).drop k).head? = some (toB (bs.getD k false)) := by
  rw [show (enc bs).drop k = enc (bs.drop k) by simp [enc, List.map_drop], drop_eq_cons_getD bs k hk]
  rfl

lemma runs_lookT (σ : Regs) (hT : σ.T = []) (hX : σ.X = []) (hsc : σ.sc = [])
    (hk : σ.P.length ≤ σ.M.length) :
    Runs lookT σ { σ with T := σ.M.drop σ.P.length } (6 * σ.M.length + 9 * σ.P.length + 10) := by
  have e1 := runs_copy .M .T .sc (by decide) (by decide) (by decide) σ hsc
  have e2 := runs_copy .P .X .sc (by decide) (by decide) (by decide) (σ.set .T (σ.get .M ++ σ.get .T)) hsc
  have e3 := runs_syncpop .T .X (by decide)
    ((σ.set .T (σ.get .M ++ σ.get .T)).set .X ((σ.set .T (σ.get .M ++ σ.get .T)).get .P ++
      (σ.set .T (σ.get .M ++ σ.get .T)).get .X))
  have hm : min σ.M.length σ.P.length = σ.P.length := min_eq_right hk
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · simp [Regs.set, Regs.get, hT, hX, hm]
  · simp only [Regs.set, Regs.get, hT, hX, List.append_nil]; omega

lemma runs_lookT2 (σ : Regs) (hT : σ.T2 = []) (hY : σ.Y = []) (hsc : σ.sc = [])
    (hk : σ.Q.length ≤ σ.M.length) :
    Runs lookT2 σ { σ with T2 := σ.M.drop σ.Q.length } (6 * σ.M.length + 9 * σ.Q.length + 10) := by
  have e1 := runs_copy .M .T2 .sc (by decide) (by decide) (by decide) σ hsc
  have e2 := runs_copy .Q .Y .sc (by decide) (by decide) (by decide) (σ.set .T2 (σ.get .M ++ σ.get .T2)) hsc
  have e3 := runs_syncpop .T2 .Y (by decide)
    ((σ.set .T2 (σ.get .M ++ σ.get .T2)).set .Y ((σ.set .T2 (σ.get .M ++ σ.get .T2)).get .Q ++
      (σ.set .T2 (σ.get .M ++ σ.get .T2)).get .Y))
  have hm : min σ.M.length σ.Q.length = σ.Q.length := min_eq_right hk
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · simp [Regs.set, Regs.get, hT, hY, hm]
  · simp only [Regs.set, Regs.get, hT, hY, List.append_nil]; omega

lemma runs_cmpP (σ : Regs) (bs : List Bool) (n k : ℕ) (hb : σ.bad = flagL bs n k)
    (h1 : σ.T.head? = some (toB (adjB bs n (k / n) (k % n))))
    (h2 : σ.T2.head? = some (toB (adjB bs n (k % n) (k / n)))) :
    Runs cmpP σ { σ with bad := flagL bs n (k + 1) } 2 := by
  by_cases hk : symBad bs n k
  · have hk' : symBad bs n (k + 1) := (symBad_succ bs n k).2 (Or.inl hk)
    have hb' : σ.bad = [.one] := by rw [hb, flagL, if_pos hk]
    refine ((runs_skip σ).brF ?_).congr ?_
    · simp [hd, Regs.get, hb']
    · rw [flagL, if_pos hk', ← hb']
  · have hb' : σ.bad = [] := by rw [hb, flagL, if_neg hk]
    by_cases hm : adjB bs n (k / n) (k % n) ≠ adjB bs n (k % n) (k / n)
    · have hk' : symBad bs n (k + 1) := (symBad_succ bs n k).2 (Or.inr hm)
      refine ((runs_push .bad .one σ).brT ?_).congr ?_
      · simp only [hd, Regs.get, h1, h2, hb']
        have : toB (adjB bs n (k / n) (k % n)) ≠ toB (adjB bs n (k % n) (k / n)) := by
          revert hm; cases adjB bs n (k / n) (k % n) <;> cases adjB bs n (k % n) (k / n) <;> simp [toB]
        simp [this]
      · rw [flagL, if_pos hk']; simp [Regs.set, Regs.get, hb']
    · have hk' : ¬ symBad bs n (k + 1) := by
        rw [symBad_succ]; push Not; exact ⟨hk, by simpa using hm⟩
      refine ((runs_skip σ).brF ?_).congr ?_
      · simp only [hd, Regs.get, h1, h2, hb']
        have : adjB bs n (k / n) (k % n) = adjB bs n (k % n) (k / n) := by simpa using hm
        simp [this]
      · rw [flagL, if_neg hk', ← hb']

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC

lemma div_mod_aux (n s t : ℕ) (ht : t < n) : (s * n + t) / n = s ∧ (s * n + t) % n = t := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ht, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

lemma stepSym (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s t : ℕ) (hs : s < n) (ht : t < n) :
    Runs symColBody (symSt n bs s t) (symSt n bs s (t + 1)) (100 * (n * n + n + 1)) := by
  have hk : s * n + t < n * n := by nlinarith
  have hk' : t * n + s < n * n := by nlinarith
  obtain ⟨hd1, hm1⟩ := div_mod_aux n s t ht
  have e1 := runs_pop .C (symSt n bs s t)
  set σ1 := (symSt n bs s t).set .C ((symSt n bs s t).get .C).tail with hσ1
  have e2 := runs_lookT σ1 (by simp [hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ1, symSt, st6, Regs.set, Regs.empty]) (by simp [hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ1, symSt, st6, Regs.set, hbs]; omega)
  set σ2 := { σ1 with T := σ1.M.drop σ1.P.length } with hσ2
  have e3 := runs_lookT2 σ2 (by simp [hσ2, hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ2, hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ2, hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ2, hσ1, symSt, st6, Regs.set, hbs]; omega)
  set σ3 := { σ2 with T2 := σ2.M.drop σ2.Q.length } with hσ3
  have e4 := runs_cmpP σ3 bs n (s * n + t) (by simp [hσ3, hσ2, hσ1, symSt, Regs.set])
    (by
      simp only [hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, List.length_replicate, hd1, hm1]
      rw [head_drop_enc bs _ (by omega)]; rfl)
    (by
      simp only [hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, List.length_replicate, hd1, hm1]
      rw [head_drop_enc bs _ (by omega)]; rfl)
  set σ4 := { σ3 with bad := flagL bs n (s * n + t + 1) } with hσ4
  have e5 := runs_clear .T σ4
  have e6 := runs_clear .T2 (σ4.set .T [])
  have e7 := runs_push .P .one ((σ4.set .T []).set .T2 [])
  set σ7 := ((σ4.set .T []).set .T2 []).set .P (.one :: ((σ4.set .T []).set .T2 []).get .P) with hσ7
  have e8 := runs_copy .N .Q .sc (by decide) (by decide) (by decide) σ7
    (by simp [hσ7, hσ4, hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, Regs.empty])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).congr ?_).mono ?_
  · have hC : n - t - 1 = n - (t + 1) := by omega
    have hQ : n + (t * n + s) = (t + 1) * n + s := by ring
    have hP : List.replicate (s * n + (t + 1)) BSym.one = BSym.one :: List.replicate (s * n + t) BSym.one := by
      rw [← Nat.add_assoc, List.replicate_succ]
    simp [hP, hσ7, hσ4, hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, Regs.empty, List.tail_replicate,
      hC, List.replicate_append_replicate, hQ, List.replicate_succ, Nat.add_assoc]
  · simp only [hσ7, hσ4, hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, Regs.empty,
      List.length_replicate, List.length_drop, length_enc, hbs, List.length_tail]
    have h1 := hk; have h2 := hk'
    generalize s * n = a at *; generalize t * n = b at *; generalize n * n = c at *
    omega

lemma runs_symColLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs symColLoop (symSt n bs s 0) (symSt n bs s n) (n * (100 * (n * n + n + 1) + 2) + 1) := by
  refine Runs.loopU _ symColBody (symSt n bs s) _ _ (fun j hj => ⟨?_, stepSym n bs hbs s j hs hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, symSt, hk, List.replicate_succ]
  · simp [hd, Regs.get, symSt]

lemma stepSymRow (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs symRowBody (symRow n bs s) (symRow n bs (s + 1))
      (n * (100 * (n * n + n + 1) + 2) + 3 * n * n + 20 * n + 20) := by
  have e1 := runs_pop .R (symRow n bs s)
  set σ1 := (symRow n bs s).set .R ((symRow n bs s).get .R).tail with hσ1
  have e2 := runs_copy .Us .Q .sc (by decide) (by decide) (by decide) σ1
    (by simp [hσ1, symRow, st6, Regs.set, Regs.get, Regs.empty])
  set σ2 := σ1.set .Q (σ1.get .Us ++ σ1.get .Q) with hσ2
  have e3 := runs_copy .N .C .sc (by decide) (by decide) (by decide) σ2
    (by simp [hσ2, hσ1, symRow, st6, Regs.set, Regs.get, Regs.empty])
  have h0 : σ2.set .C (σ2.get .N ++ σ2.get .C) = symSt n bs s 0 := by
    have hR : n - s - 1 = n - (s + 1) := by omega
    simp [hσ2, hσ1, symRow, symSt, st6, Regs.set, Regs.get, Regs.empty, List.tail_replicate, hR]
  have e4 := runs_symColLoop n bs hbs s hs
  have e5 := runs_clear .Q (symSt n bs s n)
  have e6 := runs_push .Us .one ((symSt n bs s n).set .Q [])
  refine ((e1.seq (e2.seq ((e3.congr h0).seq (e4.seq (e5.seq e6))))).congr ?_).mono ?_
  · have hP : s * n + n = (s + 1) * n := by ring
    simp [symRow, symSt, st6, Regs.set, Regs.get, Regs.empty, hP, List.replicate_succ]
  · simp only [hσ2, hσ1, symRow, symSt, st6, Regs.set, Regs.get, Regs.empty,
      List.length_replicate, List.length_tail, List.length_append, List.length_nil]
    have : s ≤ n := by omega
    nlinarith

lemma runs_symAll (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs symAll (st6 n bs) { st6 n bs with bad := flagL bs n (n * n) } (400 * (n + 1) ^ 4) := by
  have e1 := runs_copy .N .R .sc (by decide) (by decide) (by decide) (st6 n bs) rfl
  have h0 : (st6 n bs).set .R ((st6 n bs).get .N ++ (st6 n bs).get .R) = symRow n bs 0 := by
    have : ¬ symBad bs n 0 := by rintro ⟨i, hi, _⟩; omega
    simp [symRow, st6, Regs.set, Regs.get, Regs.empty, flagL, this]
  have e2 : Runs symRowLoop (symRow n bs 0) (symRow n bs n)
      (n * (n * (100 * (n * n + n + 1) + 2) + 3 * n * n + 20 * n + 22) + 1) :=
    Runs.loopU _ symRowBody (symRow n bs) _ _ (fun j hj => ⟨by
      obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
      simp [hd, Regs.get, symRow, hk, List.replicate_succ], stepSymRow n bs hbs j hj⟩)
      (by simp [hd, Regs.get, symRow])
  have e3 := runs_clear .Us (symRow n bs n)
  have e4 := runs_clear .P ((symRow n bs n).set .Us [])
  refine (((e1.congr h0).seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · simp [symRow, st6, Regs.set, Regs.empty]
  · simp only [symRow, st6, Regs.set, Regs.get, Regs.empty, List.length_replicate]
    nlinarith [sq_nonneg (n + 1), pow_le_pow_left₀ (Nat.zero_le n) (Nat.le_succ n) 4]

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC

/-! ## Undirected generation, block A: the required arcs `⟨s,0⟩ — ⟨s,1⟩` -/

def blockAU (n i : ℕ) : List ℕ := (List.range i).flatMap (fun s => [s, n + s, 0, 1])

def itemsAU : List Item := [.inl .Cs, .inl .Cns, .inr false, .inr true]

def bodyAU : Prog :=
  .seq (popProg .R) (.seq (emitSeq itemsAU) (.seq (incProg .Cs .T) (incProg .Cns .T)))

def loopAU : Prog := .loop (fun h => (h .R).isSome) bodyAU

def gAU (n : ℕ) (bs : List Bool) (i : ℕ) : Regs :=
  { st6 n bs with
    R := List.replicate (n - i) .one
    Cs := enc (Nat.bits i)
    Cns := enc (Nat.bits (n + i))
    W := (encNats (blockAU n i)).reverse }

lemma gA_zero (n : ℕ) (bs : List Bool) : gA n bs 0 = gAU n bs 0 := by
  simp [gA, gAU, blockA, blockAU]

lemma stepAU (n : ℕ) (bs : List Bool) (i : ℕ) (hi : i < n) :
    Runs bodyAU (gAU n bs i) (gAU n bs (i + 1)) (100 * (2 * n + 1)) := by
  have e1 := runs_pop .R (gAU n bs i)
  set σ1 := (gAU n bs i).set .R ((gAU n bs i).get .R).tail with hσ1
  let ν : Key → ℕ := fun k => if k = .Cs then i else if k = .Cns then n + i else 0
  have hK : ∀ k, (Nat.bits (ν k)).length ≤ 2 * n := by
    intro k
    by_cases h1 : k = .Cs
    · simp only [ν, h1, if_true]; exact len_bits_le_of_le (by omega)
    · by_cases h2 : k = .Cns
      · simp only [ν, h2, if_true]; simp only [show (Key.Cns = Key.Cs) = False by decide, if_false]
        exact len_bits_le_of_le (by omega)
      · simp only [ν, h1, h2, if_false]; simp
  have e2 := runs_emitSeq ν (2 * n) hK itemsAU σ1 rfl rfl (by
    intro x hx
    simp only [itemsAU, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [itemOK, ν, hσ1, gAU, Regs.set, Regs.get])
  set σ2 := { σ1 with W := (encNats (itemsAU.map (itemVal ν))).reverse ++ σ1.W } with hσ2
  have e3 := runs_inc .Cs .T (by decide) σ2 (Nat.bits i) (by simp [hσ2, hσ1, gAU, Regs.set, Regs.get])
    (by simp [hσ2, hσ1, gAU, Regs.set, Regs.get, st6, Regs.empty])
  set σ3 := σ2.set .Cs (enc (incL (Nat.bits i))) with hσ3
  have e4 := runs_inc .Cns .T (by decide) σ3 (Nat.bits (n + i))
    (by simp [hσ3, hσ2, hσ1, gAU, Regs.set, Regs.get])
    (by simp [hσ3, hσ2, hσ1, gAU, Regs.set, Regs.get, st6, Regs.empty])
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · rw [hσ3]; simp only [incL_bits]
    have hR : n - i - 1 = n - (i + 1) := by omega
    simp [hσ2, hσ1, gAU, Regs.set, Regs.get, itemsAU, itemVal, ν, blockAU, List.range_succ,
      encNats_append', hR, Nat.add_assoc]
  · have h1 : (Nat.bits i).length ≤ 2 * n := len_bits_le_of_le (by omega)
    have h2 : (Nat.bits (n + i)).length ≤ 2 * n := len_bits_le_of_le (by omega)
    simp only [itemsAU, List.length_cons, List.length_nil]
    omega

lemma runs_loopAU (n : ℕ) (bs : List Bool) :
    Runs loopAU (gAU n bs 0) (gAU n bs n) (n * (100 * (2 * n + 1) + 2) + 1) := by
  refine Runs.loopU _ bodyAU (gAU n bs) _ _ (fun j hj => ⟨?_, stepAU n bs j hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, gAU, hk, List.replicate_succ]
  · simp [hd, Regs.get, gAU]

/-! ## block B: the edges `{s, t}` with `s < t` -/

def rowEU (bs : List Bool) (n s t : ℕ) : List (ℕ × ℕ) :=
  (List.range t).flatMap (fun t' => if decide (s < t') && adjB bs n s t' then [(s, t')] else [])

def allEU (bs : List Bool) (n s : ℕ) : List (ℕ × ℕ) :=
  (List.range s).flatMap (fun s' => rowEU bs n s' n)

def WofU (bs : List Bool) (n s t : ℕ) : List BSym :=
  (encNats (blockAU n n ++ (allEU bs n s ++ rowEU bs n s t).flatMap quad)).reverse

def gRU (n : ℕ) (bs : List Bool) (s : ℕ) : Regs :=
  { st6 n bs with
    W := WofU bs n s 0
    E := enc (Nat.bits (n + (allEU bs n s).length))
    B2 := enc (Nat.bits (2 * n))
    R := List.replicate (n - s) .one
    Cs := enc (Nat.bits s)
    M := enc (bs.drop (s * n))
    Us := List.replicate s .one }

def gCU (n : ℕ) (bs : List Bool) (s t : ℕ) : Regs :=
  { st6 n bs with
    W := WofU bs n s t
    E := enc (Nat.bits (n + (allEU bs n s).length + (rowEU bs n s t).length))
    B2 := enc (Nat.bits (2 * n))
    R := List.replicate (n - (s + 1)) .one
    Cs := enc (Nat.bits s)
    M := enc (bs.drop (s * n + t))
    C := List.replicate (n - t) .one
    Ct := enc (Nat.bits t)
    Us := List.replicate s .one
    D := List.replicate (s + 1 - t) .one }

def gu3 : Prog :=
  .seq (clearProg .Cs) (.seq (clearProg .Cns) (.seq (copyProg .Bn .E .sc)
    (.seq (copyProg .Bn .B2 .sc) (.seq (.branch (fun h => (h .B2).isSome) (pushProg .B2 .zero) skipP)
      (copyProg .N .R .sc)))))

lemma runs_gu3 (n : ℕ) (bs : List Bool) :
    Runs gu3 (gAU n bs n) (gRU n bs 0) (100 * (n + 1)) := by
  have e1 := runs_clear .Cs (gAU n bs n)
  have e2 := runs_clear .Cns ((gAU n bs n).set .Cs [])
  set σ2 := ((gAU n bs n).set .Cs []).set .Cns [] with hσ2
  have e3 := runs_copy .Bn .E .sc (by decide) (by decide) (by decide) σ2 rfl
  set σ3 := σ2.set .E (σ2.get .Bn ++ σ2.get .E) with hσ3
  have e4 := runs_copy .Bn .B2 .sc (by decide) (by decide) (by decide) σ3 rfl
  set σ4 := σ3.set .B2 (σ3.get .Bn ++ σ3.get .B2) with hσ4
  have h4 : σ4.get .B2 = enc (Nat.bits n) := by simp [hσ4, hσ3, hσ2, gAU, st6, Regs.set, Regs.get, Regs.empty]
  obtain ⟨σ5, e5, h5⟩ : ∃ σ5, Runs (.branch (fun h => (h .B2).isSome) (pushProg .B2 .zero) skipP) σ4 σ5 2 ∧
      σ5 = σ4.set .B2 (enc (Nat.bits (2 * n))) := by
    by_cases hn : n = 0
    · subst hn
      refine ⟨σ4, (runs_skip σ4).brF (by simp [hd, h4]), ?_⟩
      rw [show enc (Nat.bits (2 * 0)) = σ4.get .B2 by rw [h4], Regs.set_get]
    · refine ⟨_, (runs_push .B2 .zero σ4).brT ?_, ?_⟩
      · simp only [hd]; rw [h4]; exact isSome_head_of_ne_nil (enc_bits_ne_nil hn)
      · rw [enc_bits_double, if_neg hn, h4]
  have e6 := runs_copy .N .R .sc (by decide) (by decide) (by decide) σ5 (by rw [h5]; rfl)
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).congr ?_).mono ?_
  · rw [h5, hσ4, hσ3, hσ2]
    simp [gAU, gRU, st6, Regs.set, Regs.get, Regs.empty, WofU, allEU, rowEU, blockAU]
  · have l1 : ((gAU n bs n).get .Cs).length ≤ n := by simp [gAU, Regs.get]; exact len_bits_le n
    have l2 : (((gAU n bs n).set .Cs []).get .Cns).length ≤ 2 * n := by
      simp [gAU, Regs.get, Regs.set]; exact len_bits_le_of_le (by omega)
    have l3 : (σ2.get .Bn).length ≤ n := by simp [hσ2, gAU, st6, Regs.get, Regs.set]; exact len_bits_le n
    have l4 : (σ3.get .Bn).length ≤ n := by
      simp [hσ3, hσ2, gAU, st6, Regs.get, Regs.set]; exact len_bits_le n
    have l5 : (σ5.get .N).length = n := by simp [h5, hσ4, hσ3, hσ2, gAU, st6, Regs.get, Regs.set]
    omega

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC

def colBodyU : Prog :=
  .seq (popProg .C)
    (.seq (.branch (fun h => (h .D).isSome) (popProg .D)
      (.branch (fun h => decide (h .M = some .one)) (.seq (emitSeq itemsB) (incProg .E .T)) skipP))
      (.seq (popProg .M) (incProg .Ct .T)))

def colLoopU : Prog := .loop (fun h => (h .C).isSome) colBodyU

def rowBodyU : Prog :=
  .seq (popProg .R) (.seq (copyProg .N .C .sc) (.seq (copyProg .Us .D .sc) (.seq (pushProg .D .one)
    (.seq colLoopU (.seq (clearProg .Ct) (.seq (clearProg .D) (.seq (incProg .Cs .T) (pushProg .Us .one))))))))

def rowLoopU : Prog := .loop (fun h => (h .R).isSome) rowBodyU

lemma rowEU_succ (bs : List Bool) (n s t : ℕ) :
    rowEU bs n s (t + 1) = rowEU bs n s t ++
      (if decide (s < t) && adjB bs n s t then [(s, t)] else []) := by
  simp [rowEU, List.range_succ, List.flatMap_append]

lemma allEU_succ (bs : List Bool) (n s : ℕ) :
    allEU bs n (s + 1) = allEU bs n s ++ rowEU bs n s n := by
  simp [allEU, List.range_succ, List.flatMap_append]

lemma len_rowEU_le (bs : List Bool) (n s t : ℕ) : (rowEU bs n s t).length ≤ t := by
  induction t with
  | zero => simp [rowEU]
  | succ t ih => rw [rowEU_succ]; split_ifs <;> simp <;> omega

lemma len_allEU_le (bs : List Bool) (n s : ℕ) : (allEU bs n s).length ≤ s * n := by
  induction s with
  | zero => simp [allEU]
  | succ s ih => rw [allEU_succ, List.length_append]; have := len_rowEU_le bs n s n; nlinarith

lemma stepCU (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s t : ℕ) (hs : s < n) (ht : t < n) :
    Runs colBodyU (gCU n bs s t) (gCU n bs s (t + 1)) (200 * (n * n + 2 * n + 1)) := by
  have hk : s * n + t < bs.length := by rw [hbs]; nlinarith
  have hM : (gCU n bs s t).M = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := by
    simp only [gCU]; rw [drop_eq_cons_getD bs _ hk]; rfl
  have e1 := runs_pop .C (gCU n bs s t)
  set σ1 := (gCU n bs s t).set .C ((gCU n bs s t).get .C).tail with hσ1
  have hσ1M : σ1.M = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := hM
  have hσ1D : σ1.D = List.replicate (s + 1 - t) .one := rfl
  let ν : Key → ℕ := fun k => if k = .Cs then s else if k = .Ct then t else 0
  have hK : ∀ k, (Nat.bits (ν k)).length ≤ n := by
    intro k
    by_cases h1 : k = .Cs
    · simp only [ν, h1, if_true]; exact len_bits_le_of_le (by omega)
    · by_cases h2 : k = .Ct
      · simp only [ν, h2, if_true]; simp only [show (Key.Ct = Key.Cs) = False by decide, if_false]
        exact len_bits_le_of_le (by omega)
      · simp only [ν, h1, h2, if_false]; simp
  have hElen : (Nat.bits (n + (allEU bs n s).length + (rowEU bs n s t).length)).length ≤
      n * n + 2 * n := by
    apply len_bits_le_of_le
    have := len_allEU_le bs n s; have := len_rowEU_le bs n s t
    have : s * n + t ≤ n * n := by nlinarith
    omega
  obtain ⟨σ2, e2, hσ2⟩ : ∃ σ2, Runs (.branch (fun h => (h .D).isSome) (popProg .D)
      (.branch (fun h => decide (h .M = some .one)) (.seq (emitSeq itemsB) (incProg .E .T)) skipP))
      σ1 σ2 (100 * (n * n + 2 * n + 1)) ∧
      σ2 = { σ1 with
        W := (encNats ((if decide (s < t) && adjB bs n s t then [(s, t)] else []).flatMap quad)).reverse ++ σ1.W
        E := enc (Nat.bits (n + (allEU bs n s).length + (rowEU bs n s (t + 1)).length))
        D := List.replicate (s + 1 - (t + 1)) .one } := by
    by_cases hst : t ≤ s
    · have hD : s + 1 - t = (s - t) + 1 := by omega
      refine ⟨_, ((runs_pop .D σ1).brT ?_).mono (by omega), ?_⟩
      · simp [hd, Regs.get, hσ1D, hD, List.replicate_succ]
      · have hlt : ¬ s < t := by omega
        rw [rowEU_succ]
        simp [hσ1, gCU, Regs.set, Regs.get, hlt, encNats, hD, List.replicate_succ,
          show s + 1 - (t + 1) = s - t by omega]
    · have hD : s + 1 - t = 0 := by omega
      have hD' : s + 1 - (t + 1) = 0 := by omega
      have hlt : s < t := by omega
      have hDt : (fun h : Key → Option BSym => (h .D).isSome) (hd σ1) = false := by
        simp [hd, Regs.get, hσ1D, hD]
      cases hadj : adjB bs n s t
      · refine ⟨σ1, (((runs_skip σ1).brF ?_).brF hDt).mono (by omega), ?_⟩
        · simp [hd, Regs.get, hσ1M, hadj, toB]
        · rw [rowEU_succ, hadj]; simp [hσ1, gCU, Regs.set, Regs.get, encNats, hD, hD']
      · have e21 := runs_emitSeq ν n hK itemsB σ1 rfl rfl (by
          intro x hx
          simp only [itemsB, List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> simp [itemOK, ν, hσ1, gCU, Regs.set, Regs.get])
        set σ21 := { σ1 with W := (encNats (itemsB.map (itemVal ν))).reverse ++ σ1.W } with hσ21
        have e22 := runs_inc .E .T (by decide) σ21 _ (by simp [hσ21, hσ1, gCU, Regs.set, Regs.get]; rfl)
          (by simp [hσ21, hσ1, gCU, Regs.set, Regs.get, st6, Regs.empty])
        refine ⟨_, (((e21.seq e22).brT ?_).brF hDt).mono ?_, ?_⟩
        · simp [hd, Regs.get, hσ1M, hadj, toB]
        · simp only [itemsB, List.length_cons, List.length_nil]; nlinarith
        · rw [incL_bits, rowEU_succ, hadj]
          simp [hσ21, hσ1, gCU, Regs.set, Regs.get, itemsB, itemVal, ν, quad, Nat.add_assoc, hlt, hD, hD']
  have e3 := runs_pop .M σ2
  set σ3 := σ2.set .M (σ2.get .M).tail with hσ3
  have e4 := runs_inc .Ct .T (by decide) σ3 (Nat.bits t) (by simp [hσ3, hσ2, hσ1, gCU, Regs.set, Regs.get])
    (by simp [hσ3, hσ2, hσ1, gCU, Regs.set, Regs.get, st6, Regs.empty])
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · rw [incL_bits]
    have hC : n - t - 1 = n - (t + 1) := by omega
    rw [hσ3, hσ2]
    simp only [Regs.set, Regs.get, hσ1M]
    simp [hσ1, gCU, Regs.set, Regs.get, WofU, hC, List.flatMap_append, encNats_append', rowEU_succ,
      Nat.add_assoc]
  · have : (Nat.bits t).length ≤ n := len_bits_le_of_le (by omega)
    nlinarith

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC

lemma runs_colLoopU (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs colLoopU (gCU n bs s 0) (gCU n bs s n) (n * (200 * (n * n + 2 * n + 1) + 2) + 1) := by
  refine Runs.loopU _ colBodyU (gCU n bs s) _ _ (fun j hj => ⟨?_, stepCU n bs hbs s j hs hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, gCU, hk, List.replicate_succ]
  · simp [hd, Regs.get, gCU]

lemma stepRU (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs rowBodyU (gRU n bs s) (gRU n bs (s + 1)) (n * (200 * (n * n + 2 * n + 1) + 2) + 40 * n + 40) := by
  have e1 := runs_pop .R (gRU n bs s)
  set σ1 := (gRU n bs s).set .R ((gRU n bs s).get .R).tail with hσ1
  have e2 := runs_copy .N .C .sc (by decide) (by decide) (by decide) σ1 rfl
  set σ2 := σ1.set .C (σ1.get .N ++ σ1.get .C) with hσ2
  have e3 := runs_copy .Us .D .sc (by decide) (by decide) (by decide) σ2 rfl
  set σ3 := σ2.set .D (σ2.get .Us ++ σ2.get .D) with hσ3
  have e4 := runs_push .D .one σ3
  have h0 : σ3.set .D (.one :: σ3.get .D) = gCU n bs s 0 := by
    have hR : n - s - 1 = n - (s + 1) := by omega
    simp [hσ3, hσ2, hσ1, gRU, gCU, st6, Regs.set, Regs.get, Regs.empty, rowEU, WofU, hR,
      List.tail_replicate, List.replicate_succ]
  have e5 := runs_colLoopU n bs hbs s hs
  have e6 := runs_clear .Ct (gCU n bs s n)
  have e7 := runs_clear .D ((gCU n bs s n).set .Ct [])
  have e8 := runs_inc .Cs .T (by decide) (((gCU n bs s n).set .Ct []).set .D []) (Nat.bits s)
    (by simp [gCU, Regs.set, Regs.get]) (by simp [gCU, Regs.set, Regs.get, st6, Regs.empty])
  have e9 := runs_push .Us .one ((((gCU n bs s n).set .Ct []).set .D []).set .Cs (enc (incL (Nat.bits s))))
  refine ((e1.seq (e2.seq (e3.seq ((e4.congr h0).seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))).congr ?_).mono ?_
  · rw [incL_bits]
    simp [gRU, gCU, st6, Regs.set, Regs.get, Regs.empty, WofU, allEU_succ, rowEU, Nat.succ_mul,
      Nat.add_assoc, List.replicate_succ]
  · have l1 : (σ1.get .N).length = n := by simp [hσ1, gRU, st6, Regs.get, Regs.set]
    have l2 : (σ2.get .Us).length = s := by simp [hσ2, hσ1, gRU, st6, Regs.get, Regs.set]
    have l3 : ((gCU n bs s n).get .Ct).length ≤ n := by
      simp [gCU, Regs.get]; exact len_bits_le n
    have l4 : (((gCU n bs s n).set .Ct []).get .D).length ≤ n := by
      simp [gCU, Regs.get, Regs.set]; omega
    have l5 : (Nat.bits s).length ≤ n := len_bits_le_of_le (by omega)
    rw [l1, l2]
    omega

lemma runs_rowLoopU (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs rowLoopU (gRU n bs 0) (gRU n bs n)
      (n * (n * (200 * (n * n + 2 * n + 1) + 2) + 40 * n + 42) + 1) := by
  refine Runs.loopU _ rowBodyU (gRU n bs) _ _ (fun j hj => ⟨?_, stepRU n bs hbs j hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, gRU, hk, List.replicate_succ]
  · simp [hd, Regs.get, gRU]

def outListU (n : ℕ) (bs : List Bool) : List ℕ :=
  [2 * n, n + (allEU bs n n).length] ++ blockAU n n ++ (allEU bs n n).flatMap quad ++ [n]

lemma runs_asmU (n : ℕ) (bs : List Bool) (L : ℕ) (hL : (WofU bs n n 0).length ≤ L) (hn : 2 * n ≤ L)
    (hE : (Nat.bits (n + (allEU bs n n).length)).length ≤ L) :
    ∃ τ, Runs asm (gRU n bs n) τ (30 * L + 30) ∧ τ.out = encNats (outListU n bs) := by
  have e1 := runs_push .out .sep (gRU n bs n)
  set σ1 := (gRU n bs n).set .out (.sep :: (gRU n bs n).get .out) with hσ1
  have e2 := runs_copy .Bn .out .sc (by decide) (by decide) (by decide) σ1 rfl
  set σ2 := σ1.set .out (σ1.get .Bn ++ σ1.get .out) with hσ2
  have e3 := runs_mv .W .out (by decide) σ2
  set σ3 := (σ2.set .W []).set .out ((σ2.get .W).reverse ++ σ2.get .out) with hσ3
  have e4 := runs_push .out .sep σ3
  set σ4 := σ3.set .out (.sep :: σ3.get .out) with hσ4
  have e5 := runs_copy .E .out .sc (by decide) (by decide) (by decide) σ4 rfl
  set σ5 := σ4.set .out (σ4.get .E ++ σ4.get .out) with hσ5
  have e6 := runs_push .out .sep σ5
  set σ6 := σ5.set .out (.sep :: σ5.get .out) with hσ6
  have e7 := runs_copy .B2 .out .sc (by decide) (by decide) (by decide) σ6 rfl
  refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).mono ?_, ?_⟩
  · have l2 : (σ1.get .Bn).length ≤ L := by
      simp [hσ1, gRU, st6, Regs.get, Regs.set]; exact le_trans (len_bits_le n) (by omega)
    have l3 : (σ2.get .W).length ≤ L := by simp [hσ2, hσ1, gRU, Regs.get, Regs.set]; exact hL
    have l5 : (σ4.get .E).length ≤ L := by
      simp [hσ4, hσ3, hσ2, hσ1, gRU, Regs.get, Regs.set]; exact hE
    have l7 : (σ6.get .B2).length ≤ L := by
      simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, gRU, Regs.get, Regs.set]
      exact le_trans (len_bits_le _) hn
    omega
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, gRU, st6, Regs.get, Regs.set, Regs.empty, WofU, outListU,
      encNats_append', encNats_cons', encNat_eq', rowEU, encNats]

lemma mem_blockAU (n x : ℕ) (hx : x ∈ blockAU n n) : x ≤ 2 * n := by
  simp only [blockAU, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at hx
  obtain ⟨s, hs, h⟩ := hx
  rcases h with rfl | rfl | rfl | rfl <;> omega

lemma mem_rowEU (bs : List Bool) (n s t : ℕ) (p : ℕ × ℕ) (hp : p ∈ rowEU bs n s t) :
    p.1 = s ∧ p.2 < t := by
  simp only [rowEU, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨t', ht', h⟩ := hp
  split_ifs at h
  · simp at h; subst h; exact ⟨rfl, ht'⟩
  · simp at h

lemma mem_allEU (bs : List Bool) (n s : ℕ) (p : ℕ × ℕ) (hp : p ∈ allEU bs n s) :
    p.1 < s ∧ p.2 < n := by
  simp only [allEU, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨s', hs', h⟩ := hp
  obtain ⟨h1, h2⟩ := mem_rowEU bs n s' n p h
  exact ⟨h1 ▸ hs', h2⟩

lemma len_WofU (bs : List Bool) (n : ℕ) :
    (WofU bs n n 0).length ≤ (4 * n + 4 * (n * n)) * (2 * n + 1) := by
  unfold WofU
  rw [List.length_reverse]
  have hmem : ∀ x ∈ blockAU n n ++ (allEU bs n n ++ rowEU bs n n 0).flatMap quad, x ≤ 2 * n := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact mem_blockAU n x h
    · simp only [rowEU, List.range_zero, List.flatMap_nil, List.append_nil, List.mem_flatMap] at h
      obtain ⟨p, hp, hx⟩ := h
      have := mem_allEU bs n n p hp
      simp only [quad, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> omega
  refine le_trans (length_encNats_le _ _ hmem) (Nat.mul_le_mul_right _ ?_)
  have h1 : (blockAU n n).length = 4 * n := by
    simp [blockAU, List.length_flatMap, List.sum_replicate, List.map_const', Nat.mul_comm]
  have h2 : ((allEU bs n n ++ rowEU bs n n 0).flatMap quad).length = 4 * (allEU bs n n).length := by
    simp [rowEU, quad, List.length_flatMap, List.sum_replicate, List.map_const', Nat.mul_comm]
  have h3 := len_allEU_le bs n n
  rw [List.length_append, h1, h2]; omega

lemma runs_genU_body (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (L : ℕ) (hL : n * n ≤ L)
    (hnL : n ≤ L) :
    ∃ τ, Runs (.seq gd1 (.seq loopAU (.seq gu3 (.seq rowLoopU asm)))) (st6 n bs) τ (4000 * (L + 1) ^ 2) ∧
      τ.out = encNats (outListU n bs) := by
  have e1 := (runs_gd1 n bs).congr (gA_zero n bs)
  have e2 := runs_loopAU n bs
  have e3 := runs_gu3 n bs
  have e4 := runs_rowLoopU n bs hbs
  have hW := len_WofU bs n
  have hE : (Nat.bits (n + (allEU bs n n).length)).length ≤ 3 * L := by
    apply len_bits_le_of_le; have := len_allEU_le bs n n; omega
  have hW' : (WofU bs n n 0).length ≤ 36 * (L + 1) ^ 2 := by
    have : n * n * n ≤ L * L := by nlinarith
    nlinarith
  obtain ⟨τ, e5, h5⟩ := runs_asmU n bs (36 * (L + 1) ^ 2) hW' (by nlinarith) (by nlinarith)
  refine ⟨τ, (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_, h5⟩
  have a1 : n * (n * n) ≤ L * L := by nlinarith
  have a2 : n * n * (n * n) ≤ L * L := Nat.mul_le_mul hL hL
  nlinarith

end RPPRed


set_option autoImplicit false

namespace RPPRed

open CookPvsNP ProjSchedTW.Complexity RuralPostman.NPC
open SchedComplexity.NoWait (HasHamiltonCircuit dhpCode)

/-! ## the whole undirected reduction -/

def genU : Prog :=
  .seq n3check (gate (.seq symAll (gate (.seq gd1 (.seq loopAU (.seq gu3 (.seq rowLoopU asm)))))))

def mainU : Prog := .seq parseProg (gate genU)

def gU (n : ℕ) (bs : List Bool) : List BSym :=
  if 3 ≤ n ∧ ¬ symBad bs n (n * n) then encNats (outListU n bs) else []

noncomputable def fU : List BSym → List BSym := decodeThen gU

theorem mainU_spec (w : List BSym) :
    ∃ τ, Runs mainU (initR w) τ (12000 * (w.length + 1) ^ 2) ∧ τ.out = fU w := by
  obtain ⟨τ, e, h⟩ := parse_spec w
  have hpos : (w.length + 1) ^ 2 ≥ w.length + 1 := by nlinarith
  rcases h with ⟨n, bs, hbs, hw, hτ⟩ | ⟨hb, ho, hinv⟩
  · subst hτ
    have hbL : bs.length ≤ w.length := hw ▸ length_code n bs
    have hL : n * n ≤ w.length := hbs ▸ hbL
    have hnL : n ≤ w.length := le_trans (n_le_of_sq hbs) hbL
    have hfw : fU w = gU n bs := by rw [fU, hw, decodeThen_code gU n bs hbs]
    obtain ⟨τ3, e3, h3a, h3b⟩ := runs_n3check n bs
    by_cases hn3 : 3 ≤ n
    · have hτ3 := h3a hn3
      subst hτ3
      have es := runs_symAll n bs hbs
      have hsq : (n + 1) ^ 4 ≤ 16 * (w.length + 1) ^ 2 := by
        have h1 : (n + 1) ^ 2 ≤ 4 * (w.length + 1) := by nlinarith
        have h2 : (n + 1) ^ 4 = ((n + 1) ^ 2) ^ 2 := by ring
        rw [h2]; nlinarith
      by_cases hsb : symBad bs n (n * n)
      · have hb' : ({ st6 n bs with bad := flagL bs n (n * n) } : Regs).bad ≠ [] := by
          simp [flagL, hsb]
        refine ⟨_, (e.seq (runs_gate_ok rfl (e3.seq (runs_gate_ok rfl (es.seq
          (runs_gate_skip hb')))))).mono ?_, ?_⟩
        · nlinarith
        · rw [hfw, gU, if_neg (fun h => h.2 hsb)]; rfl
      · have hσ : ({ st6 n bs with bad := flagL bs n (n * n) } : Regs) = st6 n bs := by
          simp [flagL, hsb, st6, Regs.empty]
        rw [hσ] at es
        obtain ⟨τ1, e1, h1⟩ := runs_genU_body n bs hbs w.length hL hnL
        refine ⟨τ1, (e.seq (runs_gate_ok rfl (e3.seq (runs_gate_ok rfl (es.seq
          (runs_gate_ok rfl e1)))))).mono ?_, ?_⟩
        · nlinarith
        · rw [h1, hfw, gU, if_pos ⟨hn3, hsb⟩]
    · obtain ⟨hb3, ho3⟩ := h3b (by omega)
      refine ⟨τ3, (e.seq (runs_gate_ok rfl (e3.seq (runs_gate_skip hb3)))).mono ?_, ?_⟩
      · nlinarith
      · rw [ho3, hfw, gU, if_neg (fun h => hn3 h.1)]
  · refine ⟨τ, (e.seq (runs_gate_skip hb)).mono ?_, ?_⟩
    · nlinarith
    · rw [ho, fU, decodeThen_invalid gU w hinv]

theorem fU_poly : PolyTimeComputable fU := by
  obtain ⟨k, hk⟩ := polynomial_absorb 12000 2 0
  refine stack_program_polytime mainU .inp .out fU k (fun w => ?_)
  obtain ⟨τ, ⟨m, hm, ex⟩, ho⟩ := mainU_spec w
  refine ⟨τ.get, m, le_trans hm (by have := hk w.length; omega), ?_, ho⟩
  rw [← initR_get]; exact ex

/-! ## the code of the undirected instance -/

lemma symBad_iff (n : ℕ) (bs : List Bool) :
    symBad bs n (n * n) ↔ ¬ IsSymm (adjOf n bs) := by
  constructor
  · rintro ⟨i, hi, h⟩ hs
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    have := hs ⟨i / n, Nat.div_lt_of_lt_mul hi⟩ ⟨i % n, Nat.mod_lt _ hn⟩
    exact h this
  · intro hs
    simp only [IsSymm, not_forall] at hs
    obtain ⟨u, v, huv⟩ := hs
    obtain ⟨h1, h2⟩ := div_mod_aux n u.val v.val v.isLt
    refine ⟨u.val * n + v.val, by have := u.isLt; have := v.isLt; nlinarith, ?_⟩
    rw [h1, h2]; exact huv

lemma urp_flat1 (n : ℕ) :
    ((List.finRange n).map (fun s : Fin n =>
      ((Fin.castAdd n s : Fin (n + n)), (Fin.natAdd n s : Fin (n + n)), (0 : ℕ), true))).flatMap arcFlat =
      blockAU n n := by
  rw [List.flatMap_map]
  unfold blockAU
  apply finRange_flatMap'
  intro s
  simp [arcFlat, Nat.add_comm]

lemma urp_flat2 (n : ℕ) (bs : List Bool) :
    ((List.finRange n).flatMap (fun s : Fin n =>
      ((List.finRange n).filter (fun t => decide (s < t) && adjOf n bs s t)).map
        (fun t => ((Fin.castAdd n s : Fin (n + n)), (Fin.castAdd n t : Fin (n + n)), (1 : ℕ), false)))).flatMap arcFlat =
      (allEU bs n n).flatMap quad := by
  rw [List.flatMap_assoc]
  unfold allEU rowEU
  rw [List.flatMap_assoc]
  apply finRange_flatMap'
  intro s
  rw [List.flatMap_map, flatMap_filter_map, List.flatMap_assoc]
  apply finRange_flatMap'
  intro t
  simp only [adjOf, Fin.lt_def]
  split_ifs with h <;> simp_all [arcFlat, quad]

lemma rpCode_urp (n : ℕ) (bs : List Bool) :
    rpCode (urpOfGraph (adjOf n bs)) = encNats (outListU n bs) := by
  rw [rpCode_eq']
  have hflat : (urpOfGraph (adjOf n bs)).arcs.flatMap arcFlat = blockAU n n ++ (allEU bs n n).flatMap quad := by
    simp only [urpOfGraph]
    rw [List.flatMap_append, urp_flat1, urp_flat2]
  have hlen : (urpOfGraph (adjOf n bs)).arcs.length = n + (allEU bs n n).length := by
    have h4 : ∀ {m : ℕ} (l : List (Fin m × Fin m × ℕ × Bool)), (l.flatMap arcFlat).length = 4 * l.length := by
      intro m l; induction l with
      | nil => simp
      | cons a l ih => simp [arcFlat, ih]; ring
    have hq : ∀ l : List (ℕ × ℕ), (l.flatMap quad).length = 4 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp [quad, ih]; ring
    have hb : (blockAU n n).length = 4 * n := by
      simp [blockAU, List.length_flatMap, List.sum_replicate, List.map_const', Nat.mul_comm]
    have := congrArg List.length hflat
    rw [h4, List.length_append, hb, hq] at this
    omega
  rw [hflat, hlen]
  simp only [outListU, urpOfGraph]
  congr 1
  simp [two_mul, List.append_assoc]

theorem uhc_red : PolyReducible uhcLang urpLang := by
  refine ⟨fU, fU_poly, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨n, adj, hsym, h3, hhc, rfl⟩
    rw [dhpCode_eq]
    have hbs := length_matBits adj
    unfold fU; rw [decodeThen_code gU n (matBits adj) hbs]
    unfold gU
    have hsb : ¬ symBad (matBits adj) n (n * n) := by
      rw [symBad_iff, adjOf_matBits]; exact not_not.2 hsym
    rw [if_pos ⟨h3, hsb⟩, ← rpCode_urp, adjOf_matBits]
    exact ⟨urpOfGraph adj, (claim_undirected adj hsym h3).1 hhc, rfl⟩
  · rintro ⟨I, hI, hw⟩
    by_cases hv : ∃ n bs, bs.length = n * n ∧ w = code n bs
    · obtain ⟨n, bs, hbs, rfl⟩ := hv
      unfold fU at hw; rw [decodeThen_code gU n bs hbs] at hw
      unfold gU at hw
      split_ifs at hw with hc
      · rw [← rpCode_urp] at hw
        have hII := rpCode_inj hw
        have hsym : IsSymm (adjOf n bs) := by
          have := hc.2; rw [symBad_iff, not_not] at this; exact this
        refine ⟨n, adjOf n bs, hsym, hc.1, ?_, by rw [dhpCode_eq, matBits_adjOf n bs hbs]⟩
        exact (claim_undirected _ hsym hc.1).2 (hII ▸ hI)
      · exact absurd hw.symm (rpCode_ne_nil I)
    · have hv' : ∀ n bs, bs.length = n * n → w ≠ code n bs := by
        intro n bs h1 h2; exact hv ⟨n, bs, h1, h2⟩
      unfold fU at hw; rw [decodeThen_invalid gU w hv'] at hw
      exact absurd hw.symm (rpCode_ne_nil I)

end RPPRed

theorem solution : CookPvsNP.PolyReducible RuralPostman.NPC.uhcLang RuralPostman.NPC.urpLang :=
  RPPRed.uhc_red
