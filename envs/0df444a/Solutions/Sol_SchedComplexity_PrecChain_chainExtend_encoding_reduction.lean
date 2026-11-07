-- Prove2me | solution 1 for SchedComplexity.PrecChain.chainExtend_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T21:52:29.57292+00:00
-- url     : https://prove2.me/submissions/39652628-85e1-476f-b54e-7e339722ca40

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackRepeat
import Definitions.Def_CookPvsNP_StackCompare
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Definitions.Def_SchedComplexity_PrecChain_Languages
import Definitions.Def_SchedComplexity_PrecChain_Construction
import Theorems.Thm_SchedComplexity_PrecChain_cmax_le_n_pstar
import Theorems.Thm_SchedComplexity_PrecChain_cmax_le_imp_sumC_le

set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity


inductive Key
  | inp | out | bad | I2 | A | Tu | Bn | F | Nu | Q | C | C2 | C3 | sc | T | rv | Yb | G | Yu | Ku | NN | Yv | A2 | Z | O | Bc
  deriving DecidableEq

instance : Fintype Key :=
  ⟨⟨([.inp, .out, .bad, .I2, .A, .Tu, .Bn, .F, .Nu, .Q, .C, .C2, .C3, .sc, .T, .rv, .Yb, .G, .Yu, .Ku, .NN, .Yv, .A2, .Z, .O, .Bc] : List Key), by decide⟩, by intro x; cases x <;> decide⟩

structure Regs where
  inp : List BSym
  out : List BSym
  bad : List BSym
  I2 : List BSym
  A : List BSym
  Tu : List BSym
  Bn : List BSym
  F : List BSym
  Nu : List BSym
  Q : List BSym
  C : List BSym
  C2 : List BSym
  C3 : List BSym
  sc : List BSym
  T : List BSym
  rv : List BSym
  Yb : List BSym
  G : List BSym
  Yu : List BSym
  Ku : List BSym
  NN : List BSym
  Yv : List BSym
  A2 : List BSym
  Z : List BSym
  O : List BSym
  Bc : List BSym

namespace Regs

def get (σ : Regs) : Key → List BSym
  | .inp => σ.inp
  | .out => σ.out
  | .bad => σ.bad
  | .I2 => σ.I2
  | .A => σ.A
  | .Tu => σ.Tu
  | .Bn => σ.Bn
  | .F => σ.F
  | .Nu => σ.Nu
  | .Q => σ.Q
  | .C => σ.C
  | .C2 => σ.C2
  | .C3 => σ.C3
  | .sc => σ.sc
  | .T => σ.T
  | .rv => σ.rv
  | .Yb => σ.Yb
  | .G => σ.G
  | .Yu => σ.Yu
  | .Ku => σ.Ku
  | .NN => σ.NN
  | .Yv => σ.Yv
  | .A2 => σ.A2
  | .Z => σ.Z
  | .O => σ.O
  | .Bc => σ.Bc

def set (σ : Regs) : Key → List BSym → Regs
  | .inp, l => { σ with inp := l }
  | .out, l => { σ with out := l }
  | .bad, l => { σ with bad := l }
  | .I2, l => { σ with I2 := l }
  | .A, l => { σ with A := l }
  | .Tu, l => { σ with Tu := l }
  | .Bn, l => { σ with Bn := l }
  | .F, l => { σ with F := l }
  | .Nu, l => { σ with Nu := l }
  | .Q, l => { σ with Q := l }
  | .C, l => { σ with C := l }
  | .C2, l => { σ with C2 := l }
  | .C3, l => { σ with C3 := l }
  | .sc, l => { σ with sc := l }
  | .T, l => { σ with T := l }
  | .rv, l => { σ with rv := l }
  | .Yb, l => { σ with Yb := l }
  | .G, l => { σ with G := l }
  | .Yu, l => { σ with Yu := l }
  | .Ku, l => { σ with Ku := l }
  | .NN, l => { σ with NN := l }
  | .Yv, l => { σ with Yv := l }
  | .A2, l => { σ with A2 := l }
  | .Z, l => { σ with Z := l }
  | .O, l => { σ with O := l }
  | .Bc, l => { σ with Bc := l }

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
  exact ⟨congrFun h .inp, congrFun h .out, congrFun h .bad, congrFun h .I2, congrFun h .A, congrFun h .Tu, congrFun h .Bn, congrFun h .F, congrFun h .Nu, congrFun h .Q, congrFun h .C, congrFun h .C2, congrFun h .C3, congrFun h .sc, congrFun h .T, congrFun h .rv, congrFun h .Yb, congrFun h .G, congrFun h .Yu, congrFun h .Ku, congrFun h .NN, congrFun h .Yv, congrFun h .A2, congrFun h .Z, congrFun h .O, congrFun h .Bc⟩

lemma set_set (σ : Regs) (k : Key) (u v : List BSym) : (σ.set k u).set k v = σ.set k v := by
  apply ext_get; funext j; simp only [get_set]; split_ifs <;> rfl

lemma set_comm (σ : Regs) {k j : Key} (h : k ≠ j) (u v : List BSym) :
    (σ.set k u).set j v = (σ.set j v).set k u := by
  apply ext_get; funext i; simp only [get_set]
  split_ifs with h1 h2 <;> first | rfl | (subst h1; subst h2; exact absurd rfl h)

lemma set_get (σ : Regs) (k : Key) : σ.set k (σ.get k) = σ := by
  apply ext_get; funext j; simp only [get_set]; split_ifs with h <;> first | rfl | (subst h; rfl)

end Regs

def Regs.empty : Regs :=
  ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩


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



variable (m : List BSym)

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



def gate (p : Prog) : Prog := .branch (fun h => (h .bad).isNone) p skipP

lemma runs_gate_ok {p : Prog} {σ τ : Regs} {B : ℕ} (hb : σ.bad = []) (h : Runs p σ τ B) :
    Runs (gate p) σ τ (B + 1) :=
  Runs.brT (by simp [hd, Regs.get, hb]) h

lemma runs_gate_skip {p : Prog} {σ : Regs} (hb : σ.bad ≠ []) : Runs (gate p) σ σ 2 :=
  Runs.brF (by
    cases h : σ.bad with
    | nil => exact absurd h hb
    | cons a l => simp [hd, Regs.get, h]) (runs_skip σ)
def isDigB : BSym → Bool
  | .one => true
  | .zero => true
  | _ => false
def digs (w : List BSym) : List BSym := w.takeWhile isDigB
def rest (w : List BSym) : List BSym := w.dropWhile isDigB

/-- the check of phase 2 -/
def numOK (w : List BSym) : Prop :=
  (rest w).head? = some .sep ∧ (digs w).getLast? ≠ some .zero

instance (w : List BSym) : Decidable (numOK w) := by unfold numOK; infer_instance
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

lemma numOK_code (n : ℕ) (r : List BSym) : numOK (enc (Nat.bits n) ++ BSym.sep :: r) := by
  unfold numOK
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

/-! ## pushing constant blocks -/

def pushL (k : Key) : List BSym → Prog
  | [] => skipP
  | a :: l => .seq (pushProg k a) (pushL k l)

lemma runs_pushL (k : Key) : ∀ (l : List BSym) (σ : Regs),
    Runs (pushL k l) σ (σ.set k (l.reverse ++ σ.get k)) (2 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro σ
    simp only [pushL, List.reverse_nil, List.nil_append, Regs.set_get, List.length_nil]
    exact runs_skip σ
  | cons a l ih =>
    intro σ
    have e1 := runs_push k a σ
    have e2 := ih (σ.set k (a :: σ.get k))
    refine ((e1.seq e2).congr ?_).mono ?_
    · simp [Regs.set_set]
    · simp; omega

def constLoop (R W : Key) (l : List BSym) : Prog :=
  .loop (fun h => (h R).isSome) (.seq (popProg R) (pushL W l))

lemma runs_constLoop (R W : Key) (hRW : R ≠ W) (l : List BSym) : ∀ (c : ℕ) (σ : Regs),
    σ.get R = List.replicate c .one →
    Runs (constLoop R W l) σ ((σ.set R []).set W ((List.replicate c l).flatten.reverse ++ σ.get W))
      (c * (2 * l.length + 6) + 1) := by
  intro c
  induction c with
  | zero =>
    intro σ hR
    simp only [List.replicate_zero, List.flatten_nil, List.reverse_nil, List.nil_append, zero_mul,
      zero_add]
    have : (σ.set R []).set W (σ.get W) = σ := by
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    rw [this]
    exact Runs.loopF (by simp [hd, hR])
  | succ c ih =>
    intro σ hR
    have e1 := runs_pop R σ
    set σ1 := σ.set R (σ.get R).tail with hσ1
    have e2 := runs_pushL W l σ1
    set σ2 := σ1.set W (l.reverse ++ σ1.get W) with hσ2
    have h2R : σ2.get R = List.replicate c .one := by
      rw [hσ2, Regs.get_set, if_neg hRW, hσ1, Regs.get_set_self, hR]; simp [List.replicate_succ]
    have e3 := ih σ2 h2R
    refine ((Runs.loopT (by simp [hd, hR, List.replicate_succ]) (e1.seq e2) e3).congr ?_).mono ?_
    · rw [hσ2, hσ1]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all [List.replicate_succ]
    · simp only [Nat.succ_mul]; omega

def tb (b : Bool) : BSym := if b then BSym.one else BSym.zero

lemma tb_ne_sep (b : Bool) : tb b ≠ BSym.sep := by cases b <;> simp [tb]

lemma bits_split : ∀ {a b : List Bool} {r r' : List BSym},
    a.map tb ++ BSym.sep :: r = b.map tb ++ BSym.sep :: r' → a = b ∧ r = r' := by
  intro a
  induction a with
  | nil =>
    intro b r r' h
    cases b with
    | nil => simpa using h
    | cons y b => simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append,
        List.cons.injEq] at h; exact absurd h.1.symm (tb_ne_sep y)
  | cons x a ih =>
    intro b r r' h
    cases b with
    | nil => simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append,
        List.cons.injEq] at h; exact absurd h.1 (tb_ne_sep x)
    | cons y b =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hxy : x = y := by cases x <;> cases y <;> simp_all [tb]
      obtain ⟨h3, h4⟩ := ih h2
      exact ⟨by rw [hxy, h3], h4⟩

def bv : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bv l)

lemma bv_bits (n : ℕ) : bv (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bv]
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bv, ih]

lemma bits_inj {a b : ℕ} (h : Nat.bits a = Nat.bits b) : a = b := by
  rw [← bv_bits a, h, bv_bits]

lemma encNat_eq_tb (k : ℕ) : encNat k = (Nat.bits k).map tb ++ [BSym.sep] := by
  simp [encNat, tb]

lemma encNat_app {a b : ℕ} {r r' : List BSym} (h : encNat a ++ r = encNat b ++ r') : a = b ∧ r = r' := by
  rw [encNat_eq_tb, encNat_eq_tb] at h
  simp only [List.append_assoc, List.singleton_append] at h
  obtain ⟨h1, h2⟩ := bits_split h
  exact ⟨bits_inj h1, h2⟩


end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity

/-! ## encodings -/

lemma encNat_enc (k : ℕ) : encNat k = enc (Nat.bits k) ++ [BSym.sep] := by
  simp [encNat, enc, toB]

lemma encNats_cons' (k : ℕ) (l : List ℕ) : encNats (k :: l) = encNat k ++ encNats l := by
  simp [encNats]

lemma encNats_append' (l l' : List ℕ) : encNats (l ++ l') = encNats l ++ encNats l' := by
  simp [encNats]

lemma encNats_nil : encNats [] = [] := rfl

lemma encNats_inj : ∀ {l l' : List ℕ}, encNats l = encNats l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons v l' => rw [encNats_nil, encNats_cons', encNat_enc] at h; simp at h
  | cons v l ih =>
    intro l' h
    cases l' with
    | nil => rw [encNats_nil, encNats_cons', encNat_enc] at h; simp at h
    | cons v' l' =>
      rw [encNats_cons', encNats_cons'] at h
      obtain ⟨h1, h2⟩ := encNat_app h
      rw [h1, ih h2]

lemma encNats_eq_nil {L : List ℕ} (h : encNats L = []) : L = [] := by
  cases L with
  | nil => rfl
  | cons v L => rw [encNats_cons', encNat_enc] at h; simp at h

lemma encNats_replicate (c v : ℕ) :
    encNats (List.replicate c v) = (List.replicate c (encNat v)).flatten := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, encNats_cons', ih, List.replicate_succ, List.flatten_cons]

lemma encNat_zero' : encNat 0 = [BSym.sep] := by simp [encNat]
lemma encNat_one' : encNat 1 = [BSym.one, BSym.sep] := by simp [encNat]

lemma flatten_rep_rev (c : ℕ) (l : List BSym) :
    (List.replicate c l).flatten.reverse = (List.replicate c l.reverse).flatten := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.flatten_cons, List.reverse_append, ih, List.replicate_succ',
      List.flatten_append]
    simp

lemma encNats_rev_head (L : List ℕ) (h : L ≠ []) : (encNats L).reverse.head? = some .sep := by
  obtain ⟨L', v, rfl⟩ : ∃ L' v, L = L' ++ [v] := ⟨L.dropLast, L.getLast h, (List.dropLast_append_getLast h).symm⟩
  rw [encNats_append', encNats_cons', encNats_nil, encNat_enc]; simp

/-- a list whose top is not a digit -/
def NoDig (r : List BSym) : Prop := ∀ x, r.head? = some x → isDigB x = false

lemma noDig_nil : NoDig [] := by intro x h; simp at h

lemma noDig_encNats (L : List ℕ) (r : List BSym) (hr : NoDig r) : NoDig ((encNats L).reverse ++ r) := by
  by_cases h : L = []
  · subst h; simp only [encNats_nil, List.reverse_nil, List.nil_append]; exact hr
  · intro x hx
    have := encNats_rev_head L h
    have hne : (encNats L).reverse ≠ [] := by
      intro h0; rw [h0] at this; simp at this
    rw [List.head?_append_of_ne_nil _ hne, this] at hx
    cases hx; rfl

lemma len_encNat_pos (k : ℕ) : 1 ≤ (encNat k).length := by simp [encNat]

lemma length_le_encNats (L : List ℕ) : L.length ≤ (encNats L).length := by
  induction L with
  | nil => simp
  | cons v L ih => rw [encNats_cons', List.length_append]; have := len_encNat_pos v; simp; omega

lemma len_enc_bits_le_encNat (k : ℕ) : (Nat.bits k).length + 1 = (encNat k).length := by
  simp [encNat]

lemma len_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

lemma enc_bits_ne_nil {k : ℕ} (hk : k ≠ 0) : enc (Nat.bits k) ≠ [] := by
  intro h
  have : Nat.bits k = [] := by simpa [enc] using h
  exact hk ((bits_eq_nil_iff' k).1 this)

lemma isSome_head_of_ne_nil {l : List BSym} (h : l ≠ []) : l.head?.isSome = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

/-! ## the fuel loop: `U := min x f` in unary -/

def fuelLoopG (X F U : Key) : Prog :=
  .loop (fun h => (h X).isSome && (h F).isSome)
    (.seq (popProg F) (.seq (pushProg U .one) (decProg X .T)))

lemma runs_fuelG (X F U : Key) (hXF : X ≠ F) (hXU : X ≠ U) (hFU : F ≠ U) (hXT : X ≠ .T)
    (hFT : F ≠ .T) (hUT : U ≠ .T) :
    ∀ (f x : ℕ) (σ : Regs), σ.get X = enc (Nat.bits x) → σ.get F = List.replicate f .one →
      σ.get .T = [] →
      Runs (fuelLoopG X F U) σ
        (((σ.set X (enc (Nat.bits (x - min x f)))).set F (List.replicate (f - min x f) .one)).set U
          (List.replicate (min x f) .one ++ σ.get U))
        (min x f * (6 * (Nat.bits x).length + 22) + 1) := by
  intro f
  induction f with
  | zero =>
    intro x σ hX hF hT
    have hF' : σ.get F = [] := by simpa using hF
    simp only [Nat.min_zero, Nat.sub_zero, List.replicate_zero, List.nil_append, zero_mul, zero_add]
    rw [← hX, ← hF', Regs.set_get, Regs.set_get, Regs.set_get]
    exact Runs.loopF (by simp [hd, hF])
  | succ f ih =>
    intro x σ hX hF hT
    by_cases hx : x = 0
    · subst hx
      simp only [Nat.zero_min, Nat.sub_zero, List.replicate_zero, List.nil_append, zero_mul,
        zero_add]
      rw [← hX, ← hF, Regs.set_get, Regs.set_get, Regs.set_get]
      exact Runs.loopF (by simp [hd, hX, enc])
    obtain ⟨c, r, hcr⟩ := bits_split_false x hx
    have e1 := runs_pop F σ
    set σ1 := σ.set F (σ.get F).tail with hσ1
    have e2 := runs_push U .one σ1
    set σ2 := σ1.set U (.one :: σ1.get U) with hσ2
    have h2X : σ2.get X = enc (List.replicate c false ++ true :: r) := by
      rw [hσ2, Regs.get_set, if_neg hXU, hσ1, Regs.get_set, if_neg hXF, hX, hcr]
    have h2T : σ2.get .T = [] := by
      rw [hσ2, Regs.get_set, if_neg (Ne.symm hUT), hσ1, Regs.get_set, if_neg (Ne.symm hFT), hT]
    have e3 := runs_dec X .T hXT σ2 c r h2X h2T
    rw [← hcr, decL_bits] at e3
    set σ3 := σ2.set X (enc (Nat.bits (x - 1))) with hσ3
    have h3X : σ3.get X = enc (Nat.bits (x - 1)) := by rw [hσ3, Regs.get_set_self]
    have h3F : σ3.get F = List.replicate f .one := by
      rw [hσ3, Regs.get_set, if_neg (Ne.symm hXF), hσ2, Regs.get_set, if_neg hFU, hσ1,
        Regs.get_set_self, hF]; simp [List.replicate_succ]
    have h3T : σ3.get .T = [] := by
      rw [hσ3, Regs.get_set, if_neg (Ne.symm hXT), h2T]
    have e4 := ih (x - 1) σ3 h3X h3F h3T
    have hmin : min x (f + 1) = min (x - 1) f + 1 := by omega
    have hfin : (((σ3.set X (enc (Nat.bits (x - 1 - min (x - 1) f)))).set F
        (List.replicate (f - min (x - 1) f) .one)).set U
          (List.replicate (min (x - 1) f) .one ++ σ3.get U)) =
        (((σ.set X (enc (Nat.bits (x - min x (f + 1))))).set F
          (List.replicate (f + 1 - min x (f + 1)) .one)).set U
          (List.replicate (min x (f + 1)) .one ++ σ.get U)) := by
      have h3U : σ3.get U = .one :: σ.get U := by
        rw [hσ3, Regs.get_set, if_neg (Ne.symm hXU), hσ2, Regs.get_set_self, hσ1, Regs.get_set,
          if_neg (Ne.symm hFU)]
      rw [h3U, hmin]
      have e5 : x - 1 - min (x - 1) f = x - (min (x - 1) f + 1) := by omega
      have e6 : f - min (x - 1) f = f + 1 - (min (x - 1) f + 1) := by omega
      rw [e5, e6, hσ3, hσ2, hσ1]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs <;> simp [List.replicate_succ']
    have hc : c ≤ (Nat.bits x).length := by rw [hcr]; simp
    have hlen : (Nat.bits (x - 1)).length ≤ (Nat.bits x).length := len_bits_mono (by omega)
    refine ((Runs.loopT ?_ (e1.seq (e2.seq e3)) e4).congr hfin).mono ?_
    · have h1 : (σ.get X).head?.isSome = true := by
        rw [hX]; exact isSome_head_of_ne_nil (enc_bits_ne_nil hx)
      have h2 : (σ.get F).head?.isSome = true := by rw [hF]; rfl
      simp only [hd, h1, h2, Bool.and_self]
    · rw [hmin]
      have : min (x - 1) f * (6 * (Nat.bits (x - 1)).length + 22) ≤
          min (x - 1) f * (6 * (Nat.bits x).length + 22) := Nat.mul_le_mul_left _ (by omega)
      nlinarith

/-! ## unary to binary, prepended to `out` -/

def binLoop (X : Key) : Prog := .loop (fun h => (h X).isSome) (.seq (popProg X) (incProg .Bc .T))

lemma runs_binLoop (X : Key) (hXB : X ≠ .Bc) (hXT : X ≠ .T) :
    ∀ (c j : ℕ) (σ : Regs), σ.get X = List.replicate c .one → σ.get .Bc = enc (Nat.bits j) →
      σ.get .T = [] →
      Runs (binLoop X) σ ((σ.set X []).set .Bc (enc (Nat.bits (j + c))))
        (c * (6 * (j + c) + 14) + 1) := by
  intro c
  induction c with
  | zero =>
    intro j σ hX hB hT
    simp only [List.replicate_zero] at hX
    simp only [add_zero, zero_mul, zero_add]
    rw [← hX, ← hB, Regs.set_get, Regs.set_get]
    exact Runs.loopF (by simp [hd, hX])
  | succ c ih =>
    intro j σ hX hB hT
    have e1 := runs_pop X σ
    set σ1 := σ.set X (σ.get X).tail with hσ1
    have h1B : σ1.get .Bc = enc (Nat.bits j) := by rw [hσ1, Regs.get_set, if_neg (Ne.symm hXB), hB]
    have h1T : σ1.get .T = [] := by rw [hσ1, Regs.get_set, if_neg (Ne.symm hXT), hT]
    have e2 := runs_inc .Bc .T (by decide) σ1 (Nat.bits j) h1B h1T
    rw [incL_bits] at e2
    set σ2 := σ1.set .Bc (enc (Nat.bits (j + 1))) with hσ2
    have h2X : σ2.get X = List.replicate c .one := by
      rw [hσ2, Regs.get_set, if_neg hXB, hσ1, Regs.get_set_self, hX]; simp [List.replicate_succ]
    have h2B : σ2.get .Bc = enc (Nat.bits (j + 1)) := by rw [hσ2, Regs.get_set_self]
    have h2T : σ2.get .T = [] := by rw [hσ2, Regs.get_set, if_neg (by decide), h1T]
    have e3 := ih (j + 1) σ2 h2X h2B h2T
    have hfin : (σ2.set X []).set .Bc (enc (Nat.bits (j + 1 + c))) =
        (σ.set X []).set .Bc (enc (Nat.bits (j + (c + 1)))) := by
      rw [show j + 1 + c = j + (c + 1) by omega, hσ2, hσ1]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs <;> subst_vars <;> simp_all
    refine ((Runs.loopT (by simp [hd, hX, List.replicate_succ]) (e1.seq e2) e3).congr hfin).mono ?_
    have hl : (Nat.bits j).length ≤ j + (c + 1) := le_trans (len_bits_le j) (by omega)
    have : c * (6 * (j + 1 + c) + 14) ≤ c * (6 * (j + (c + 1)) + 14) := le_of_eq (by ring_nf)
    nlinarith

def emitU (X : Key) : Prog :=
  .seq (binLoop X) (.seq (pushProg .out .sep) (.seq (mvProg .Bc .A) (mvProg .A .out)))

lemma runs_emitU (X : Key) (hXB : X ≠ .Bc) (hXT : X ≠ .T) (hXo : X ≠ .out) (hXA : X ≠ .A)
    (c : ℕ) (σ : Regs) (hX : σ.get X = List.replicate c .one) (hB : σ.Bc = []) (hT : σ.T = [])
    (hA : σ.A = []) :
    Runs (emitU X) σ ((σ.set X []).set .out (encNat c ++ σ.out)) (c * (6 * c + 14) + 6 * c + 12) := by
  have e1 := runs_binLoop X hXB hXT c 0 σ hX (by simp [Regs.get, hB]) (by simp [Regs.get, hT])
  rw [zero_add] at e1
  set σ1 := (σ.set X []).set .Bc (enc (Nat.bits c)) with hσ1
  have e2 := runs_push .out .sep σ1
  set σ2 := σ1.set .out (.sep :: σ1.get .out) with hσ2
  have e3 := runs_mv .Bc .A (by decide) σ2
  set σ3 := (σ2.set .Bc []).set .A ((σ2.get .Bc).reverse ++ σ2.get .A) with hσ3
  have e4 := runs_mv .A .out (by decide) σ3
  have hfin : (σ3.set .A []).set .out ((σ3.get .A).reverse ++ σ3.get .out) =
      (σ.set X []).set .out (encNat c ++ σ.out) := by
    have h2B : σ2.get .Bc = enc (Nat.bits c) := by
      rw [hσ2, Regs.get_set, if_neg (by decide), hσ1, Regs.get_set_self]
    have h2A : σ2.get .A = [] := by
      rw [hσ2, Regs.get_set, if_neg (by decide), hσ1, Regs.get_set, if_neg (by decide),
        Regs.get_set, if_neg (Ne.symm hXA)]; exact hA
    have h3A : σ3.get .A = (enc (Nat.bits c)).reverse := by
      rw [hσ3, Regs.get_set_self, h2B, h2A, List.append_nil]
    have h3o : σ3.get .out = .sep :: σ.out := by
      rw [hσ3, Regs.get_set, if_neg (by decide), Regs.get_set, if_neg (by decide), hσ2,
        Regs.get_set_self, hσ1, Regs.get_set, if_neg (by decide), Regs.get_set, if_neg (Ne.symm hXo)]
      rfl
    rw [h3A, h3o, List.reverse_reverse, encNat_enc, hσ3, hσ2, hσ1]
    apply Regs.ext_get; funext i; simp only [Regs.get_set]
    split_ifs <;> subst_vars <;> simp_all [Regs.get]
  refine ((e1.seq (e2.seq (e3.seq e4))).congr hfin).mono ?_
  have h2B : (σ2.get .Bc).length ≤ c := by
    rw [hσ2, Regs.get_set, if_neg (by decide), hσ1, Regs.get_set_self, length_enc]
    exact len_bits_le c
  have h3A : (σ3.get .A).length ≤ c := by
    rw [hσ3, Regs.get_set_self, List.length_append, List.length_reverse]
    have : σ2.get .A = [] := by
      rw [hσ2, Regs.get_set, if_neg (by decide), hσ1, Regs.get_set, if_neg (by decide),
        Regs.get_set, if_neg (Ne.symm hXA)]; exact hA
    rw [this]; simpa using h2B
  omega

/-! ## moving one token from the reversed input `rv` onto `out` -/

def tok1 : Prog := .seq (mv1 .rv .out) (mvwProg .rv .out isDigB)

lemma takeWhile_noDig (r : List BSym) (hr : NoDig r) : r.takeWhile isDigB = [] := by
  cases r with
  | nil => rfl
  | cons x r => have := hr x rfl; simp [List.takeWhile, this]

lemma dropWhile_noDig (r : List BSym) (hr : NoDig r) : r.dropWhile isDigB = r := by
  cases r with
  | nil => rfl
  | cons x r => have := hr x rfl; simp [List.dropWhile, this]

lemma runs_tok1 (σ : Regs) (v : ℕ) (r : List BSym) (hr : NoDig r)
    (h : σ.rv = (encNat v).reverse ++ r) :
    Runs tok1 σ ((σ.set .rv r).set .out (encNat v ++ σ.out)) (3 * σ.rv.length + 3) := by
  have hrv : σ.get .rv = BSym.sep :: ((enc (Nat.bits v)).reverse ++ r) := by
    simp only [Regs.get, h, encNat_enc, List.reverse_append]; simp
  have e1 := runs_mv1 .rv .out (by decide) σ _ _ hrv
  set σ1 := (σ.set .rv ((enc (Nat.bits v)).reverse ++ r)).set .out (.sep :: σ.get .out) with hσ1
  have e2 := runs_mvw .rv .out (by decide) isDigB _ σ1 (by rw [hσ1, Regs.get_set, if_neg (by decide), Regs.get_set_self])
  have hdig : ∀ x ∈ (enc (Nat.bits v)).reverse, isDigB x = true := by
    intro x hx; exact isDigB_enc _ x (List.mem_reverse.mp hx)
  rw [List.takeWhile_append_of_pos hdig, List.dropWhile_append_of_pos hdig,
    takeWhile_noDig r hr, dropWhile_noDig r hr, List.append_nil, List.reverse_reverse] at e2
  refine (e1.seq e2).congr ?_ |>.mono ?_
  · rw [hσ1]
    apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, encNat_enc]
  · have : ((enc (Nat.bits v)).reverse ++ r).length + 1 = σ.rv.length := by
      rw [h, encNat_enc]; simp
    omega

/-- transfer as many tokens as the counter `Ck` holds -/
def tokLoop (Ck : Key) : Prog := .loop (fun h => (h Ck).isSome) (.seq (popProg Ck) tok1)

lemma runs_tokLoop (Ck : Key) (hC1 : Ck ≠ .rv) (hC2 : Ck ≠ .out) (r : List BSym) (hr : NoDig r) :
    ∀ (vs : List ℕ) (σ : Regs), σ.get Ck = List.replicate vs.length .one →
      σ.rv = (encNats vs).reverse ++ r →
      Runs (tokLoop Ck) σ (((σ.set Ck []).set .rv r).set .out (encNats vs ++ σ.out))
        (vs.length * (3 * σ.rv.length + 8) + 1) := by
  intro vs
  induction vs using List.reverseRecOn with
  | nil =>
    intro σ hC hrv
    simp only [List.length_nil, List.replicate_zero] at hC
    simp only [encNats_nil, List.reverse_nil, List.nil_append] at hrv
    simp only [List.length_nil, zero_mul, zero_add, encNats_nil, List.nil_append]
    have : ((σ.set Ck []).set .rv r).set .out σ.out = σ := by
      rw [← hC, ← hrv, Regs.set_get]
      show (σ.set .rv (σ.get .rv)).set .out (σ.get .out) = σ
      rw [Regs.set_get, Regs.set_get]
    rw [this]
    exact Runs.loopF (by simp [hd, hC])
  | append_singleton vs v ih =>
    intro σ hC hrv
    have e1 := runs_pop Ck σ
    set σ1 := σ.set Ck (σ.get Ck).tail with hσ1
    have h1rv : σ1.rv = (encNat v).reverse ++ ((encNats vs).reverse ++ r) := by
      have : σ1.rv = σ.rv := by
        rw [hσ1]; cases Ck <;> first | exact absurd rfl hC1 | rfl
      rw [this, hrv, encNats_append', encNats_cons', encNats_nil]; simp
    have e2 := runs_tok1 σ1 v _ (noDig_encNats vs r hr) h1rv
    set σ2 := (σ1.set .rv ((encNats vs).reverse ++ r)).set .out (encNat v ++ σ1.out) with hσ2
    have h2C : σ2.get Ck = List.replicate vs.length .one := by
      rw [hσ2, Regs.get_set, if_neg hC2, Regs.get_set, if_neg hC1, hσ1, Regs.get_set_self, hC]
      simp [List.replicate_succ]
    have e3 := ih σ2 h2C rfl
    have hfin : ((σ2.set Ck []).set .rv r).set .out (encNats vs ++ σ2.out) =
        ((σ.set Ck []).set .rv r).set .out (encNats (vs ++ [v]) ++ σ.out) := by
      have ho : σ2.out = encNat v ++ σ.out := by
        have h1 : σ2.get .out = encNat v ++ σ1.out := by rw [hσ2, Regs.get_set_self]
        have h2 : σ1.get .out = σ.get .out := by rw [hσ1, Regs.get_set, if_neg (Ne.symm hC2)]
        exact h1.trans (by rw [show σ1.out = σ1.get .out from rfl, h2]; rfl)
      rw [ho, encNats_append', encNats_cons', encNats_nil, List.append_nil, List.append_assoc]
      rw [hσ2, hσ1]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs <;> simp_all
    refine ((Runs.loopT (by simp [hd, hC]) (e1.seq e2) e3).congr hfin).mono ?_
    have hl1 : σ1.rv.length = σ.rv.length := by
      rw [hσ1]; cases Ck <;> first | exact absurd rfl hC1 | rfl
    have hl2 : σ2.rv.length ≤ σ.rv.length := by
      have : σ2.rv = (encNats vs).reverse ++ r := by
        show σ2.get .rv = _
        rw [hσ2, Regs.get_set, if_neg (by decide), Regs.get_set_self]
      rw [this, hrv, encNats_append']; simp
    simp only [List.length_append, List.length_singleton]
    have : vs.length * (3 * σ2.rv.length + 8) ≤ vs.length * (3 * σ.rv.length + 8) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity

/-! ## token validation: the input is `encNats L` for some list `L` -/

def tstV : (Key → Option BSym) → Bool :=
  fun h => decide (h .I2 = some .sep) && decide (h .A ≠ some .zero)

def tokBody : Prog :=
  .seq (mvwProg .I2 .A isDigB)
    (.seq (.branch tstV (.seq (popProg .I2) (pushProg .Tu .one)) (pushProg .bad .one))
      (clearProg .A))

def vLoop : Prog := .loop (fun h => (h .I2).isSome && (h .bad).isNone) tokBody

lemma runs_tokBody (σ : Regs) (w : List BSym) (hI : σ.I2 = w) (hA : σ.A = []) :
    Runs tokBody σ
      (if numOK w then { σ with I2 := (rest w).tail, Tu := .one :: σ.Tu }
        else { σ with I2 := rest w, bad := .one :: σ.bad }) (6 * w.length + 10) := by
  have e1 := runs_mvw .I2 .A (by decide) isDigB w σ hI
  set σ1 := (σ.set .I2 (w.dropWhile isDigB)).set .A ((w.takeWhile isDigB).reverse ++ σ.get .A)
    with hσ1
  have h1i : σ1.I2 = rest w := rfl
  have h1A : σ1.A = (digs w).reverse := by
    simp [hσ1, Regs.set, Regs.get, hA, digs]
  have hdl : (digs w).length ≤ w.length := (List.takeWhile_sublist _).length_le
  by_cases hok : numOK w
  · rw [if_pos hok]
    obtain ⟨hs, hl⟩ := hok
    have e2 : Runs (.branch tstV (.seq (popProg .I2) (pushProg .Tu .one)) (pushProg .bad .one))
        σ1 ((σ1.set .I2 (σ1.get .I2).tail).set .Tu (.one :: (σ1.set .I2 (σ1.get .I2).tail).get .Tu))
        4 := by
      refine ((runs_pop .I2 σ1).seq (runs_push .Tu .one _)).brT ?_
      simp only [tstV, hd, Regs.get, h1i, hs, h1A, List.head?_reverse, decide_true, Bool.true_and,
        decide_eq_true_eq]
      exact hl
    set σ2 := (σ1.set .I2 (σ1.get .I2).tail).set .Tu (.one :: (σ1.set .I2 (σ1.get .I2).tail).get .Tu)
      with hσ2
    have e3 := runs_clear .A σ2
    refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
    · rw [hσ2]
      apply Regs.ext_get; funext i
      cases i <;> simp [Regs.get, Regs.set, hσ1, hA, rest]
    · have : (σ2.get .A).length ≤ w.length := by
        simp only [hσ2, Regs.get, Regs.set, h1A, List.length_reverse]; exact hdl
      omega
  · rw [if_neg hok]
    have e2 : Runs (.branch tstV (.seq (popProg .I2) (pushProg .Tu .one)) (pushProg .bad .one))
        σ1 (σ1.set .bad (.one :: σ1.get .bad)) 2 := by
      refine (runs_push .bad .one σ1).brF ?_
      simp only [tstV, hd, Regs.get, h1i, h1A, List.head?_reverse]
      unfold numOK at hok
      by_cases hs : (rest w).head? = some .sep
      · have hl : (digs w).getLast? = some .zero := by
          by_contra h; exact hok ⟨hs, h⟩
        simp [hs, hl]
      · simp [hs]
    set σ2 := σ1.set .bad (.one :: σ1.get .bad) with hσ2
    have e3 := runs_clear .A σ2
    refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
    · rw [hσ2]
      apply Regs.ext_get; funext i
      cases i <;> simp [Regs.get, Regs.set, hσ1, hA, rest]
    · have : (σ2.get .A).length ≤ w.length := by
        simp only [hσ2, Regs.get, Regs.set, h1A, List.length_reverse]; exact hdl
      omega

lemma rest_len' (w : List BSym) : (rest w).length ≤ w.length := (List.dropWhile_sublist _).length_le

lemma numOK_decomp (w : List BSym) (h : numOK w) :
    w = enc (Nat.bits (nval w)) ++ BSym.sep :: (rest w).tail := by
  have h1 := List.takeWhile_append_dropWhile (p := isDigB) (l := w)
  have h3 : rest w = BSym.sep :: (rest w).tail := by
    have := h.1
    cases hr : rest w with
    | nil => rw [hr] at this; cases this
    | cons a l => rw [hr] at this; simp at this; subst this; rfl
  rw [← digs_eq w h, ← h3]
  exact h1.symm

lemma encNats_cons_enc (v : ℕ) (L : List ℕ) :
    encNats (v :: L) = enc (Nat.bits v) ++ BSym.sep :: encNats L := by
  rw [encNats_cons', encNat_enc]; simp

lemma runs_vLoop : ∀ (N : ℕ) (w : List BSym), w.length ≤ N → ∀ σ : Regs, σ.I2 = w → σ.A = [] →
    σ.bad = [] →
    ∃ τ, Runs vLoop σ τ (10 * (w.length + 1) ^ 2) ∧
      (∀ L, w = encNats L → τ = { σ with I2 := [], Tu := List.replicate L.length .one ++ σ.Tu }) ∧
      ((¬ ∃ L, w = encNats L) → τ.bad ≠ [] ∧ τ.out = σ.out ∧ τ.inp = σ.inp) := by
  intro N
  induction N with
  | zero =>
    intro w hw σ hI hA hb
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw0
    refine ⟨σ, (Runs.loopF (by simp [hd, Regs.get, hI])).mono (by simp), ?_, ?_⟩
    · intro L hL
      have := encNats_eq_nil hL.symm; subst this
      cases σ; simp_all
    · intro h; exact absurd ⟨[], rfl⟩ h
  | succ N ih =>
    intro w hw σ hI hA hb
    cases w with
    | nil =>
      refine ⟨σ, (Runs.loopF (by simp [hd, Regs.get, hI])).mono (by simp), ?_, ?_⟩
      · intro L hL
        have := encNats_eq_nil hL.symm; subst this
        cases σ; simp_all
      · intro h; exact absurd ⟨[], rfl⟩ h
    | cons x r =>
      have e1 := runs_tokBody σ (x :: r) hI hA
      have htest : (fun h : Key → Option BSym => (h .I2).isSome && (h .bad).isNone) (hd σ) = true := by
        simp [hd, Regs.get, hI, hb]
      by_cases hok : numOK (x :: r)
      · rw [if_pos hok] at e1
        set σ1 := { σ with I2 := (rest (x :: r)).tail, Tu := .one :: σ.Tu } with hσ1
        have hlen : (rest (x :: r)).tail.length ≤ N := by
          have := rest_len' (x :: r)
          have h3 : (rest (x :: r)).tail.length + 1 = (rest (x :: r)).length := by
            have := hok.1
            cases hr : rest (x :: r) with
            | nil => rw [hr] at this; cases this
            | cons a l => simp
          simp at hw this; omega
        obtain ⟨τ, e2, h2a, h2b⟩ := ih _ hlen σ1 rfl hA hb
        refine ⟨τ, (Runs.loopT htest e1 e2).mono ?_, ?_, ?_⟩
        · have : (rest (x :: r)).tail.length ≤ r.length := by
            have := rest_len' (x :: r)
            have h3 : (rest (x :: r)).tail.length + 1 = (rest (x :: r)).length := by
              have := hok.1
              cases hr : rest (x :: r) with
              | nil => rw [hr] at this; cases this
              | cons a l => simp
            simp at this; omega
          simp only [List.length_cons]
          nlinarith
        · intro L hL
          cases L with
          | nil => simp [encNats] at hL
          | cons v L' =>
            have hrest : (rest (x :: r)).tail = encNats L' := by
              rw [hL, encNats_cons_enc, rest_code]; rfl
            rw [h2a L' hrest, hσ1]
            simp [List.replicate_succ']
        · intro hno
          have hno' : ¬ ∃ L, (rest (x :: r)).tail = encNats L := by
            rintro ⟨L, hL⟩
            apply hno
            refine ⟨nval (x :: r) :: L, ?_⟩
            rw [encNats_cons_enc, ← hL]; exact numOK_decomp _ hok
          obtain ⟨h1, h2, h3⟩ := h2b hno'
          exact ⟨h1, h2, h3⟩
      · rw [if_neg hok] at e1
        set σ1 := { σ with I2 := rest (x :: r), bad := .one :: σ.bad } with hσ1
        have e2 : Runs vLoop σ1 σ1 1 := Runs.loopF (by simp [hd, Regs.get, hσ1])
        refine ⟨σ1, (Runs.loopT htest e1 e2).mono ?_, ?_, ?_⟩
        · simp only [List.length_cons]; nlinarith
        · intro L hL
          exfalso
          cases L with
          | nil => simp [encNats] at hL
          | cons v L' =>
            apply hok; rw [hL, encNats_cons_enc]; exact numOK_code v _
        · intro _; exact ⟨by simp [hσ1], rfl, rfl⟩

end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity

def S0 (w : List BSym) : Regs := { Regs.empty with inp := w }

def C1 : Prog :=
  .seq (copyProg .inp .I2 .sc) (.seq (mvwProg .I2 .A isDigB) (.seq (mvProg .A .Bn) (clearProg .I2)))

def C2 : Prog :=
  .seq (copyProg .Tu .F .sc) (.seq (fuelLoopG .Bn .F .Nu)
    (.seq (.branch (fun h => (h .Bn).isSome) (pushProg .bad .one) skipP) (clearProg .F)))

def C3 : Prog :=
  .seq (copyProg .Nu .C .sc)
    (.seq (repProg .Nu .Q .C .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (.seq (copyProg .Nu .Q .sc) (.seq (pushL .Q [.one, .one, .one]) (.seq (syncPopProg .Q .Tu)
        (.branch (fun h => (h .Q).isSome || (h .Tu).isSome) (pushProg .bad .one) skipP)))))

def valProg : Prog :=
  .seq (copyProg .inp .I2 .sc) (.seq vLoop (gate (.seq C1 (.seq C2 (gate C3)))))

/-- the syntactic validity of an input -/
def ValidL (L : List ℕ) : Prop := L.length = L.headD 0 * L.headD 0 + L.headD 0 + 3

lemma digs_encNats (L : List ℕ) : digs (encNats L) = enc (Nat.bits (L.headD 0)) := by
  cases L with
  | nil => rfl
  | cons v L => rw [encNats_cons_enc, digs_code]; rfl

lemma runs_C1 (w : List BSym) (t : List BSym) :
    Runs C1 { S0 w with Tu := t } { S0 w with Tu := t, Bn := digs w } (20 * w.length + 10) := by
  set σ0 : Regs := { S0 w with Tu := t } with hσ0
  have e1 := runs_copy .inp .I2 .sc (by decide) (by decide) (by decide) σ0 rfl
  set σ1 := σ0.set .I2 (σ0.get .inp ++ σ0.get .I2) with hσ1
  have e2 := runs_mvw .I2 .A (by decide) isDigB w σ1 (by simp [hσ1, hσ0, Regs.get, Regs.set, S0, Regs.empty])
  set σ2 := (σ1.set .I2 (w.dropWhile isDigB)).set .A ((w.takeWhile isDigB).reverse ++ σ1.get .A) with hσ2
  have e3 := runs_mv .A .Bn (by decide) σ2
  set σ3 := (σ2.set .A []).set .Bn ((σ2.get .A).reverse ++ σ2.get .Bn) with hσ3
  have e4 := runs_clear .I2 σ3
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ3, hσ2, hσ1, hσ0, S0, Regs.empty, digs]
  · have hd1 : (w.takeWhile isDigB).length ≤ w.length := (List.takeWhile_sublist _).length_le
    have hd2 : (w.dropWhile isDigB).length ≤ w.length := (List.dropWhile_sublist _).length_le
    simp [Regs.get, Regs.set, hσ3, hσ2, hσ1, hσ0, S0, Regs.empty]
    omega

lemma runs_C2 (w : List BSym) (n f : ℕ) :
    ∃ τ, Runs C2 { S0 w with Tu := List.replicate f .one, Bn := enc (Nat.bits n) } τ
        (f * (6 * (Nat.bits n).length + 22) + 12 * f + 30) ∧
      (n ≤ f → τ = { S0 w with Tu := List.replicate f .one, Nu := List.replicate n .one }) ∧
      (f < n → τ.bad ≠ [] ∧ τ.out = []) := by
  set σ0 : Regs := { S0 w with Tu := List.replicate f .one, Bn := enc (Nat.bits n) } with hσ0
  have e1 := runs_copy .Tu .F .sc (by decide) (by decide) (by decide) σ0 rfl
  set σ1 := σ0.set .F (σ0.get .Tu ++ σ0.get .F) with hσ1
  have e2 := runs_fuelG .Bn .F .Nu (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) f n σ1 (by simp [hσ1, hσ0, Regs.get, Regs.set])
    (by simp [hσ1, hσ0, Regs.get, Regs.set, S0, Regs.empty]) (by simp [hσ1, hσ0, Regs.get, Regs.set, S0, Regs.empty])
  set σ2 := ((σ1.set .Bn (enc (Nat.bits (n - min n f)))).set .F (List.replicate (f - min n f) .one)).set .Nu
    (List.replicate (min n f) .one ++ σ1.get .Nu) with hσ2
  have hcost1 : (6 * (σ0.get .Tu).length + 3) = 6 * f + 3 := by simp [hσ0, Regs.get]
  rw [hcost1] at e1
  have hm : min n f * (6 * (Nat.bits n).length + 22) ≤ f * (6 * (Nat.bits n).length + 22) :=
    Nat.mul_le_mul_right _ (min_le_right _ _)
  by_cases h : n ≤ f
  · have hmin : min n f = n := min_eq_left h
    have hBn : σ2.Bn = [] := by simp [hσ2, Regs.set, hmin, enc]
    have e3 : Runs (.branch (fun h => (h .Bn).isSome) (pushProg .bad .one) skipP) σ2 σ2 2 :=
      (runs_skip _).brF (by simp [hd, Regs.get, hBn])
    have e4 := runs_clear .F σ2
    refine ⟨_, ((e1.seq (e2.seq (e3.seq e4)))).mono ?_, fun _ => ?_, fun h' => by omega⟩
    · have : (σ2.get .F).length ≤ f := by simp [hσ2, Regs.get, Regs.set]
      omega
    · apply Regs.ext_get; funext i
      cases i <;> simp [Regs.get, Regs.set, hσ2, hσ1, hσ0, S0, Regs.empty, hmin, enc]
  · have hmin : min n f = f := min_eq_right (by omega)
    have hne : σ2.Bn ≠ [] := by
      simp only [hσ2, Regs.set, hmin]; exact enc_bits_ne_nil (by omega)
    have e3 : Runs (.branch (fun h => (h .Bn).isSome) (pushProg .bad .one) skipP) σ2
        (σ2.set .bad (.one :: σ2.get .bad)) 2 :=
      (runs_push .bad .one _).brT (by simp only [hd, Regs.get]; exact isSome_head_of_ne_nil hne)
    have e4 := runs_clear .F (σ2.set .bad (.one :: σ2.get .bad))
    refine ⟨_, ((e1.seq (e2.seq (e3.seq e4)))).mono ?_, fun h' => absurd h' h, fun _ => ?_⟩
    · have : ((σ2.set .bad (.one :: σ2.get .bad)).get .F).length ≤ f := by
        simp [hσ2, Regs.get, Regs.set]
      omega
    · constructor
      · simp [Regs.set, Regs.get]
      · simp [Regs.set, Regs.get, hσ2, hσ1, hσ0, S0, Regs.empty]

lemma flatten_rep_one (a b : ℕ) :
    (List.replicate a (List.replicate b BSym.one)).flatten = List.replicate (a * b) .one := by
  induction a with
  | zero => simp
  | succ a ih => rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm,
      List.replicate_add]

lemma runs_C3 (w : List BSym) (n f : ℕ) :
    ∃ τ, Runs C3 { S0 w with Tu := List.replicate f .one, Nu := List.replicate n .one } τ
        (20 * (n + 1) ^ 2 + 3 * f + 30) ∧
      (f = n * n + n + 3 → τ = { S0 w with Nu := List.replicate n .one }) ∧
      (f ≠ n * n + n + 3 → τ.bad ≠ [] ∧ τ.out = []) := by
  set σ0 : Regs := { S0 w with Tu := List.replicate f .one, Nu := List.replicate n .one } with hσ0
  have e1 := runs_copy .Nu .C .sc (by decide) (by decide) (by decide) σ0 rfl
  rw [show σ0.get .Nu = List.replicate n .one from rfl, show σ0.get .C = [] from rfl,
    List.append_nil, List.length_replicate] at e1
  set σ1 := σ0.set .C (List.replicate n .one) with hσ1
  have e2 := runs_rep .Nu .Q .C .sc (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ1 rfl
  rw [show σ1.get .C = List.replicate n .one from Regs.get_set_self _ _ _,
    show σ1.get .Nu = List.replicate n .one from rfl, show σ1.get .Q = [] from rfl,
    List.append_nil, List.length_replicate, flatten_rep_one] at e2
  set σ2 := (σ1.set .C []).set .Q (List.replicate (n * n) .one) with hσ2
  have e3 := runs_copy .Nu .Q .sc (by decide) (by decide) (by decide) σ2 rfl
  rw [show σ2.get .Nu = List.replicate n .one from rfl,
    show σ2.get .Q = List.replicate (n * n) .one from Regs.get_set_self _ _ _,
    ← List.replicate_add, List.length_replicate] at e3
  set σ3 := σ2.set .Q (List.replicate (n + n * n) .one) with hσ3
  have e4 := runs_pushL .Q [.one, .one, .one] σ3
  rw [show σ3.get .Q = List.replicate (n + n * n) .one from Regs.get_set_self _ _ _] at e4
  have hrep : [BSym.one, .one, .one].reverse ++ List.replicate (n + n * n) .one =
      List.replicate (n * n + n + 3) .one := by
    rw [show n * n + n + 3 = (n + n * n) + 1 + 1 + 1 by ring]
    simp [List.replicate_succ]
  rw [hrep] at e4
  set σ4 := σ3.set .Q (List.replicate (n * n + n + 3) .one) with hσ4
  have h4Q : σ4.get .Q = List.replicate (n * n + n + 3) .one := Regs.get_set_self _ _ _
  have h4T : σ4.get .Tu = List.replicate f .one := rfl
  have e5 := runs_syncpop .Q .Tu (by decide) σ4
  rw [h4Q, h4T] at e5
  simp only [List.length_replicate, List.drop_replicate] at e5
  set σ5 := (σ4.set .Q (List.replicate (n * n + n + 3 - min (n * n + n + 3) f) .one)).set .Tu
    (List.replicate (f - min (n * n + n + 3) f) .one) with hσ5
  have hcost : 6 * n + 3 + 1 + ((6 * n + 7) * n + 1 + 1 + (6 * n + 3 + 1 +
      (2 * List.length [BSym.one, BSym.one, BSym.one] + 1 + 1 +
      (3 * min (n * n + n + 3) f + 1 + 1 + 2)))) ≤ 20 * (n + 1) ^ 2 + 3 * f + 30 := by
    have : min (n * n + n + 3) f ≤ f := min_le_right _ _
    simp only [List.length_cons, List.length_nil]
    nlinarith
  by_cases h : f = n * n + n + 3
  · have hQ : σ5.Q = [] := by simp [hσ5, Regs.set, h]
    have hT : σ5.Tu = [] := by simp [hσ5, Regs.set, h]
    have e6 : Runs (.branch (fun h => (h .Q).isSome || (h .Tu).isSome) (pushProg .bad .one) skipP)
        σ5 σ5 2 := (runs_skip _).brF (by simp [hd, Regs.get, hQ, hT])
    refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).mono hcost, fun _ => ?_, fun h' => absurd h h'⟩
    apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, S0, Regs.empty, h]
  · have hne : (σ5.get .Q).head?.isSome || (σ5.get .Tu).head?.isSome := by
      simp only [hσ5, Regs.get_set_self, Regs.get_set, if_neg (show Key.Tu ≠ Key.Q by decide)]
      rcases Nat.lt_or_gt_of_ne h with h' | h'
      · rw [min_eq_right h'.le]
        have : n * n + n + 3 - f ≠ 0 := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
        rw [hk]; simp [List.replicate_succ]
      · rw [min_eq_left h'.le]
        have : f - (n * n + n + 3) ≠ 0 := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
        rw [hk]; simp [List.replicate_succ]
    have e6 : Runs (.branch (fun h => (h .Q).isSome || (h .Tu).isSome) (pushProg .bad .one) skipP)
        σ5 (σ5.set .bad (.one :: σ5.get .bad)) 2 :=
      (runs_push .bad .one _).brT (by simpa [hd] using hne)
    refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).mono hcost, fun h' => absurd h' h, fun _ => ?_⟩
    constructor
    · simp [Regs.set, Regs.get]
    · simp [Regs.set, Regs.get, hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, S0, Regs.empty]

/-- the validation phase -/
theorem runs_val (w : List BSym) :
    ∃ τ, Runs valProg (S0 w) τ (200 * (w.length + 1) ^ 2) ∧
      (∀ L, w = encNats L → ValidL L → τ = { S0 w with Nu := List.replicate (L.headD 0) .one }) ∧
      ((¬ ∃ L, w = encNats L ∧ ValidL L) → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_copy .inp .I2 .sc (by decide) (by decide) (by decide) (S0 w) rfl
  set σ1 := (S0 w).set .I2 ((S0 w).get .inp ++ (S0 w).get .I2) with hσ1
  obtain ⟨τ2, e2, h2a, h2b⟩ := runs_vLoop w.length w le_rfl σ1 (by simp [hσ1, S0, Regs.get, Regs.set, Regs.empty])
    (by simp [hσ1, S0, Regs.get, Regs.set, Regs.empty]) (by simp [hσ1, S0, Regs.get, Regs.set, Regs.empty])
  have hc1 : 6 * ((S0 w).get .inp).length + 3 = 6 * w.length + 3 := by simp [S0, Regs.get]
  rw [hc1] at e1
  by_cases hv : ∃ L, w = encNats L
  · obtain ⟨L, hL⟩ := hv
    have hτ2 : τ2 = { S0 w with Tu := List.replicate L.length .one } := by
      rw [h2a L hL]; simp [hσ1, S0, Regs.get, Regs.set, Regs.empty]
    subst hτ2
    have e3 := runs_C1 w (List.replicate L.length .one)
    rw [hL, digs_encNats, ← hL] at e3
    obtain ⟨τ4, e4, h4a, h4b⟩ := runs_C2 w (L.headD 0) L.length
    have hLw : L.length ≤ w.length := by rw [hL]; exact length_le_encNats L
    have hbits : (Nat.bits (L.headD 0)).length ≤ w.length := by
      have : (digs w).length ≤ w.length := (List.takeWhile_sublist _).length_le
      rw [hL, digs_encNats, length_enc] at this; rw [hL]; exact this
    have hc4 : L.length * (6 * (Nat.bits (L.headD 0)).length + 22) ≤ w.length * (6 * w.length + 22) :=
      Nat.mul_le_mul hLw (by omega)
    by_cases hn : L.headD 0 ≤ L.length
    · have hτ4 := h4a hn
      subst hτ4
      obtain ⟨τ5, e5, h5a, h5b⟩ := runs_C3 w (L.headD 0) L.length
      have hnw : L.headD 0 ≤ w.length := le_trans hn hLw
      have hc5 : 20 * (L.headD 0 + 1) ^ 2 ≤ 20 * (w.length + 1) ^ 2 := by
        have := Nat.pow_le_pow_left (show L.headD 0 + 1 ≤ w.length + 1 by omega) 2
        omega
      by_cases hval : ValidL L
      · have hτ5 := h5a hval
        subst hτ5
        have e45 := runs_gate_ok (p := C3) (by simp [S0, Regs.empty]) e5
        have e := runs_gate_ok (p := .seq C1 (.seq C2 (gate C3))) (by simp [S0, Regs.empty])
          (e3.seq (e4.seq e45))
        refine ⟨_, (e1.seq (e2.seq e)).mono ?_, ?_, ?_⟩
        · nlinarith
        · intro L' hL' _
          have := encNats_inj (hL.symm.trans hL'); subst this; rfl
        · intro hno; exact absurd ⟨L, hL, hval⟩ hno
      · obtain ⟨hb5, ho5⟩ := h5b hval
        have e45 := runs_gate_ok (p := C3) (by simp [S0, Regs.empty]) e5
        have e := runs_gate_ok (p := .seq C1 (.seq C2 (gate C3))) (by simp [S0, Regs.empty])
          (e3.seq (e4.seq e45))
        refine ⟨_, (e1.seq (e2.seq e)).mono ?_, ?_, fun _ => ⟨hb5, ho5⟩⟩
        · nlinarith
        · intro L' hL' hv'
          have := encNats_inj (hL.symm.trans hL'); subst this; exact absurd hv' hval
    · push Not at hn
      obtain ⟨hb4, ho4⟩ := h4b hn
      have e45 := runs_gate_skip (p := C3) hb4
      have e := runs_gate_ok (p := .seq C1 (.seq C2 (gate C3))) (by simp [S0, Regs.empty])
        (e3.seq (e4.seq e45))
      have hnot : ¬ ValidL L := by unfold ValidL; intro h; nlinarith
      refine ⟨_, (e1.seq (e2.seq e)).mono ?_, ?_, fun _ => ⟨hb4, ho4⟩⟩
      · nlinarith
      · intro L' hL' hv'
        have := encNats_inj (hL.symm.trans hL'); subst this; exact absurd hv' hnot
  · obtain ⟨hb2, ho2, _⟩ := h2b hv
    have e := runs_gate_skip (p := .seq C1 (.seq C2 (gate C3))) hb2
    refine ⟨_, (e1.seq (e2.seq e)).mono ?_, ?_, fun _ => ⟨hb2, by rw [ho2]; simp [hσ1, S0, Regs.get, Regs.set, Regs.empty]⟩⟩
    · nlinarith
    · intro L hL; exact absurd ⟨L, hL⟩ hv

end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity

/-! ## the triangular loop: `Yv += K (K + 1) / 2` -/

def triLoop : Prog :=
  .loop (fun h => (h .C).isSome) (.seq (popProg .C) (.seq (pushProg .A2 .one) (copyProg .A2 .Yv .sc)))

lemma tri_arith (c t : ℕ) :
    t + 1 + (c * (t + 1) + c * (c + 1) / 2) = (c + 1) * t + (c + 1) * (c + 1 + 1) / 2 := by
  have h1 : (c + 1) * (c + 1 + 1) = c * (c + 1) + 2 * (c + 1) := by ring
  rw [h1]
  have h2 : (c * (c + 1) + 2 * (c + 1)) / 2 = c * (c + 1) / 2 + (c + 1) := by omega
  rw [h2]; ring

lemma runs_triLoop (M : ℕ) : ∀ (c t : ℕ) (σ : Regs), σ.C = List.replicate c .one →
    σ.A2 = List.replicate t .one → σ.sc = [] → t + c ≤ M →
    Runs triLoop σ { σ with C := [], A2 := List.replicate (t + c) .one, Yv := List.replicate (c * t + c * (c + 1) / 2) .one ++ σ.Yv } (c * (6 * M + 20) + 1) := by
  intro c
  induction c with
  | zero =>
    intro t σ hC hA hsc hM
    refine (Runs.loopF (by simp [hd, Regs.get, hC])).congr ?_ |>.mono (by simp)
    cases σ; simp_all
  | succ c ih =>
    intro t σ hC hA hsc hM
    have e1 := runs_pop .C σ
    set σ1 := σ.set .C (σ.get .C).tail with hσ1
    have e2 := runs_push .A2 .one σ1
    set σ2 := σ1.set .A2 (.one :: σ1.get .A2) with hσ2
    have e3 := runs_copy .A2 .Yv .sc (by decide) (by decide) (by decide) σ2 (by simp [hσ2, hσ1, Regs.get, Regs.set, hsc])
    set σ3 := σ2.set .Yv (σ2.get .A2 ++ σ2.get .Yv) with hσ3
    have h3 : σ3 = { σ with C := List.replicate c .one, A2 := List.replicate (t + 1) .one, Yv := List.replicate (t + 1) .one ++ σ.Yv } := by
      apply Regs.ext_get; funext i
      cases i <;> simp [Regs.get, Regs.set, hσ3, hσ2, hσ1, hC, hA, List.replicate_succ]
    have e4 := ih (t + 1) { σ with C := List.replicate c .one, A2 := List.replicate (t + 1) .one, Yv := List.replicate (t + 1) .one ++ σ.Yv } rfl rfl hsc (by omega)
    refine ((Runs.loopT (by simp [hd, Regs.get, hC, List.replicate_succ]) (e1.seq (e2.seq (e3.congr h3))) e4).congr ?_).mono ?_
    · simp only [← List.append_assoc, ← List.replicate_add]
      rw [show c * (t + 1) + c * (c + 1) / 2 + (t + 1) = (c + 1) * t + (c + 1) * (c + 1 + 1) / 2 by
        have := tri_arith c t; omega, show t + 1 + c = t + (c + 1) by omega]
    · have : (σ2.get .A2).length = t + 1 := by simp [hσ2, hσ1, Regs.get, Regs.set, hA]
      rw [this]
      nlinarith

/-! ## the new rows -/

def newBody : Prog :=
  .seq (popProg .C) (.seq (copyProg .O .C2 .sc) (.seq (constLoop .C2 .out [.sep, .one])
    (.seq (copyProg .Z .C3 .sc) (.seq (constLoop .C3 .out [.sep])
      (.seq (pushProg .O .one) (popProg .Z))))))

def newLoop : Prog := .loop (fun h => (h .C).isSome) newBody

def rowSym (t z : ℕ) : List BSym := encNats (List.replicate z 0 ++ List.replicate t 1)

def newBlk : ℕ → ℕ → ℕ → List BSym
  | _, _, 0 => []
  | t, z, c + 1 => newBlk (t + 1) (z - 1) c ++ rowSym t z

lemma ones_tokens (t : ℕ) :
    (List.replicate t [BSym.sep, BSym.one]).flatten.reverse = encNats (List.replicate t 1) := by
  rw [flatten_rep_rev, encNats_replicate, encNat_one']; rfl

lemma zeros_tokens (t : ℕ) :
    (List.replicate t [BSym.sep]).flatten.reverse = encNats (List.replicate t 0) := by
  rw [flatten_rep_rev, encNats_replicate, encNat_zero']; rfl

lemma runs_newBody (M : ℕ) (t z : ℕ) (σ : Regs) (hO : σ.O = List.replicate t .one)
    (hZ : σ.Z = List.replicate z .one) (hC2 : σ.C2 = []) (hC3 : σ.C3 = []) (hsc : σ.sc = [])
    (hM : t + z ≤ M) :
    Runs newBody σ { σ with C := σ.C.tail, O := List.replicate (t + 1) .one, Z := List.replicate (z - 1) .one, out := rowSym t z ++ σ.out } (16 * M + 20) := by
  have e1 := runs_pop .C σ
  set σ1 := σ.set .C (σ.get .C).tail with hσ1
  have e2 := runs_copy .O .C2 .sc (by decide) (by decide) (by decide) σ1 (by simp [hσ1, Regs.get, Regs.set, hsc])
  set σ2 := σ1.set .C2 (σ1.get .O ++ σ1.get .C2) with hσ2
  have e3 := runs_constLoop .C2 .out (by decide) [.sep, .one] t σ2 (by simp [hσ2, hσ1, Regs.get, Regs.set, hO, hC2])
  set σ3 := (σ2.set .C2 []).set .out ((List.replicate t [BSym.sep, .one]).flatten.reverse ++ σ2.get .out) with hσ3
  have e4 := runs_copy .Z .C3 .sc (by decide) (by decide) (by decide) σ3 (by simp [hσ3, hσ2, hσ1, Regs.get, Regs.set, hsc])
  set σ4 := σ3.set .C3 (σ3.get .Z ++ σ3.get .C3) with hσ4
  have e5 := runs_constLoop .C3 .out (by decide) [.sep] z σ4 (by simp [hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hZ, hC3])
  set σ5 := (σ4.set .C3 []).set .out ((List.replicate z [BSym.sep]).flatten.reverse ++ σ4.get .out) with hσ5
  have e6 := runs_push .O .one σ5
  set σ6 := σ5.set .O (.one :: σ5.get .O) with hσ6
  have e7 := runs_pop .Z σ6
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).congr ?_).mono ?_
  · rw [ones_tokens, zeros_tokens] at *
    apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hO, hZ, hC2, hC3,
      rowSym, encNats_append', List.replicate_succ, ones_tokens, zeros_tokens]
  · have h1 : (σ1.get .O).length = t := by simp [hσ1, Regs.get, Regs.set, hO]
    have h3 : (σ3.get .Z).length = z := by simp [hσ3, hσ2, hσ1, Regs.get, Regs.set, hZ]
    simp only [h1, h3, List.length_cons, List.length_nil]
    omega

lemma runs_newLoop (M : ℕ) : ∀ (c t z : ℕ) (σ : Regs), σ.C = List.replicate c .one →
    σ.O = List.replicate t .one → σ.Z = List.replicate z .one → σ.C2 = [] → σ.C3 = [] →
    σ.sc = [] → c ≤ z → t + z ≤ M →
    Runs newLoop σ { σ with C := [], O := List.replicate (t + c) .one, Z := List.replicate (z - c) .one, out := newBlk t z c ++ σ.out } (c * (16 * M + 22) + 1) := by
  intro c
  induction c with
  | zero =>
    intro t z σ hC hO hZ hC2 hC3 hsc hcz hM
    refine (Runs.loopF (by simp [hd, Regs.get, hC])).congr ?_ |>.mono (by simp)
    cases σ; simp_all [newBlk]
  | succ c ih =>
    intro t z σ hC hO hZ hC2 hC3 hsc hcz hM
    have e1 := runs_newBody M t z σ hO hZ hC2 hC3 hsc hM
    have e2 := ih (t + 1) (z - 1) { σ with C := σ.C.tail, O := List.replicate (t + 1) .one, Z := List.replicate (z - 1) .one, out := rowSym t z ++ σ.out }
      (by simp [hC, List.replicate_succ]) rfl rfl hC2 hC3 hsc (by omega) (by omega)
    refine ((Runs.loopT (by simp [hd, Regs.get, hC, List.replicate_succ]) e1 e2).congr ?_).mono ?_
    · simp only [newBlk, List.append_assoc]
      rw [show t + 1 + c = t + (c + 1) by omega, show z - 1 - c = z - (c + 1) by omega]
    · nlinarith

/-! ## the old rows -/

def oldBody : Prog :=
  .seq (popProg .C) (.seq (copyProg .Ku .C2 .sc) (.seq (constLoop .C2 .out [.sep, .one])
    (.seq (copyProg .Nu .C3 .sc) (tokLoop .C3))))

def oldLoop : Prog := .loop (fun h => (h .C).isSome) oldBody

lemma runs_oldBody (M K n : ℕ) (row : List ℕ) (hrow : row.length = n) (r : List BSym)
    (hr : NoDig r) (σ : Regs) (hrv : σ.rv = (encNats row).reverse ++ r)
    (hK : σ.Ku = List.replicate K .one) (hN : σ.Nu = List.replicate n .one) (hC2 : σ.C2 = [])
    (hC3 : σ.C3 = []) (hsc : σ.sc = []) (hM1 : σ.rv.length ≤ M) (hM2 : n ≤ M) (hM3 : K ≤ M) :
    Runs oldBody σ { σ with C := σ.C.tail, rv := r, out := encNats row ++ encNats (List.replicate K 1) ++ σ.out } (3 * M * M + 30 * M + 20) := by
  have e1 := runs_pop .C σ
  set σ1 := σ.set .C (σ.get .C).tail with hσ1
  have e2 := runs_copy .Ku .C2 .sc (by decide) (by decide) (by decide) σ1 (by simp [hσ1, Regs.get, Regs.set, hsc])
  set σ2 := σ1.set .C2 (σ1.get .Ku ++ σ1.get .C2) with hσ2
  have e3 := runs_constLoop .C2 .out (by decide) [.sep, .one] K σ2 (by simp [hσ2, hσ1, Regs.get, Regs.set, hK, hC2])
  set σ3 := (σ2.set .C2 []).set .out ((List.replicate K [BSym.sep, .one]).flatten.reverse ++ σ2.get .out) with hσ3
  have e4 := runs_copy .Nu .C3 .sc (by decide) (by decide) (by decide) σ3 (by simp [hσ3, hσ2, hσ1, Regs.get, Regs.set, hsc])
  set σ4 := σ3.set .C3 (σ3.get .Nu ++ σ3.get .C3) with hσ4
  have h4rv : σ4.rv = (encNats row).reverse ++ r := by
    simp [hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hrv]
  have e5 := runs_tokLoop .C3 (by decide) (by decide) r hr row σ4
    (by simp [hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hN, hC3, hrow]) h4rv
  refine ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr ?_).mono ?_
  · rw [ones_tokens] at *
    apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ4, hσ3, hσ2, hσ1, hK, hN, hC2, hC3, ones_tokens]
  · have h1 : (σ1.get .Ku).length = K := by simp [hσ1, Regs.get, Regs.set, hK]
    have h3 : (σ3.get .Nu).length = n := by simp [hσ3, hσ2, hσ1, Regs.get, Regs.set, hN]
    have h4 : σ4.rv.length = σ.rv.length := by simp [hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set]
    simp only [h1, h3, h4, List.length_cons, List.length_nil, hrow]
    have : n * (3 * σ.rv.length + 8) ≤ M * (3 * M + 8) := Nat.mul_le_mul hM2 (by omega)
    nlinarith

lemma runs_oldLoop (M K n : ℕ) (r : List BSym) (hr : NoDig r) :
    ∀ (R : List (List ℕ)), (∀ row ∈ R, row.length = n) → ∀ σ : Regs,
      σ.C = List.replicate R.length .one → σ.rv = (encNats R.flatten).reverse ++ r →
      σ.Ku = List.replicate K .one → σ.Nu = List.replicate n .one → σ.C2 = [] → σ.C3 = [] →
      σ.sc = [] → σ.rv.length ≤ M → n ≤ M → K ≤ M →
      Runs oldLoop σ { σ with C := [], rv := r, out := encNats (R.flatMap (fun row => row ++ List.replicate K 1)) ++ σ.out }
        (R.length * (3 * M * M + 30 * M + 22) + 1) := by
  intro R
  induction R using List.reverseRecOn with
  | nil =>
    intro _ σ hC hrv hK hN hC2 hC3 hsc hM1 hM2 hM3
    refine (Runs.loopF (by simp [hd, Regs.get, hC])).congr ?_ |>.mono (by simp)
    simp at hC hrv
    cases σ; simp_all [encNats_nil]
  | append_singleton R row ih =>
    intro hrows σ hC hrv hK hN hC2 hC3 hsc hM1 hM2 hM3
    have hrow : row.length = n := hrows row (by simp)
    have hrv' : σ.rv = (encNats row).reverse ++ ((encNats R.flatten).reverse ++ r) := by
      rw [hrv]; simp [encNats_append']
    have e1 := runs_oldBody M K n row hrow _ (noDig_encNats _ r hr) σ hrv' hK hN hC2 hC3 hsc hM1 hM2 hM3
    have e2 := ih (fun row' h' => hrows row' (by simp [h'])) { σ with C := σ.C.tail, rv := (encNats R.flatten).reverse ++ r, out := encNats row ++ encNats (List.replicate K 1) ++ σ.out }
      (by simp [hC]) rfl hK hN hC2 hC3 hsc
      (by simp only; rw [hrv'] at hM1; simp at hM1 ⊢; omega) hM2 hM3
    refine ((Runs.loopT (by simp [hd, Regs.get, hC]) e1 e2).congr ?_).mono ?_
    · simp [List.flatMap_append, encNats_append', List.append_assoc]
    · simp only [List.length_append, List.length_singleton]
      nlinarith

end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity

/-! ## phase A: split off the threshold `y` -/

def mA : Prog := .seq (mvProg .inp .rv) (.seq (popProg .rv) (mvwProg .rv .Yb isDigB))

lemma runs_mA (σ : Regs) (pre : List ℕ) (y : ℕ) (h : σ.inp = encNats (pre ++ [y]))
    (hrv : σ.rv = []) (hYb : σ.Yb = []) :
    Runs mA σ { σ with inp := [], rv := (encNats pre).reverse, Yb := enc (Nat.bits y) }
      (7 * σ.inp.length + 4) := by
  have e1 := runs_mv .inp .rv (by decide) σ
  set σ1 := (σ.set .inp []).set .rv ((σ.get .inp).reverse ++ σ.get .rv) with hσ1
  have e2 := runs_pop .rv σ1
  set σ2 := σ1.set .rv (σ1.get .rv).tail with hσ2
  have h2 : σ2.get .rv = (enc (Nat.bits y)).reverse ++ (encNats pre).reverse := by
    simp [hσ2, hσ1, Regs.get, Regs.set, h, hrv, encNats_append', encNat_enc, encNats_cons', encNats_nil]
  have e3 := runs_mvw .rv .Yb (by decide) isDigB _ σ2 h2
  have hdig : ∀ x ∈ (enc (Nat.bits y)).reverse, isDigB x = true := by
    intro x hx; exact isDigB_enc _ x (List.mem_reverse.mp hx)
  have hnd : NoDig (encNats pre).reverse := by
    have := noDig_encNats pre [] noDig_nil; simpa using this
  rw [List.takeWhile_append_of_pos hdig, List.dropWhile_append_of_pos hdig,
    takeWhile_noDig _ hnd, dropWhile_noDig _ hnd, List.append_nil, List.reverse_reverse] at e3
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ2, hσ1, hYb]
  · have : ((enc (Nat.bits y)).reverse ++ (encNats pre).reverse).length + 1 = σ.inp.length := by
      rw [h]; simp [encNats_append', encNat_enc, encNats_cons', encNats_nil]; omega
    have h1 : (σ.get .inp).length = σ.inp.length := rfl
    omega

/-! ## phase B: the numbers `y'' = min y (p n)`, `n'' = (n - 1) y''`, `n + n''`, and `y` -/

def mB1 (pstar : ℕ) : Prog :=
  .seq (pushL .C (List.replicate pstar .one))
    (.seq (repProg .Nu .G .C .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fuelLoopG .Yb .G .Yu))

lemma runs_mB1 (pstar n y M : ℕ) (σ : Regs) (hN : σ.Nu = List.replicate n .one)
    (hYb : σ.Yb = enc (Nat.bits y)) (hC : σ.C = []) (hG : σ.G = []) (hYu : σ.Yu = [])
    (hsc : σ.sc = []) (hT : σ.T = []) (hM1 : n ≤ M) (hM2 : pstar ≤ M) (hM3 : (Nat.bits y).length ≤ M) :
    Runs (mB1 pstar) σ { σ with Yb := enc (Nat.bits (y - min y (pstar * n))), G := List.replicate (pstar * n - min y (pstar * n)) .one, Yu := List.replicate (min y (pstar * n)) .one } (30 * (M + 1) ^ 3) := by
  have e1 := runs_pushL .C (List.replicate pstar .one) σ
  set σ1 := σ.set .C ((List.replicate pstar BSym.one).reverse ++ σ.get .C) with hσ1
  have e2 := runs_rep .Nu .G .C .sc (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ1 (by simp [hσ1, Regs.get, Regs.set, hsc])
  have h1C : σ1.get .C = List.replicate pstar .one := by simp [hσ1, Regs.get, Regs.set, hC]
  have h1N : σ1.get .Nu = List.replicate n .one := by simp [hσ1, Regs.get, Regs.set, hN]
  have h1G : σ1.get .G = [] := by simp [hσ1, Regs.get, Regs.set, hG]
  rw [h1C, h1N, h1G, List.length_replicate, List.length_replicate, flatten_rep_one, List.append_nil] at e2
  set σ2 := (σ1.set .C []).set .G (List.replicate (pstar * n) .one) with hσ2
  have e3 := runs_fuelG .Yb .G .Yu (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (pstar * n) y σ2 (by simp [hσ2, hσ1, Regs.get, Regs.set, hYb])
    (by simp [hσ2, Regs.get, Regs.set]) (by simp [hσ2, hσ1, Regs.get, Regs.set, hT])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ2, hσ1, hC, hYu]
  · have hm : min y (pstar * n) ≤ M * M := le_trans (min_le_right _ _) (Nat.mul_le_mul hM2 hM1)
    have h4 : min y (pstar * n) * (6 * (Nat.bits y).length + 22) ≤ M * M * (6 * M + 22) :=
      Nat.mul_le_mul hm (by omega)
    have h5 : (6 * n + 7) * pstar ≤ (6 * M + 7) * M := Nat.mul_le_mul (by omega) hM2
    simp only [List.length_replicate]
    nlinarith

def mB2 : Prog :=
  .seq (copyProg .Nu .C .sc) (.seq (popProg .C)
    (.seq (repProg .Yu .Ku .C .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (.seq (copyProg .Nu .NN .sc) (copyProg .Ku .NN .sc))))

lemma runs_mB2 (n y2 M : ℕ) (σ : Regs) (hN : σ.Nu = List.replicate n .one)
    (hYu : σ.Yu = List.replicate y2 .one) (hC : σ.C = []) (hK : σ.Ku = []) (hNN : σ.NN = [])
    (hsc : σ.sc = []) (hM1 : n ≤ M) (hM2 : y2 ≤ M) (hM3 : (n - 1) * y2 ≤ M) :
    Runs mB2 σ { σ with Ku := List.replicate ((n - 1) * y2) .one, NN := List.replicate ((n - 1) * y2 + n) .one } (30 * (M + 1) ^ 2) := by
  have e1 := runs_copy .Nu .C .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
  set σ1 := σ.set .C (σ.get .Nu ++ σ.get .C) with hσ1
  have e2 := runs_pop .C σ1
  set σ2 := σ1.set .C (σ1.get .C).tail with hσ2
  have e3 := runs_rep .Yu .Ku .C .sc (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ2 (by simp [hσ2, hσ1, Regs.get, Regs.set, hsc])
  have h2C : σ2.get .C = List.replicate (n - 1) .one := by
    simp [hσ2, hσ1, Regs.get, Regs.set, hN, hC]
  have h2Y : σ2.get .Yu = List.replicate y2 .one := by simp [hσ2, hσ1, Regs.get, Regs.set, hYu]
  have h2K : σ2.get .Ku = [] := by simp [hσ2, hσ1, Regs.get, Regs.set, hK]
  rw [h2C, h2Y, h2K, List.length_replicate, List.length_replicate, flatten_rep_one, List.append_nil] at e3
  set σ3 := (σ2.set .C []).set .Ku (List.replicate ((n - 1) * y2) .one) with hσ3
  have e4 := runs_copy .Nu .NN .sc (by decide) (by decide) (by decide) σ3
    (by simp [hσ3, hσ2, hσ1, Regs.get, Regs.set, hsc])
  set σ4 := σ3.set .NN (σ3.get .Nu ++ σ3.get .NN) with hσ4
  have e5 := runs_copy .Ku .NN .sc (by decide) (by decide) (by decide) σ4
    (by simp [hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hsc])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr ?_).mono ?_
  · apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ4, hσ3, hσ2, hσ1, hC, hN, hNN, ← List.replicate_add]
  · have h5 : (6 * y2 + 7) * (n - 1) ≤ (6 * M + 7) * M := Nat.mul_le_mul (by omega) (by omega)
    simp [hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hN]
    nlinarith

def mB3 : Prog :=
  .seq (copyProg .Yu .C .sc)
    (.seq (repProg .NN .Yv .C .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (.seq (copyProg .Ku .C .sc) triLoop))

lemma runs_mB3 (y2 N K M : ℕ) (σ : Regs) (hYu : σ.Yu = List.replicate y2 .one)
    (hNN : σ.NN = List.replicate N .one) (hK : σ.Ku = List.replicate K .one) (hC : σ.C = [])
    (hYv : σ.Yv = []) (hA2 : σ.A2 = []) (hsc : σ.sc = []) (hM1 : y2 ≤ M) (hM2 : N ≤ M) (hM3 : K ≤ M) :
    Runs mB3 σ { σ with Yv := List.replicate (K * (K + 1) / 2 + y2 * N) .one, A2 := List.replicate K .one } (30 * (M + 1) ^ 2) := by
  have e1 := runs_copy .Yu .C .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
  rw [show σ.get .Yu = List.replicate y2 .one from hYu, show σ.get .C = [] from hC,
    List.append_nil] at e1
  set σ1 := σ.set .C (List.replicate y2 .one) with hσ1
  have e2 := runs_rep .NN .Yv .C .sc (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ1 (by simp [hσ1, Regs.get, Regs.set, hsc])
  rw [show σ1.get .C = List.replicate y2 .one from Regs.get_set_self _ _ _,
    show σ1.get .NN = List.replicate N .one from hNN, show σ1.get .Yv = [] from hYv,
    List.length_replicate, List.length_replicate, flatten_rep_one, List.append_nil] at e2
  set σ2 := (σ1.set .C []).set .Yv (List.replicate (y2 * N) .one) with hσ2
  have e3 := runs_copy .Ku .C .sc (by decide) (by decide) (by decide) σ2
    (by simp [hσ2, hσ1, Regs.get, Regs.set, hsc])
  rw [show σ2.get .Ku = List.replicate K .one from hK, show σ2.get .C = [] by
    simp [hσ2, Regs.get, Regs.set], List.append_nil, List.length_replicate] at e3
  set σ3 := σ2.set .C (List.replicate K .one) with hσ3
  have e4 := runs_triLoop M K 0 σ3 (by simp [hσ3, Regs.set]) (by simp [hσ3, hσ2, hσ1, Regs.set, hA2])
    (by simp [hσ3, hσ2, hσ1, Regs.set, hsc]) (by omega)
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ3, hσ2, hσ1, hC]
  · have h5 : (6 * N + 7) * y2 ≤ (6 * M + 7) * M := Nat.mul_le_mul (by omega) hM1
    have h6 : K * (6 * M + 20) ≤ M * (6 * M + 20) := Nat.mul_le_mul_right _ hM3
    simp only [List.length_replicate]
    nlinarith

/-! ## phases D–F -/

def mD : Prog := .seq (copyProg .Ku .C .sc) (.seq (copyProg .NN .Z .sc) newLoop)

lemma runs_mD (K N M : ℕ) (σ : Regs) (hK : σ.Ku = List.replicate K .one)
    (hNN : σ.NN = List.replicate N .one) (hC : σ.C = []) (hZ : σ.Z = []) (hO : σ.O = [])
    (hC2 : σ.C2 = []) (hC3 : σ.C3 = []) (hsc : σ.sc = []) (hKN : K ≤ N) (hM : N ≤ M) :
    Runs mD σ { σ with Z := List.replicate (N - K) .one, O := List.replicate K .one, out := newBlk 0 N K ++ σ.out } (30 * (M + 1) ^ 2) := by
  have e1 := runs_copy .Ku .C .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
  rw [show σ.get .Ku = List.replicate K .one from hK, show σ.get .C = [] from hC,
    List.append_nil, List.length_replicate] at e1
  set σ1 := σ.set .C (List.replicate K .one) with hσ1
  have e2 := runs_copy .NN .Z .sc (by decide) (by decide) (by decide) σ1 (by simp [hσ1, Regs.get, Regs.set, hsc])
  rw [show σ1.get .NN = List.replicate N .one from hNN, show σ1.get .Z = [] from hZ,
    List.append_nil, List.length_replicate] at e2
  set σ2 := σ1.set .Z (List.replicate N .one) with hσ2
  have e3 := runs_newLoop M K 0 N σ2 (by simp [hσ2, hσ1, Regs.set]) (by simp [hσ2, hσ1, Regs.set, hO])
    (by simp [hσ2, Regs.set]) (by simp [hσ2, hσ1, Regs.set, hC2]) (by simp [hσ2, hσ1, Regs.set, hC3])
    (by simp [hσ2, hσ1, Regs.set, hsc]) hKN (by omega)
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ2, hσ1, hC]
  · have h6 : K * (16 * M + 22) ≤ M * (16 * M + 22) := Nat.mul_le_mul_right _ (by omega)
    nlinarith

def mE : Prog := .seq (copyProg .Nu .C .sc) oldLoop

lemma runs_mE (M K n : ℕ) (r : List BSym) (hr : NoDig r) (ms : List ℕ) (R : List (List ℕ))
    (hR : R.flatten = ms) (hRl : R.length = n) (hrows : ∀ row ∈ R, row.length = n) (σ : Regs)
    (hrv : σ.rv = (encNats ms).reverse ++ r) (hK : σ.Ku = List.replicate K .one)
    (hN : σ.Nu = List.replicate n .one) (hC : σ.C = []) (hC2 : σ.C2 = []) (hC3 : σ.C3 = [])
    (hsc : σ.sc = []) (hM1 : σ.rv.length ≤ M) (hM2 : n ≤ M) (hM3 : K ≤ M) :
    Runs mE σ { σ with rv := r, out := encNats (R.flatMap (fun row => row ++ List.replicate K 1)) ++ σ.out }
      (40 * (M + 1) ^ 3) := by
  have e1 := runs_copy .Nu .C .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
  rw [show σ.get .Nu = List.replicate n .one from hN, show σ.get .C = [] from hC,
    List.append_nil, List.length_replicate] at e1
  set σ1 := σ.set .C (List.replicate n .one) with hσ1
  have e2 := runs_oldLoop M K n r hr R hrows σ1 (by simp [hσ1, Regs.set, hRl])
    (by simp [hσ1, Regs.set, hrv, hR]) (by simp [hσ1, Regs.set, hK]) (by simp [hσ1, Regs.set, hN])
    (by simp [hσ1, Regs.set, hC2]) (by simp [hσ1, Regs.set, hC3]) (by simp [hσ1, Regs.set, hsc])
    (by simpa [hσ1, Regs.set] using hM1) hM2 hM3
  refine ((e1.seq e2).congr ?_).mono ?_
  · apply Regs.ext_get; funext i
    cases i <;> simp [Regs.get, Regs.set, hσ1, hC]
  · rw [hRl]
    have h6 : n * (3 * M * M + 30 * M + 22) ≤ M * (3 * M * M + 30 * M + 22) :=
      Nat.mul_le_mul_right _ hM2
    have h7 : (M + 1) ^ 3 = M * M * M + 3 * (M * M) + 3 * M + 1 := by ring
    have h8 : M * (3 * M * M + 30 * M + 22) = 3 * (M * M * M) + 30 * (M * M) + 22 * M := by ring
    rw [h7]; rw [h8] at h6
    nlinarith [Nat.zero_le (M * M * M), Nat.zero_le (M * M)]

def mF : Prog :=
  .seq (copyProg .Ku .C .sc) (.seq (constLoop .C .out [.sep, .one]) (.seq (copyProg .Nu .C .sc)
    (.seq (tokLoop .C) (.seq tok1 (emitU .NN)))))

lemma runs_mF (M K n N m : ℕ) (ps : List ℕ) (hps : ps.length = n) (σ : Regs)
    (hrv : σ.rv = (encNats ([n, m] ++ ps)).reverse) (hK : σ.Ku = List.replicate K .one)
    (hN : σ.Nu = List.replicate n .one) (hNN : σ.NN = List.replicate N .one) (hC : σ.C = [])
    (hsc : σ.sc = []) (hBc : σ.Bc = []) (hT : σ.T = []) (hA : σ.A = [])
    (hM1 : σ.rv.length ≤ M) (hM2 : n ≤ M) (hM3 : K ≤ M) (hM4 : N ≤ M) :
    ∃ τ, Runs mF σ τ (60 * (M + 1) ^ 2) ∧
      τ.out = encNat N ++ encNat m ++ encNats ps ++ encNats (List.replicate K 1) ++ σ.out := by
  have e1 := runs_copy .Ku .C .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
  rw [show σ.get .Ku = List.replicate K .one from hK, show σ.get .C = [] from hC,
    List.append_nil, List.length_replicate] at e1
  set σ1 := σ.set .C (List.replicate K .one) with hσ1
  have e2 := runs_constLoop .C .out (by decide) [.sep, .one] K σ1 (Regs.get_set_self _ _ _)
  rw [ones_tokens] at e2
  set σ2 := (σ1.set .C []).set .out (encNats (List.replicate K 1) ++ σ1.get .out) with hσ2
  have e3 := runs_copy .Nu .C .sc (by decide) (by decide) (by decide) σ2
    (by simp [hσ2, hσ1, Regs.get, Regs.set, hsc])
  rw [show σ2.get .Nu = List.replicate n .one from hN, show σ2.get .C = [] by
    simp [hσ2, Regs.get, Regs.set], List.append_nil, List.length_replicate] at e3
  set σ3 := σ2.set .C (List.replicate n .one) with hσ3
  have hnd : NoDig (encNats [n, m]).reverse := by
    have := noDig_encNats [n, m] [] noDig_nil; simpa using this
  have hsplit : (encNats ([n, m] ++ ps)).reverse = (encNats ps).reverse ++ (encNats [n, m]).reverse := by
    rw [encNats_append', List.reverse_append]
  have e4 := runs_tokLoop .C (by decide) (by decide) _ hnd ps σ3 (by simp [hσ3, Regs.get, Regs.set, hps])
    (by simp only [hσ3, hσ2, hσ1, Regs.get, Regs.set]; rw [hrv, hsplit])
  set σ4 := ((σ3.set .C []).set .rv (encNats [n, m]).reverse).set .out (encNats ps ++ σ3.out) with hσ4
  have hnd2 : NoDig (encNat n).reverse := by
    have := noDig_encNats [n] [] noDig_nil; simpa [encNats_cons', encNats_nil] using this
  have e5 := runs_tok1 σ4 m _ hnd2 (by simp [hσ4, Regs.get, Regs.set, encNats_cons', encNats_nil])
  set σ5 := (σ4.set .rv (encNat n).reverse).set .out (encNat m ++ σ4.out) with hσ5
  have e6 := runs_emitU .NN (by decide) (by decide) (by decide) (by decide) N σ5
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hNN])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hBc])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hT])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, hA])
  refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).mono ?_, ?_⟩
  · have h4 : σ4.rv.length ≤ σ.rv.length := by
      simp only [hσ4, Regs.get, Regs.set]; rw [hrv, hsplit]; simp
    have h3 : σ3.rv = σ.rv := by simp [hσ3, hσ2, hσ1, Regs.get, Regs.set]
    rw [h3]
    simp only [List.length_cons, List.length_nil, hps]
    have h6 : n * (3 * σ.rv.length + 8) ≤ M * (3 * M + 8) := Nat.mul_le_mul hM2 (by omega)
    have h7 : N * (6 * N + 14) ≤ M * (6 * M + 14) := Nat.mul_le_mul hM4 (by omega)
    have h8 : K * (2 * 2 + 6) ≤ M * 10 := Nat.mul_le_mul hM3 le_rfl
    nlinarith
  · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Regs.get, Regs.set, List.append_assoc]

end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity

/-! ## the whole main phase -/

def mainP (pstar : ℕ) : Prog :=
  .seq mA (.seq (mB1 pstar) (.seq mB2 (.seq mB3 (.seq (emitU .Yv) (.seq mD (.seq mE mF))))))

def progAll (pstar : ℕ) : Prog := .seq valProg (gate (mainP pstar))

/-- the rows of the matrix entries `ms` -/
def rowsOf (n : ℕ) (ms : List ℕ) : List (List ℕ) :=
  (List.range n).map (fun j => (List.range n).map (fun k => ms.getD (j * n + k) 0))

lemma flat_range (g : ℕ → ℕ) (b : ℕ) : ∀ a : ℕ,
    ((List.range a).map (fun j => (List.range b).map (fun k => g (j * b + k)))).flatten =
      (List.range (a * b)).map g := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih, Nat.succ_mul, List.range_add,
      List.map_append]
    simp [List.map_map, Function.comp_def]

lemma rowsOf_flatten (n : ℕ) (ms : List ℕ) (h : ms.length = n * n) : (rowsOf n ms).flatten = ms := by
  unfold rowsOf
  rw [flat_range (fun i => ms.getD i 0) n n]
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

lemma rowsOf_length (n : ℕ) (ms : List ℕ) : (rowsOf n ms).length = n := by simp [rowsOf]

lemma rowsOf_rows (n : ℕ) (ms : List ℕ) : ∀ row ∈ rowsOf n ms, row.length = n := by
  intro row h; simp [rowsOf] at h; obtain ⟨j, _, rfl⟩ := h; simp

/-- the machine output -/
def outSym (pstar n m : ℕ) (ps ms : List ℕ) (y : ℕ) : List BSym :=
  let y2 := min y (pstar * n)
  let K := (n - 1) * y2
  encNat (K + n) ++ encNat m ++ encNats ps ++ encNats (List.replicate K 1) ++
    encNats ((rowsOf n ms).flatMap (fun row => row ++ List.replicate K 1)) ++
    newBlk 0 (K + n) K ++ encNat (K * (K + 1) / 2 + y2 * (K + n))

lemma len_tuple (n m y : ℕ) (ps ms : List ℕ) (hps : ps.length = n) (hms : ms.length = n * n) :
    n * n + n + 3 ≤ (encNats ([n, m] ++ ps ++ ms ++ [y])).length := by
  have h1 := length_le_encNats ([n, m] ++ ps ++ ms ++ [y])
  have h2 : ([n, m] ++ ps ++ ms ++ [y]).length = n * n + n + 3 := by simp [hps, hms]; omega
  omega

lemma bound_arith (M Y a : ℕ) (hY : Y ≤ 2 * (M + 1) ^ 2) (ha : a ≤ 7 * M + 4) :
    a + 1 + (30 * (M + 1) ^ 3 + 1 + (30 * (M + 1) ^ 2 + 1 + (30 * (M + 1) ^ 2 + 1 +
      (Y * (6 * Y + 14) + 6 * Y + 12 + 1 + (30 * (M + 1) ^ 2 + 1 + (40 * (M + 1) ^ 3 + 1 +
        60 * (M + 1) ^ 2)))))) ≤ 400 * ((M + 1) ^ 4) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (M + 1) ^ 2 := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact Nat.one_le_pow _ _ (by omega)
  have hMQ : M + 1 ≤ Q := by rw [hQ]; nlinarith
  have h3 : (M + 1) ^ 3 ≤ Q * Q := by rw [hQ]; nlinarith
  have h4 : (M + 1) ^ 4 = Q * Q := by rw [hQ]; ring
  rw [← hQ] at hY ⊢
  have hYY : Y * (6 * Y + 14) ≤ (2 * Q) * (6 * (2 * Q) + 14) := Nat.mul_le_mul hY (by omega)
  rw [h4]
  nlinarith

theorem runs_mainP (pstar n m y : ℕ) (ps ms : List ℕ) (hps : ps.length = n) (hms : ms.length = n * n)
    (w : List BSym) (hw : w = encNats ([n, m] ++ ps ++ ms ++ [y])) :
    ∃ τ, Runs (mainP pstar) { S0 w with Nu := List.replicate n .one } τ
      (400 * ((pstar + 1) * (w.length + 1) + 1) ^ 4) ∧ τ.out = outSym pstar n m ps ms y := by
  set M := (pstar + 1) * (w.length + 1) with hM
  set y2 := min y (pstar * n) with hy2
  set K := (n - 1) * y2 with hK
  have hlen := len_tuple n m y ps ms hps hms
  rw [← hw] at hlen
  have hnw : n ≤ w.length := by nlinarith
  have hnnw : n * n ≤ w.length := by omega
  have hwM : w.length ≤ M := by rw [hM]; nlinarith
  have hpM : pstar ≤ M := by rw [hM]; nlinarith
  have hnM : n ≤ M := le_trans hnw hwM
  have hy2M : y2 ≤ M := by
    have : y2 ≤ pstar * n := min_le_right _ _
    have : pstar * n ≤ pstar * w.length := Nat.mul_le_mul_left _ hnw
    rw [hM]; nlinarith
  have hKM : K ≤ pstar * w.length := by
    have h1 : y2 ≤ pstar * n := min_le_right _ _
    have h2 : K ≤ n * (pstar * n) := Nat.mul_le_mul (by omega) h1
    have h3 : n * (pstar * n) = pstar * (n * n) := by ring
    have h4 : pstar * (n * n) ≤ pstar * w.length := Nat.mul_le_mul_left _ hnnw
    omega
  have hKM' : K ≤ M := by rw [hM]; nlinarith
  have hNM : K + n ≤ M := by rw [hM]; nlinarith
  have hbits : (Nat.bits y).length ≤ M := by
    have h1 : (encNat y).length ≤ w.length := by
      rw [hw]; simp [encNats_append', encNats_cons', encNats_nil]; omega
    have h2 := len_enc_bits_le_encNat y
    omega
  -- phase A
  set σ0 : Regs := { S0 w with Nu := List.replicate n .one } with hσ0
  have eA := runs_mA σ0 ([n, m] ++ ps ++ ms) y (by simp [hσ0, S0, hw]) rfl rfl
  set σA : Regs := { σ0 with inp := [], rv := (encNats ([n, m] ++ ps ++ ms)).reverse, Yb := enc (Nat.bits y) } with hσA
  -- phase B
  have eB1 := runs_mB1 pstar n y M σA rfl rfl rfl rfl rfl rfl rfl hnM hpM hbits
  set σB1 : Regs := { σA with Yb := enc (Nat.bits (y - min y (pstar * n))), G := List.replicate (pstar * n - min y (pstar * n)) .one, Yu := List.replicate (min y (pstar * n)) .one } with hσB1
  have eB2 := runs_mB2 n y2 M σB1 rfl rfl rfl rfl rfl rfl hnM hy2M hKM'
  set σB2 : Regs := { σB1 with Ku := List.replicate ((n - 1) * y2) .one, NN := List.replicate ((n - 1) * y2 + n) .one } with hσB2
  have eB3 := runs_mB3 y2 (K + n) K M σB2 rfl rfl rfl rfl rfl rfl rfl hy2M hNM hKM'
  set σB3 : Regs := { σB2 with Yv := List.replicate (K * (K + 1) / 2 + y2 * (K + n)) .one, A2 := List.replicate K .one } with hσB3
  -- phase C
  have eC := runs_emitU .Yv (by decide) (by decide) (by decide) (by decide) _ σB3 rfl rfl rfl rfl
  set σC := (σB3.set .Yv []).set .out (encNat (K * (K + 1) / 2 + y2 * (K + n)) ++ σB3.out) with hσC
  -- phase D
  have eD := runs_mD K (K + n) M σC (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by omega) hNM
  set σD : Regs := { σC with Z := List.replicate (K + n - K) .one, O := List.replicate K .one, out := newBlk 0 (K + n) K ++ σC.out } with hσD
  -- phase E
  have hndE : NoDig (encNats ([n, m] ++ ps)).reverse := by
    have := noDig_encNats ([n, m] ++ ps) [] noDig_nil; simpa using this
  have hrvE : σD.rv = (encNats ms).reverse ++ (encNats ([n, m] ++ ps)).reverse := by
    simp only [hσD, hσC, Regs.set]
    show (encNats ([n, m] ++ ps ++ ms)).reverse = _
    rw [encNats_append', List.reverse_append]
  have hrvM : σD.rv.length ≤ M := by
    rw [hrvE]
    have : (encNats ([n, m] ++ ps ++ ms ++ [y])).length = (encNats ms).length +
        (encNats ([n, m] ++ ps)).length + (encNat y).length := by
      simp only [encNats_append', List.length_append, encNats_cons', encNats_nil, List.append_nil]; omega
    rw [hw] at hwM
    simp only [List.length_append, List.length_reverse]; omega
  have eE := runs_mE M K n _ hndE ms (rowsOf n ms) (rowsOf_flatten n ms hms) (rowsOf_length n ms)
    (rowsOf_rows n ms) σD hrvE (by simp [hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) hrvM hnM hKM'
  set σE : Regs := { σD with rv := (encNats ([n, m] ++ ps)).reverse, out := encNats ((rowsOf n ms).flatMap (fun row => row ++ List.replicate K 1)) ++ σD.out } with hσE
  -- phase F
  obtain ⟨τ, eF, hF⟩ := runs_mF M K n (K + n) m ps hps σE rfl (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK]) (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by simp [hσE, hσD, hσC, hσB3, hσB2, hσB1, hσA, hσ0, Regs.set, S0, Regs.empty, ← hK])
    (by have := hrvM; rw [hrvE] at this; simp only [hσE]
        simp only [List.length_append, List.length_reverse] at this ⊢; omega) hnM hKM' hNM
  have hY : K * (K + 1) / 2 + y2 * (K + n) ≤ 2 * (M + 1) ^ 2 := by
    have h1 : K * (K + 1) / 2 ≤ K * (K + 1) := Nat.div_le_self _ _
    have h2 : K * (K + 1) ≤ M * (M + 1) := Nat.mul_le_mul hKM' (by omega)
    have h3 : y2 * (K + n) ≤ M * M := Nat.mul_le_mul hy2M hNM
    nlinarith
  refine ⟨τ, (eA.seq (eB1.seq (eB2.seq (eB3.seq (eC.seq (eD.seq (eE.seq eF))))))).mono ?_, ?_⟩
  · have hA : 7 * σ0.inp.length + 4 ≤ 7 * M + 4 := by simp [hσ0, S0]; omega
    exact bound_arith M _ _ hY hA
  · have hoE : σE.out = encNats ((rowsOf n ms).flatMap (fun row => row ++ List.replicate K 1)) ++ σD.out := rfl
    have hoD : σD.out = newBlk 0 (K + n) K ++ σC.out := rfl
    have hoC : σC.out = encNat (K * (K + 1) / 2 + y2 * (K + n)) ++ σB3.out := rfl
    have hoB : σB3.out = [] := rfl
    rw [hF, hoE, hoD, hoC, hoB]
    simp only [outSym, List.append_assoc, List.append_nil]
    rfl

end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity

/-! ## the reduction function -/

def TupOK (w : List BSym) (n m : ℕ) (ps ms : List ℕ) (y : ℕ) : Prop :=
  w = encNats ([n, m] ++ ps ++ ms ++ [y]) ∧ ps.length = n ∧ ms.length = n * n

lemma tup_unique {w : List BSym} {n m y n' m' y' : ℕ} {ps ms ps' ms' : List ℕ}
    (h : TupOK w n m ps ms y) (h' : TupOK w n' m' ps' ms' y') :
    n = n' ∧ m = m' ∧ ps = ps' ∧ ms = ms' ∧ y = y' := by
  obtain ⟨hw, hp, hm⟩ := h
  obtain ⟨hw', hp', hm'⟩ := h'
  have hL := encNats_inj (hw.symm.trans hw')
  simp only [List.cons_append, List.nil_append, List.cons.injEq, List.append_assoc] at hL
  obtain ⟨h1, h2, hL⟩ := hL
  subst h1; subst h2
  obtain ⟨h3, hL⟩ := List.append_inj hL (by rw [hp, hp'])
  obtain ⟨h4, hL⟩ := List.append_inj hL (by rw [hm, hm'])
  simp at hL
  exact ⟨rfl, rfl, h3, h4, hL⟩

def Tup : Type := ℕ × ℕ × List ℕ × List ℕ × ℕ

def TupOK' (w : List BSym) (t : Tup) : Prop := TupOK w t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

open Classical in
noncomputable def Fw (pstar : ℕ) (w : List BSym) : List BSym :=
  if h : ∃ t : Tup, TupOK' w t then
    outSym pstar h.choose.1 h.choose.2.1 h.choose.2.2.1 h.choose.2.2.2.1 h.choose.2.2.2.2
  else []

lemma Fw_tup (pstar : ℕ) {w : List BSym} {n m y : ℕ} {ps ms : List ℕ} (h : TupOK w n m ps ms y) :
    Fw pstar w = outSym pstar n m ps ms y := by
  have hex : ∃ t : Tup, TupOK' w t := ⟨(n, m, ps, ms, y), h⟩
  unfold Fw
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3, h4, h5⟩ := tup_unique hex.choose_spec h
  rw [h1, h2, h3, h4, h5]

lemma Fw_bad (pstar : ℕ) {w : List BSym} (h : ∀ n m ps ms y, ¬ TupOK w n m ps ms y) :
    Fw pstar w = [] := by
  unfold Fw
  rw [dif_neg]
  rintro ⟨t, ht⟩
  exact h _ _ _ _ _ ht

lemma valid_iff_tup (w : List BSym) :
    (∃ L, w = encNats L ∧ ValidL L) ↔ ∃ n m ps ms y, TupOK w n m ps ms y := by
  constructor
  · rintro ⟨L, hw, hv⟩
    unfold ValidL at hv
    match L, hv with
    | a :: b :: rest, hv =>
      simp only [List.headD_cons, List.length_cons] at hv
      have hr : rest.length = a * a + a + 1 := by omega
      obtain ⟨q, hq⟩ : ∃ q, q = a * a := ⟨_, rfl⟩
      rw [← hq] at hr
      refine ⟨a, b, rest.take a, (rest.drop a).take (a * a), ((rest.drop a).drop (a * a)).headD 0,
        ?_, by simp [hr]; omega, by rw [← hq]; simp [hr]; omega⟩
      rw [hw]
      congr 1
      have hlast : (rest.drop a).drop (a * a) = [((rest.drop a).drop (a * a)).headD 0] := by
        have hl : ((rest.drop a).drop (a * a)).length = 1 := by rw [← hq]; simp [hr]; omega
        match hx : (rest.drop a).drop (a * a), hl with
        | [x], _ => rfl
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      congr 2
      conv_lhs => rw [← List.take_append_drop a rest, ← List.take_append_drop (a * a) (rest.drop a), hlast]
  · rintro ⟨n, m, ps, ms, y, hw, hp, hm⟩
    refine ⟨_, hw, ?_⟩
    unfold ValidL
    simp [hp, hm]; ring

lemma valid_head {w : List BSym} {L : List ℕ} {n m y : ℕ} {ps ms : List ℕ} (hL : w = encNats L)
    (h : TupOK w n m ps ms y) : L.headD 0 = n := by
  have := encNats_inj (hL.symm.trans h.1)
  rw [this]; rfl

def bigB (pstar L : ℕ) : ℕ := 200 * (L + 1) ^ 2 + 1 + (400 * ((pstar + 1) * (L + 1) + 1) ^ 4 + 1)

theorem main_spec (pstar : ℕ) (w : List BSym) :
    ∃ τ, Runs (progAll pstar) (S0 w) τ (bigB pstar w.length) ∧ τ.out = Fw pstar w := by
  obtain ⟨τ1, e1, h1a, h1b⟩ := runs_val w
  by_cases hv : ∃ L, w = encNats L ∧ ValidL L
  · obtain ⟨n, m, ps, ms, y, ht⟩ := (valid_iff_tup w).1 hv
    obtain ⟨L, hL, hvL⟩ := hv
    have hτ1 := h1a L hL hvL
    rw [valid_head hL ht] at hτ1
    subst hτ1
    obtain ⟨τ, e2, h2⟩ := runs_mainP pstar n m y ps ms ht.2.1 ht.2.2 w ht.1
    refine ⟨τ, (e1.seq (runs_gate_ok (by simp [S0, Regs.empty]) e2)).mono ?_, ?_⟩
    · unfold bigB; have := Nat.one_le_pow 4 ((pstar + 1) * (w.length + 1) + 1) (by omega); omega
    · rw [h2, Fw_tup pstar ht]
  · obtain ⟨hb, ho⟩ := h1b hv
    refine ⟨τ1, (e1.seq (runs_gate_skip hb)).mono ?_, ?_⟩
    · unfold bigB; have := Nat.one_le_pow 4 ((pstar + 1) * (w.length + 1) + 1) (by omega); omega
    · rw [ho, Fw_bad]
      intro n m ps ms y ht
      exact hv ((valid_iff_tup w).2 ⟨n, m, ps, ms, y, ht⟩)

lemma S0_get (w : List BSym) : (S0 w).get = fun j => if j = .inp then w else [] := by
  funext j; cases j <;> rfl

theorem Fw_poly (pstar : ℕ) : PolyTimeComputable (Fw pstar) := by
  obtain ⟨k, hk⟩ := polynomial_absorb (400 * (pstar + 2) ^ 4 + 200) 4 2
  apply stack_program_polytime (progAll pstar) .inp .out (Fw pstar) k
  intro w
  obtain ⟨τ, ⟨n, hn, e⟩, hout⟩ := main_spec pstar w
  refine ⟨τ.get, n, ?_, by rw [← S0_get]; exact e, hout⟩
  have hb : bigB pstar w.length ≤ (400 * (pstar + 2) ^ 4 + 200) * (w.length + 1) ^ 4 + 2 := by
    unfold bigB
    have h1 : (pstar + 1) * (w.length + 1) + 1 ≤ (pstar + 2) * (w.length + 1) := by nlinarith
    have h2 : ((pstar + 1) * (w.length + 1) + 1) ^ 4 ≤ ((pstar + 2) * (w.length + 1)) ^ 4 :=
      Nat.pow_le_pow_left h1 4
    have h3 : (w.length + 1) ^ 2 ≤ (w.length + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [mul_pow] at h2
    nlinarith
  have := hk w.length
  omega

end PCR


set_option autoImplicit false

namespace PCR

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.PrecChain

/-! ## lists -/

lemma ofFn_val' {α : Type} (n : ℕ) (h : ℕ → α) :
    List.ofFn (fun v : Fin n => h v.val) = (List.range n).map h := by
  apply List.ext_getElem <;> simp

lemma flatten_getD (n : ℕ) : ∀ (Rs : List (List ℕ)), (∀ r ∈ Rs, r.length = n) → ∀ j k,
    j < Rs.length → k < n → Rs.flatten.getD (j * n + k) 0 = (Rs.getD j []).getD k 0 := by
  intro Rs
  induction Rs with
  | nil => intro _ j k h; simp at h
  | cons r Rs ih =>
    intro hr j k hj hk
    have hrl : r.length = n := hr r (by simp)
    rw [List.flatten_cons]
    cases j with
    | zero =>
      simp only [zero_mul, zero_add, List.getD_cons_zero]
      rw [List.getD_append _ _ _ _ (by omega)]
    | succ j =>
      simp only [List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by rw [hrl]; nlinarith)]
      rw [show (j + 1) * n + k - r.length = j * n + k by rw [hrl]; ring_nf; omega]
      exact ih (fun r' h' => hr r' (by simp [h'])) j k (by simp at hj; omega) hk

lemma rowsOf_inv (n : ℕ) (Rs : List (List ℕ)) (hl : Rs.length = n) (hr : ∀ r ∈ Rs, r.length = n) :
    rowsOf n Rs.flatten = Rs := by
  apply List.ext_getElem
  · rw [rowsOf_length, hl]
  · intro j h1 h2
    simp only [rowsOf, List.getElem_map, List.getElem_range]
    have hjl : (Rs[j]).length = n := hr _ (List.getElem_mem _)
    apply List.ext_getElem
    · simp [hjl]
    · intro k hk1 hk2
      simp only [List.getElem_map, List.getElem_range]
      rw [flatten_getD n Rs hr j k h2 (by simp at hk1; exact hk1)]
      rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ hk2]

lemma len_matrix {a b : ℕ} (G : Fin a → Fin b → ℕ) :
    (List.ofFn fun j => List.ofFn fun k => G j k).flatten.length = a * b := by
  simp [List.length_flatten, List.sum_ofFn]

lemma rows_matrix {n : ℕ} (G : Fin n → Fin n → ℕ) :
    rowsOf n (List.ofFn fun j => List.ofFn fun k => G j k).flatten =
      List.ofFn fun j => List.ofFn fun k => G j k :=
  rowsOf_inv n _ (by simp) (by intro r h; simp at h; obtain ⟨j, rfl⟩ := h; simp)

lemma range_ite (K i : ℕ) (hi : i < K) :
    (List.range K).map (fun x => if i < x then 1 else 0) =
      List.replicate (i + 1) 0 ++ List.replicate (K - 1 - i) 1 := by
  apply List.ext_getElem
  · simp; omega
  · intro x h1 h2
    simp only [List.getElem_map, List.getElem_range]
    by_cases hx : x < i + 1
    · rw [List.getElem_append_left (by simpa using hx)]
      simp; omega
    · rw [List.getElem_append_right (by simpa using hx)]
      simp; omega

/-! ## the code of an instance -/

def matI (I : Instance) : List ℕ :=
  (List.ofFn fun j : Fin I.n => List.ofFn fun k : Fin I.n => if I.prec j k then 1 else 0).flatten

lemma tup_code (I : Instance) (y : ℕ) : TupOK (code I y) I.n I.m (List.ofFn I.p) (matI I) y :=
  ⟨rfl, by simp, len_matrix _⟩

lemma code_ne_nil (I : Instance) (y : ℕ) : code I y ≠ [] := by
  intro h
  have := encNats_eq_nil h
  simp at this

lemma ite_inj (a b : Bool) (h : (if a then 1 else 0 : ℕ) = if b then 1 else 0) : a = b := by
  cases a <;> cases b <;> simp_all

lemma code_inj {I I' : Instance} {y y' : ℕ} (h : code I y = code I' y') : I = I' ∧ y = y' := by
  have t1 := tup_code I y
  have t2 := tup_code I' y'
  rw [← h] at t2
  obtain ⟨h1, h2, h3, h4, h5⟩ := tup_unique t1 t2
  refine ⟨?_, h5⟩
  cases I with
  | mk n m p prec =>
  cases I' with
  | mk n' m' p' prec' =>
  simp only at h1 h2 h3 h4
  subst h1; subst h2
  have hp : p = p' := List.ofFn_inj.mp h3
  subst hp
  have h4' := congrArg (rowsOf n) h4
  unfold matI at h4'
  simp only at h4'
  rw [rows_matrix, rows_matrix] at h4'
  have h6 := List.ofFn_inj.mp h4'
  have hprec : prec = prec' := by
    funext j k
    have := congrFun h6 j
    have := congrFun (List.ofFn_inj.mp this) k
    exact ite_inj _ _ this
  subst hprec
  rfl

/-! ## the output of the machine as a code -/

def newRowsL (n K : ℕ) : List ℕ :=
  (List.range K).flatMap (fun i => List.replicate (n + i + 1) 0 ++ List.replicate (K - 1 - i) 1)

lemma newBlk_eq : ∀ (c t z : ℕ), newBlk t z c = encNats ((List.range c).flatMap
    (fun i => List.replicate (z - (c - 1 - i)) 0 ++ List.replicate (t + (c - 1 - i)) 1)) := by
  intro c
  induction c with
  | zero => intro t z; rfl
  | succ c ih =>
    intro t z
    rw [newBlk, ih, List.range_succ, List.flatMap_append, encNats_append']
    congr 1
    · congr 1
      unfold List.flatMap
      congr 1
      apply List.map_congr_left
      intro i hi
      simp at hi
      rw [show z - 1 - (c - 1 - i) = z - (c + 1 - 1 - i) by omega,
        show t + 1 + (c - 1 - i) = t + (c + 1 - 1 - i) by omega]
    · simp [rowSym]

lemma newBlk_eq' (n K : ℕ) : newBlk 0 (K + n) K = encNats (newRowsL n K) := by
  rw [newBlk_eq, newRowsL]
  congr 1
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro i hi
  simp at hi
  rw [show K + n - (K - 1 - i) = n + i + 1 by omega, show 0 + (K - 1 - i) = K - 1 - i by omega]

lemma outSym_eq (pstar n m : ℕ) (ps ms : List ℕ) (y : ℕ) :
    outSym pstar n m ps ms y = encNats ([(n - 1) * min y (pstar * n) + n, m] ++ ps ++
      List.replicate ((n - 1) * min y (pstar * n)) 1 ++
      ((rowsOf n ms).flatMap (fun row => row ++ List.replicate ((n - 1) * min y (pstar * n)) 1) ++
      newRowsL n ((n - 1) * min y (pstar * n))) ++
      [(n - 1) * min y (pstar * n) * ((n - 1) * min y (pstar * n) + 1) / 2 +
        min y (pstar * n) * ((n - 1) * min y (pstar * n) + n)]) := by
  simp only [outSym, newBlk_eq']
  simp only [encNats_append', encNats_cons', encNats_nil, List.append_nil, List.append_assoc]

/-! ## the matrix of the construction -/

lemma matI_chain (I : Instance) (y2 : ℕ) :
    matI (chainExtend I y2) = (rowsOf I.n (matI I)).flatMap
      (fun row => row ++ List.replicate (nNew I.n y2) 1) ++ newRowsL I.n (nNew I.n y2) := by
  unfold matI
  rw [rows_matrix]
  show (List.ofFn fun j : Fin (I.n + nNew I.n y2) => List.ofFn fun k : Fin (I.n + nNew I.n y2) =>
    if (chainExtend I y2).prec j k then 1 else 0).flatten = _
  rw [List.ofFn_add, List.flatten_append]
  congr 1
  · unfold List.flatMap
    rw [List.map_ofFn]
    congr 1
    congr 1
    funext j
    simp only [Function.comp_apply]
    rw [List.ofFn_add]
    congr 1
    · congr 1; funext k
      simp [chainExtend]
    · rw [← List.ofFn_const]
      congr 1
      funext k
      have := j.isLt
      simp [chainExtend]; omega
  · unfold newRowsL List.flatMap
    rw [← ofFn_val']
    congr 1
    congr 1
    funext i
    rw [List.ofFn_add, show I.n + ↑i + 1 = I.n + (↑i + 1) by omega, List.replicate_add,
      List.append_assoc]
    congr 1
    · rw [← List.ofFn_const]; congr 1; funext k; simp [chainExtend]
    · rw [← range_ite _ i i.isLt, ← ofFn_val']; congr 1; funext k; simp [chainExtend]

lemma ofFn_p_chain (I : Instance) (y2 : ℕ) :
    List.ofFn (chainExtend I y2).p = List.ofFn I.p ++ List.replicate (nNew I.n y2) 1 := by
  show List.ofFn (fun j : Fin (I.n + nNew I.n y2) => (chainExtend I y2).p j) = _
  rw [List.ofFn_add, ← List.ofFn_const]
  congr 1
  · congr 1; funext j; simp [chainExtend]
  · congr 1; funext j; simp [chainExtend]

theorem Fw_code (pstar : ℕ) (I : Instance) (y : ℕ) :
    Fw pstar (code I y) = code (chainExtend I (min y (pstar * I.n)))
      (chainThreshold I.n (min y (pstar * I.n))) := by
  rw [Fw_tup pstar (tup_code I y), outSym_eq]
  show _ = encNats ([I.n + nNew I.n (min y (pstar * I.n)), I.m] ++
    List.ofFn (chainExtend I (min y (pstar * I.n))).p ++
    matI (chainExtend I (min y (pstar * I.n))) ++ [chainThreshold I.n (min y (pstar * I.n))])
  rw [ofFn_p_chain, matI_chain]
  simp only [nNew, chainThreshold]
  generalize min y (pstar * I.n) = y2
  generalize (I.n - 1) * y2 = K
  rw [show K + I.n = I.n + K by ring,
    show K * (K + 1) / 2 + y2 * (I.n + K) = (I.n + K) * y2 + K * (K + 1) / 2 by ring]
  simp only [List.append_assoc]

/-! ## decoding the output -/

lemma mem_matI_le {I : Instance} {x : ℕ} (h : x ∈ matI I) : x ≤ 1 := by
  unfold matI at h
  simp only [List.mem_flatten, List.mem_ofFn] at h
  obtain ⟨l, ⟨j, rfl⟩, hx⟩ := h
  simp only [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  split <;> omega

theorem Fw_inv (pstar : ℕ) (w : List BSym) (J : Instance) (yJ : ℕ) (h : Fw pstar w = code J yJ) :
    ∃ I y, w = code I y := by
  by_cases hex : ∃ n m ps ms y, TupOK w n m ps ms y
  · obtain ⟨n, m, ps, ms, y, ht⟩ := hex
    rw [Fw_tup pstar ht, outSym_eq] at h
    have hL := encNats_inj (h.trans (tup_code J yJ).1.symm)
    -- the entries of `ms` are bits
    simp only [List.cons_append, List.nil_append, List.cons.injEq, List.append_assoc] at hL
    obtain ⟨hn, -, hL⟩ := hL
    have hlen : (ps ++ List.replicate ((n - 1) * min y (pstar * n)) 1).length = (List.ofFn J.p).length := by
      simp [ht.2.1, ← hn]; omega
    rw [← List.append_assoc] at hL
    obtain ⟨-, hL⟩ := List.append_inj hL hlen
    rw [← List.append_assoc] at hL
    obtain ⟨hX, -⟩ := List.append_inj' hL (by simp)
    have hbit : ∀ x ∈ ms, x ≤ 1 := by
      intro x hx
      apply mem_matI_le (I := J)
      unfold matI
      rw [← hX]
      apply List.mem_append_left
      rw [← rowsOf_flatten n ms ht.2.2] at hx
      simp only [List.mem_flatten] at hx
      obtain ⟨r, hr, hxr⟩ := hx
      exact List.mem_flatMap.mpr ⟨r, hr, List.mem_append_left _ hxr⟩
    let I : Instance := ⟨n, m, fun j => ps.getD j 0, fun j k => decide (ms.getD (j * n + k) 0 = 1)⟩
    have hp : List.ofFn I.p = ps := by
      show List.ofFn (fun j : Fin n => ps.getD j 0) = ps
      rw [ofFn_val' n (fun j => ps.getD j 0)]
      apply List.ext_getElem
      · simp [ht.2.1]
      · intro i h1 h2; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    have hm : matI I = ms := by
      show (List.ofFn fun j : Fin n => List.ofFn fun k : Fin n =>
          if decide (ms.getD (j * n + k) 0 = 1) = true then 1 else 0).flatten = ms
      have : (List.ofFn fun j : Fin n => List.ofFn fun k : Fin n =>
          if decide (ms.getD (j * n + k) 0 = 1) = true then 1 else 0) =
          List.ofFn fun j : Fin n => List.ofFn fun k : Fin n => ms.getD (j * n + k) 0 := by
        congr 1; funext j; congr 1; funext k
        have hlt : j.val * n + k.val < ms.length := by
          rw [ht.2.2]; nlinarith [j.isLt, k.isLt]
        have hmem : ms.getD (j * n + k) 0 ∈ ms := by
          rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _
        have := hbit _ hmem
        by_cases h1 : ms.getD (j * n + k) 0 = 1
        · simp only [decide_eq_true_eq, if_pos h1, h1, if_true]
        · simp only [decide_eq_true_eq, if_neg h1]; omega
      rw [this]
      have h2 := rowsOf_flatten n ms ht.2.2
      unfold rowsOf at h2
      rw [← ofFn_val'] at h2
      conv_rhs => rw [← h2]
      congr 1; congr 1; funext j
      rw [← ofFn_val']
    refine ⟨I, y, ?_⟩
    rw [ht.1, (tup_code I y).1, hp, hm]
  · exfalso
    rw [Fw_bad pstar (fun n m ps ms y ht => hex ⟨n, m, ps, ms, y, ht⟩)] at h
    exact code_ne_nil J yJ h.symm

/-! ## the class -/

lemma chain_prec_lt (I : Instance) (y2 : ℕ) :
    ∀ a b : Fin (chainExtend I y2).n, Relation.TransGen (chainExtend I y2).Precedes a b →
      (∀ hb : b.val < I.n, ∃ ha : a.val < I.n,
        Relation.TransGen I.Precedes ⟨a.val, ha⟩ ⟨b.val, hb⟩) ∧ (I.n ≤ b.val → a.val < b.val) := by
  intro a b h
  induction h with
  | single hab =>
    rename_i b
    unfold Instance.Precedes at hab
    simp only [chainExtend] at hab
    constructor
    · intro hb
      rw [dif_pos hb] at hab
      by_cases ha : a.val < I.n
      · rw [dif_pos ha] at hab
        exact ⟨ha, Relation.TransGen.single hab⟩
      · rw [dif_neg ha] at hab; cases hab
    · intro hb
      rw [dif_neg (by omega)] at hab
      simpa using hab
  | tail hab hbc ih =>
    rename_i b c
    unfold Instance.Precedes at hbc
    simp only [chainExtend] at hbc
    constructor
    · intro hc
      rw [dif_pos hc] at hbc
      by_cases hb : b.val < I.n
      · rw [dif_pos hb] at hbc
        obtain ⟨ha, hab'⟩ := ih.1 hb
        exact ⟨ha, Relation.TransGen.tail hab' hbc⟩
      · rw [dif_neg hb] at hbc; cases hbc
    · intro hc
      rw [dif_neg (by omega)] at hbc
      have hbc' : b.val < c.val := by simpa using hbc
      by_cases hb : b.val < I.n
      · obtain ⟨ha, _⟩ := ih.1 hb; omega
      · have := ih.2 (by omega); omega

lemma inClass_chain (pstar : ℕ) (hp : 1 ≤ pstar) (I : Instance) (hI : I.InClass pstar) (y2 : ℕ) :
    (chainExtend I y2).InClass pstar := by
  obtain ⟨hm, hpj, hac⟩ := hI
  refine ⟨hm, ?_, ?_⟩
  · intro j
    simp only [chainExtend]
    split
    · exact hpj _
    · exact ⟨le_rfl, hp⟩
  · intro j hj
    obtain ⟨h1, h2⟩ := chain_prec_lt I y2 j j hj
    by_cases hjn : j.val < I.n
    · obtain ⟨_, h⟩ := h1 hjn
      exact hac _ h
    · have := h2 (by omega); omega

lemma inClass_of_chain (pstar : ℕ) (I : Instance) (y2 : ℕ) (h : (chainExtend I y2).InClass pstar) :
    I.InClass pstar := by
  obtain ⟨hm, hpj, hac⟩ := h
  refine ⟨hm, ?_, ?_⟩
  · intro j
    have := hpj (Fin.castAdd (nNew I.n y2) j)
    simpa [chainExtend] using this
  · intro j hj
    apply hac (Fin.castAdd (nNew I.n y2) j)
    refine Relation.TransGen.lift (Fin.castAdd (nNew I.n y2)) (fun a b hab => ?_) j j hj
    show (chainExtend I y2).prec _ _ = true
    unfold Instance.Precedes at hab
    simpa [chainExtend] using hab

lemma chainThreshold_cast (n y : ℕ) : (chainThreshold n y : ℚ) = chainThresholdQ n y := by
  unfold chainThreshold chainThresholdQ
  have hd : 2 ∣ nNew n y * (nNew n y + 1) := (Nat.even_mul_succ_self _).two_dvd
  rw [Nat.cast_add, Nat.cast_div hd (by norm_num)]
  push_cast
  ring

/-! ## the reduction -/

theorem leaf (pstar : ℕ) (hpstar : 1 ≤ pstar) :
    ∃ f : List BSym → List BSym, CookPvsNP.PolyTimeComputable f ∧
      ∀ c : List BSym,
        ((∃ (I : Instance) (y' : ℕ), I.InClass pstar ∧ y' ≤ I.n * pstar ∧
            (∃ σ : Schedule (chainExtend I y'), σ.IsFeasible ∧
              (σ.totalCompletion : ℚ) ≤ chainThresholdQ I.n y') ∧
            c = code I y') ∨
          (∃ (I : Instance) (y' : ℕ), I.InClass pstar ∧ I.n * pstar < y' ∧ c = code I y')) ↔
          f c ∈ sumCLang pstar := by
  refine ⟨Fw pstar, Fw_poly pstar, fun c => ⟨?_, ?_⟩⟩
  · rintro (⟨I, y', hI, hy, ⟨σ, hσ, hle⟩, rfl⟩ | ⟨I, y', hI, hy, rfl⟩)
    · have hmin : min y' (pstar * I.n) = y' := min_eq_left (by rw [mul_comm]; exact hy)
      rw [Fw_code, hmin]
      refine ⟨_, _, inClass_chain pstar hpstar I hI y', ⟨σ, hσ, ?_⟩, rfl⟩
      rw [← chainThreshold_cast] at hle
      exact_mod_cast hle
    · have hmin : min y' (pstar * I.n) = I.n * pstar := by
        rw [min_eq_right (by rw [mul_comm]; exact hy.le), mul_comm]
      rw [Fw_code, hmin]
      obtain ⟨σ, hσ, hle⟩ := cmax_le_imp_sumC_le pstar I hI (I.n * pstar) le_rfl
        (cmax_le_n_pstar pstar I hI)
      refine ⟨_, _, inClass_chain pstar hpstar I hI _, ⟨σ, hσ, ?_⟩, rfl⟩
      rw [← chainThreshold_cast] at hle
      exact_mod_cast hle
  · rintro ⟨J, yJ, hJ, hyes, hc⟩
    obtain ⟨I, y', rfl⟩ := Fw_inv pstar c J yJ hc
    rw [Fw_code] at hc
    by_cases hy : y' ≤ I.n * pstar
    · have hmin : min y' (pstar * I.n) = y' := min_eq_left (by rw [mul_comm]; exact hy)
      rw [hmin] at hc
      obtain ⟨hJI, hyJ⟩ := code_inj hc
      subst hJI; subst hyJ
      obtain ⟨σ, hσ, hle⟩ := hyes
      left
      refine ⟨I, y', inClass_of_chain pstar I _ hJ, hy, ⟨σ, hσ, ?_⟩, rfl⟩
      rw [← chainThreshold_cast]; exact_mod_cast hle
    · obtain ⟨hJI, -⟩ := code_inj hc
      subst hJI
      right
      exact ⟨I, y', inClass_of_chain pstar I _ hJ, by omega, rfl⟩

end PCR

open SchedComplexity.PrecChain
open ProjSchedTW.Complexity (BSym encNats)

theorem solution (pstar : ℕ) (hpstar : 1 ≤ pstar) :
    ∃ f : List BSym → List BSym, CookPvsNP.PolyTimeComputable f ∧
      ∀ c : List BSym,
        ((∃ (I : Instance) (y' : ℕ), I.InClass pstar ∧ y' ≤ I.n * pstar ∧
            (∃ σ : Schedule (chainExtend I y'), σ.IsFeasible ∧
              (σ.totalCompletion : ℚ) ≤ chainThresholdQ I.n y') ∧
            c = code I y') ∨
          (∃ (I : Instance) (y' : ℕ), I.InClass pstar ∧ I.n * pstar < y' ∧ c = code I y')) ↔
          f c ∈ sumCLang pstar :=
  PCR.leaf pstar hpstar
