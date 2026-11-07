-- Prove2me | solution 1 for SchedComplexity.Partition.partition_twoMachine_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:51:34.499361+00:00
-- url     : https://prove2.me/submissions/767013f4-f8ca-4b69-abe9-ea52615608ab

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_Languages
import Definitions.Def_SchedComplexity_Partition_Constructions
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false

namespace P3R

open CookPvsNP ProjSchedTW.Complexity

/-! ## Binary arithmetic model (LSB first) -/

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

def Canon : List Bool → Prop
  | [] => True
  | b :: l => (l = [] → b = true) ∧ Canon l

lemma bval_pos {l : List Bool} (h : Canon l) (hne : l ≠ []) : 0 < bval l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b t ih =>
    simp only [Canon] at h
    by_cases ht : t = []
    · subst ht; have := h.1 rfl; subst this; simp [bval]
    · have := ih h.2 ht
      simp only [bval]
      cases b <;> simp [Nat.bit] <;> omega

lemma bits_bval {l : List Bool} (h : Canon l) : Nat.bits (bval l) = l := by
  induction l with
  | nil => simp [bval]
  | cons b t ih =>
    simp only [Canon] at h
    simp only [bval]
    rw [Nat.bits_append_bit, ih h.2]
    intro h0
    by_cases ht : t = []
    · exact h.1 ht
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp (bval_pos h.2 ht))

lemma canon_bits_bval (n : ℕ) : Canon (Nat.bits n) ∧ bval (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Canon, bval]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    refine ⟨⟨fun h => ?_, ih.1⟩, by simp [bval, ih.2]⟩
    have : n = 0 := by
      have h2 := ih.2; rw [h] at h2; simpa [bval] using h2.symm
    exact hn this

lemma bval_bits (n : ℕ) : bval (Nat.bits n) = n := (canon_bits_bval n).2

def addB : List Bool → List Bool → Bool → List Bool
  | [], [], false => []
  | [], [], true => [true]
  | x :: xs, [], c => (x ^^ c) :: addB xs [] (x && c)
  | [], y :: ys, c => (y ^^ c) :: addB [] ys (y && c)
  | x :: xs, y :: ys, c => (x ^^ y ^^ c) :: addB xs ys ((x && y) || (c && (x ^^ y)))

lemma bval_addB (x y : List Bool) (c : Bool) :
    bval (addB x y c) = bval x + bval y + c.toNat := by
  induction x, y, c using addB.induct with
  | case1 => simp [addB, bval]
  | case2 => simp [addB, bval, Nat.bit]
  | case3 x xs c ih =>
    simp only [addB, bval, ih]; cases x <;> cases c <;> simp [Nat.bit] <;> omega
  | case4 y ys c ih =>
    simp only [addB, bval, ih]; cases y <;> cases c <;> simp [Nat.bit] <;> omega
  | case5 x xs y ys c ih =>
    simp only [addB, bval, ih]; cases x <;> cases y <;> cases c <;> simp [Nat.bit] <;> omega

lemma addB_eq_nil {x y : List Bool} {c : Bool} (h : addB x y c = []) :
    x = [] ∧ y = [] ∧ c = false := by
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> cases c <;> simp_all [addB]

lemma canon_addB (x y : List Bool) (c : Bool) (hx : Canon x) (hy : Canon y) :
    Canon (addB x y c) := by
  induction x, y, c using addB.induct with
  | case1 => simp [addB, Canon]
  | case2 => simp [addB, Canon]
  | case3 x xs c ih =>
    simp only [Canon] at hx
    simp only [addB, Canon]
    refine ⟨fun h => ?_, ih hx.2 hy⟩
    obtain ⟨h1, -, h3⟩ := addB_eq_nil h
    have := hx.1 h1; subst this; simpa using h3
  | case4 y ys c ih =>
    simp only [Canon] at hy
    simp only [addB, Canon]
    refine ⟨fun h => ?_, ih hx hy.2⟩
    obtain ⟨-, h2, h3⟩ := addB_eq_nil h
    have := hy.1 h2; subst this; simpa using h3
  | case5 x xs y ys c ih =>
    simp only [Canon] at hx hy
    simp only [addB, Canon]
    refine ⟨fun h => ?_, ih hx.2 hy.2⟩
    obtain ⟨h1, h2, h3⟩ := addB_eq_nil h
    have := hx.1 h1; have := hy.1 h2; subst_vars; simp at h3

lemma bits_add (a b : ℕ) : Nat.bits (a + b) = addB (Nat.bits a) (Nat.bits b) false := by
  have ha := canon_bits_bval a; have hb := canon_bits_bval b
  have hc := canon_addB _ _ false ha.1 hb.1
  rw [← bits_bval hc, bval_addB, ha.2, hb.2]; simp

lemma bits_div_two (n : ℕ) : Nat.bits (n / 2) = (Nat.bits n).tail := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn _ =>
    rw [Nat.bits_append_bit _ _ hn]
    simp [Nat.bit_div_two]

lemma bits_two_mul (m : ℕ) (hm : m ≠ 0) : Nat.bits (2 * m) = false :: Nat.bits m := by
  have : 2 * m = Nat.bit false m := by simp [Nat.bit]
  rw [this, Nat.bits_append_bit _ _ (fun h => absurd h hm)]

lemma addB_step (x y : List Bool) (c : Bool) (h : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    addB x y c = (x.headD false ^^ y.headD false ^^ c) ::
      addB x.tail y.tail ((x.headD false && y.headD false) ||
        (c && (x.headD false ^^ y.headD false))) := by
  match x, y, c with
  | [], [], false => simp at h
  | [], [], true => simp [addB]
  | x :: xs, [], c => cases x <;> cases c <;> simp [addB]
  | [], y :: ys, c => cases y <;> cases c <;> simp [addB]
  | x :: xs, y :: ys, c => simp [addB]

lemma meas_step (x y : List Bool) (c : Bool) (h0 : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    x.tail.length + y.tail.length +
      ((x.headD false && y.headD false) || (c && (x.headD false ^^ y.headD false))).toNat + 1 ≤
      x.length + y.length + c.toNat := by
  rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;>
    (try cases x0) <;> (try cases y0) <;> simp_all <;> omega

/-! ## Stacks -/

inductive Key
  | inp | inp2 | inpC | c1 | c2 | tmp | car | sc | mA | mB | acc | lt | gt | pend | last1 | bad
  | R | out
  | ONE | ZR | A | T | Q | X | X2 | S2 | Q2 | Y | H
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .inp2, .inpC, .c1, .c2, .tmp, .car, .sc, .mA, .mB, .acc, .lt, .gt, .pend, .last1,
    .bad, .R, .out, .ONE, .ZR, .A, .T, .Q, .X, .X2, .S2, .Q2, .Y, .H}
  complete := by intro x; cases x <;> decide

abbrev Store := Key → List BSym
abbrev Prog := StackProg Key BSym

def toB (b : Bool) : BSym := if b then .one else .zero
def enc (x : List Bool) : List BSym := x.map toB
def encN (n : ℕ) : List BSym := enc (Nat.bits n)
def flag (b : Bool) : List BSym := if b then [.one] else []

lemma encNat_eq (k : ℕ) : encNat k = encN k ++ [BSym.sep] := by
  simp [encNat, encN, enc, toB]

lemma encN_zero : encN 0 = [] := by simp [encN, enc]

lemma length_encN (n : ℕ) : (encN n).length = (Nat.bits n).length := by simp [encN, enc]

def bitOf : Option BSym → Bool
  | some .one => true
  | _ => false

def isDig : Option BSym → Bool
  | some .one => true
  | some .zero => true
  | _ => false

lemma bitOf_enc (x : List Bool) : bitOf (enc x).head? = x.headD false := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

lemma isSome_enc (x : List Bool) : ((enc x).head?).isSome = !x.isEmpty := by
  cases x <;> simp [enc]

lemma flag_isSome (b : Bool) : ((flag b).head?).isSome = b := by cases b <;> rfl

/-- set a flag stack (holding `flag cur`) to `flag new`. -/
def setFlag (cur new : Bool) : StackAct BSym :=
  if new then (if cur then .keep else .push .one) else (if cur then .pop else .keep)

lemma setFlag_apply (c n : Bool) : (setFlag c n).apply (flag c) = flag n := by
  cases c <;> cases n <;> rfl

/-! ## Runs -/

def Runs (p : Prog) (s t : Store) (B : ℕ) : Prop := ∃ n ≤ B, p.Exec s t n

lemma Runs.mono {p : Prog} {s t : Store} {B B' : ℕ} (h : Runs p s t B) (hB : B ≤ B') :
    Runs p s t B' := by
  obtain ⟨n, hn, e⟩ := h; exact ⟨n, le_trans hn hB, e⟩

lemma Runs.seq {p q : Prog} {s t u : Store} {B1 B2 : ℕ} (h1 : Runs p s t B1)
    (h2 : Runs q t u B2) : Runs (.seq p q) s u (B1 + B2 + 1) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, f⟩ := h2
  exact ⟨n + 1 + m, by omega, StackProg.Exec.seq e f⟩

lemma Runs.seq' {p q : Prog} {s t u : Store} {B1 B2 B : ℕ} (h1 : Runs p s t B1)
    (h2 : Runs q t u B2) (hB : B1 + B2 + 1 ≤ B) : Runs (.seq p q) s u B :=
  (h1.seq h2).mono hB

lemma Runs.brT {test : (Key → Option BSym) → Bool} {p q : Prog} {s t : Store} {B : ℕ}
    (ht : test (fun k => (s k).head?) = true) (h : Runs p s t B) :
    Runs (.branch test p q) s t (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchTrue ht e⟩

lemma Runs.brF {test : (Key → Option BSym) → Bool} {p q : Prog} {s t : Store} {B : ℕ}
    (ht : test (fun k => (s k).head?) = false) (h : Runs q s t B) :
    Runs (.branch test p q) s t (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchFalse ht e⟩

lemma Runs.act (f : (Key → Option BSym) → Key → StackAct BSym) (s : Store) :
    Runs (.act f) s (StackProg.applyAct f s) 1 := ⟨1, le_rfl, StackProg.Exec.act f s⟩

lemma Runs.loopF {test : (Key → Option BSym) → Bool} {p : Prog} {s : Store}
    (ht : test (fun k => (s k).head?) = false) : Runs (.loop test p) s s 1 :=
  ⟨1, le_rfl, StackProg.Exec.loopFalse ht⟩

lemma Runs.loopT {test : (Key → Option BSym) → Bool} {p : Prog} {s t u : Store} {B1 B2 : ℕ}
    (ht : test (fun k => (s k).head?) = true) (h1 : Runs p s t B1)
    (h2 : Runs (.loop test p) t u B2) : Runs (.loop test p) s u (B1 + B2 + 2) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, f⟩ := h2
  exact ⟨1 + n + 1 + m, by omega, StackProg.Exec.loopTrue ht e f⟩

def skipP : Prog := .act (fun _ _ => .keep)

lemma runs_skip (s : Store) : Runs skipP s s 1 := by
  have := Runs.act (fun _ _ => StackAct.keep) s
  have e : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
    funext k; rfl
  rw [e] at this; exact this

lemma runs_push (k : Key) (a : BSym) (s : Store) :
    Runs (pushProg k a) s (Function.update s k (a :: s k)) 1 := by
  have := Runs.act (fun _ j => if j = k then StackAct.push a else .keep) s
  have e : StackProg.applyAct (fun _ j => if j = k then StackAct.push a else .keep) s =
      Function.update s k (a :: s k) := by
    funext j; by_cases h : j = k
    · subst h; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, h]
  rw [e] at this; exact this

lemma runs_pop (k : Key) (s : Store) :
    Runs (popProg k) s (Function.update s k (s k).tail) 1 := by
  have := Runs.act (fun _ j => if j = k then StackAct.pop else .keep) s
  have e : StackProg.applyAct (fun _ j => if j = k then StackAct.pop else .keep) s =
      Function.update s k (s k).tail := by
    funext j; by_cases h : j = k
    · subst h; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, h]
  rw [e] at this; exact this

lemma runs_transfer (src : Key) (targets : Key → Bool) :
    ∀ (s : Store), Runs (transferProg src targets) s (transferStore src targets s)
      (3 * (s src).length + 1) := by
  suffices h : ∀ (l : List BSym) (s : Store), s src = l →
      Runs (transferProg src targets) s (transferStore src targets s) (3 * l.length + 1) by
    intro s; exact h _ s rfl
  intro l
  induction l with
  | nil =>
    intro s hs
    have : transferStore src targets s = s := by
      funext k; simp only [transferStore]
      split_ifs with h1 h2 <;> simp_all
    rw [this]
    exact Runs.loopF (by simp [hs])
  | cons a l ih =>
    intro s hs
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = StackProg.applyAct (transferAct src targets) s := ⟨_, rfl⟩
    have e1 : s1 src = l := by
      rw [hs1]; simp [StackProg.applyAct, transferAct, StackAct.apply, hs]
    have hpost : transferStore src targets s1 = transferStore src targets s := by
      funext k; simp only [transferStore]
      by_cases k1 : k = src
      · simp [k1]
      by_cases k2 : targets k = true
      · simp [k1, k2, e1, hs, hs1, StackProg.applyAct, transferAct, StackAct.apply]
      · simp [k1, k2, hs1, StackProg.applyAct, transferAct, StackAct.apply]
    have ih' := ih s1 e1
    rw [hpost, hs1] at ih'
    have := Runs.loopT (test := fun h => (h src).isSome) (by simp [hs])
      (Runs.act (transferAct src targets) s) ih'
    exact this.mono (by simp; omega)

lemma runs_move (src dst : Key) (h : src ≠ dst) (s : Store) :
    Runs (transferProg src (fun k => decide (k = dst))) s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst))
      (3 * (s src).length + 1) := by
  have := runs_transfer src (fun k => decide (k = dst)) s
  have e : transferStore src (fun k => decide (k = dst)) s =
      Function.update (Function.update s src []) dst ((s src).reverse ++ s dst) := by
    funext k
    by_cases k1 : k = dst
    · subst k1; simp [transferStore, Ne.symm h]
    by_cases k2 : k = src
    · subst k2; rw [Function.update_of_ne k1, Function.update_self]; simp [transferStore]
    · simp [transferStore, k1, k2]
  rw [e] at this; exact this

lemma runs_clear (k : Key) (s : Store) :
    Runs (clearProg k) s (Function.update s k []) (3 * (s k).length + 1) := by
  have := runs_transfer k (fun _ => false) s
  have e : transferStore k (fun _ => false) s = Function.update s k [] := by
    funext j; by_cases h : j = k
    · subst h; simp [transferStore]
    · simp [transferStore, h]
  rw [e] at this; exact this

lemma runs_copy (src dst scr : Key) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (s : Store) (hs : s scr = []) :
    Runs (copyProg src dst scr) s (Function.update s dst (s src ++ s dst))
      (6 * (s src).length + 3) := by
  have e1 := runs_transfer src (fun k => decide (k = scr)) s
  set s1 := transferStore src (fun k => decide (k = scr)) s with hs1
  have hs1scr : s1 scr = (s src).reverse := by simp [hs1, transferStore, h2.symm, hs]
  have e2 := runs_transfer scr (fun k => decide (k = src ∨ k = dst)) s1
  have : transferStore scr (fun k => decide (k = src ∨ k = dst)) s1 =
      Function.update s dst (s src ++ s dst) := by
    funext k
    by_cases k1 : k = scr
    · subst k1; simp [transferStore, h3.symm, hs]
    by_cases k2 : k = src
    · subst k2; simp [transferStore, hs1, k1, h1, Ne.symm k1, hs]
    by_cases k3 : k = dst
    · subst k3; simp [transferStore, hs1, k1, k2, h2.symm, h3, hs]
    · simp [transferStore, hs1, k1, k2, k3]
  rw [this] at e2
  refine (e1.seq e2).mono ?_
  rw [hs1scr]; simp; omega

end P3R



namespace P3R

open CookPvsNP ProjSchedTW.Complexity

def sz (n : ℕ) : ℕ := (Nat.bits n).length

lemma sz_eq_size (n : ℕ) : sz n = Nat.size n := Nat.size_eq_bits_len n ▸ rfl

lemma sz_mono {m n : ℕ} (h : m ≤ n) : sz m ≤ sz n := by
  rw [sz_eq_size, sz_eq_size]; exact Nat.size_le_size h

lemma sz_le_iff {n W : ℕ} : sz n ≤ W ↔ n < 2 ^ W := by
  rw [sz_eq_size]; exact Nat.size_le

lemma lt_pow_sz (n : ℕ) : n < 2 ^ sz n := sz_le_iff.mp le_rfl

lemma sz_add_le (a b : ℕ) : sz (a + b) ≤ sz a + sz b + 1 := by
  rw [sz_le_iff]
  have ha := lt_pow_sz a; have hb := lt_pow_sz b
  have h1 : 2 ^ sz a ≤ 2 ^ (sz a + sz b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ sz b ≤ 2 ^ (sz a + sz b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

lemma sz_mul_le (a b : ℕ) : sz (a * b) ≤ sz a + sz b := by
  rw [sz_le_iff, pow_add]
  exact Nat.mul_lt_mul'' (lt_pow_sz a) (lt_pow_sz b)

lemma sz_mul_pow (a k : ℕ) : sz (a * 2 ^ k) ≤ sz a + k := by
  rw [sz_le_iff, pow_add]
  exact Nat.mul_lt_mul_of_pos_right (lt_pow_sz a) (by positivity)

lemma sz_div2 (n : ℕ) : sz (n / 2) ≤ sz n := sz_mono (Nat.div_le_self _ _)

lemma length_encN' (n : ℕ) : (encN n).length = sz n := by simp [encN, enc, sz]

/-! ## The adder loop: `c1`, `c2` (and carry `car`) into `tmp` (reversed). -/

def carryOut (a b c : Bool) : Bool := (a && b) || (c && (a ^^ b))

def addAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .c1 then .pop else if k = .c2 then .pop
  else if k = .tmp then .push (toB (bitOf (h .c1) ^^ bitOf (h .c2) ^^ (h .car).isSome))
  else if k = .car then setFlag (h .car).isSome (carryOut (bitOf (h .c1)) (bitOf (h .c2)) (h .car).isSome)
  else .keep

def addTest (h : Key → Option BSym) : Bool := (h .c1).isSome || (h .c2).isSome || (h .car).isSome

def addLoop : Prog := .loop addTest (.act addAct)

def addPost (x y : List Bool) (c : Bool) (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s .c1 []) .c2 []) .car [])
    .tmp ((enc (addB x y c)).reverse ++ s .tmp)

lemma runs_addLoop : ∀ (N : ℕ) (x y : List Bool) (c : Bool) (s : Store),
    x.length + y.length + c.toNat ≤ N →
    s .c1 = enc x → s .c2 = enc y → s .car = flag c →
    Runs addLoop s (addPost x y c s) (3 * (x.length + y.length + c.toNat) + 1) := by
  intro N
  induction N with
  | zero =>
    intro x y c s hN hx hy hc
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hc0 : c = false := by cases c <;> simp_all
    subst hx0 hy0 hc0
    have hpost : addPost [] [] false s = s := by
      funext k
      simp only [addPost, addB, enc, List.map_nil, List.reverse_nil, List.nil_append,
        Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [flag, enc]
    rw [hpost]
    exact (Runs.loopF (by simp [addTest, hx, hy, hc, enc, flag])).mono (by simp)
  | succ N ih =>
    intro x y c s hN hx hy hc
    by_cases h0 : x = [] ∧ y = [] ∧ c = false
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      have hpost : addPost [] [] false s = s := by
        funext k
        simp only [addPost, addB, enc, List.map_nil, List.reverse_nil, List.nil_append,
          Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [flag, enc]
      rw [hpost]
      exact (Runs.loopF (by simp [addTest, hx, hy, hc, enc, flag])).mono (by simp)
    · have hmeas := meas_step x y c h0
      have hstep := addB_step x y c h0
      have hhx : bitOf (s .c1).head? = x.headD false := by rw [hx]; exact bitOf_enc x
      have hhy : bitOf (s .c2).head? = y.headD false := by rw [hy]; exact bitOf_enc y
      have hcs : ((s .car).head?).isSome = c := by rw [hc]; exact flag_isSome c
      set a := x.headD false
      set b := y.headD false
      set s1 := StackProg.applyAct addAct s with hs1
      have e1 : s1 .c1 = enc x.tail := by
        simp [s1, StackProg.applyAct, addAct, StackAct.apply, hx, enc, List.map_tail]
      have e2 : s1 .c2 = enc y.tail := by
        simp [s1, StackProg.applyAct, addAct, StackAct.apply, hy, enc, List.map_tail]
      have e3 : s1 .tmp = toB (a ^^ b ^^ c) :: s .tmp := by
        simp only [s1, StackProg.applyAct, addAct]
        simp [hhx, hhy, hcs, StackAct.apply]
      have e4 : s1 .car = flag (carryOut a b c) := by
        simp only [s1, StackProg.applyAct, addAct]
        simp only [reduceCtorEq, if_false, if_true, hhx, hhy, hcs]
        rw [hc]; exact setFlag_apply c _
      have e5 : ∀ k, k ≠ .c1 → k ≠ .c2 → k ≠ .tmp → k ≠ .car → s1 k = s k := by
        intro k h1 h2 h3 h4
        simp [s1, StackProg.applyAct, addAct, h1, h2, h3, h4, StackAct.apply]
      have ih' := ih x.tail y.tail (carryOut a b c) s1 (by unfold carryOut; omega) e1 e2 e4
      have hpost : addPost x.tail y.tail (carryOut a b c) s1 = addPost x y c s := by
        funext k
        simp only [addPost, Function.update_apply]
        by_cases k1 : k = .tmp
        · subst k1; simp only [if_true, e3, hstep, carryOut]; simp [enc]
        by_cases k2 : k = .car
        · simp [k2]
        by_cases k3 : k = .c2
        · simp [k3]
        by_cases k4 : k = .c1
        · simp [k4]
        simp [k1, k2, k3, k4, e5 k k4 k3 k1 k2]
      rw [hpost] at ih'
      have htest : addTest (fun k => (s k).head?) = true := by
        simp only [addTest, hx, hy, hc, isSome_enc, flag_isSome]
        rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;> simp_all
      exact (Runs.loopT htest (Runs.act addAct s) ih').mono (by unfold carryOut; omega)

/-! ## Addition of registers -/

def addProg (x y z : Key) : Prog :=
  .seq (copyProg x .c1 .sc) (.seq (copyProg y .c2 .sc) (.seq addLoop
    (.seq (clearProg z) (transferProg .tmp (fun k => decide (k = z))))))

/-- keys not used as scratch by `addProg`. -/
def AFree (k : Key) : Prop := k ≠ .c1 ∧ k ≠ .c2 ∧ k ≠ .tmp ∧ k ≠ .car ∧ k ≠ .sc

lemma runs_add (x y z : Key) (hx : AFree x) (hy : AFree y) (hz : AFree z) (s : Store)
    (h1 : s .c1 = []) (h2 : s .c2 = []) (h3 : s .tmp = []) (h4 : s .car = []) (h5 : s .sc = [])
    (a b : ℕ) (ha : s x = encN a) (hb : s y = encN b) :
    Runs (addProg x y z) s (Function.update s z (encN (a + b)))
      (12 * (sz a + sz b) + 3 * (s z).length + 20) := by
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
  have r1 := runs_copy x .c1 .sc hx1 hx5 (by decide) s h5
  set s1 := Function.update s .c1 (s x ++ s .c1) with hs1
  have r2 := runs_copy y .c2 .sc hy2 hy5 (by decide) s1 (by simp [s1, h5])
  set s2 := Function.update s1 .c2 (s1 y ++ s1 .c2) with hs2
  have r3 := runs_addLoop _ (Nat.bits a) (Nat.bits b) false s2 le_rfl
    (by simp [s2, s1, ha, h1, encN]) (by simp [s2, s1, hb, h2, hy1, encN])
    (by simp [s2, s1, h4, flag])
  set s3 := addPost (Nat.bits a) (Nat.bits b) false s2 with hs3
  have r4 := runs_clear z s3
  set s4 := Function.update s3 z [] with hs4
  have r5 := runs_move .tmp z (Ne.symm hz3) s4
  have e4tmp : s4 .tmp = (encN (a + b)).reverse := by
    simp [s4, s3, addPost, Ne.symm hz3, s2, s1, h3, encN, bits_add]
  have hfin : Function.update (Function.update s4 .tmp []) z ((s4 .tmp).reverse ++ s4 z) =
      Function.update s z (encN (a + b)) := by
    rw [e4tmp]
    funext k
    by_cases k1 : k = z
    · subst k1; simp [s4]
    by_cases k2 : k = .tmp
    · subst k2; simp [k1, h3]
    simp only [Function.update_apply, k1, k2, if_false, s4, s3, addPost, s2, s1]
    by_cases k3 : k = .car
    · subst k3; simp [h4]
    by_cases k4 : k = .c2
    · subst k4; simp [h2]
    by_cases k5 : k = .c1
    · subst k5; simp [h1]
    simp [k3, k4, k5]
  rw [hfin] at r5
  refine (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_
  have l1 : (s x).length = sz a := by rw [ha, length_encN']
  have l2 : (s1 y).length = sz b := by simp [s1, hy1, hb, length_encN']
  have l3 : (s4 .tmp).length = sz (a + b) := by rw [e4tmp]; simp [length_encN']
  have l4 : (s3 z).length = (s z).length := by
    simp [s3, addPost, hz3, hz4, hz2, hz1, s2, s1]
  have l5 := sz_add_le a b
  simp only [l1, l2, l3, l4, Bool.toNat_false, sz] at *
  omega

/-! ## Multiplication -/

def mulBody : Prog :=
  .seq (.branch (fun h => bitOf (h .mB)) (addProg .mA .acc .acc) skipP)
    (.seq (popProg .mB) (.branch (fun h => (h .mA).isSome) (pushProg .mA .zero) skipP))

def mulLoop : Prog := .loop (fun h => (h .mB).isSome) mulBody

lemma encN_two_mul (m : ℕ) (hm : m ≠ 0) : encN (2 * m) = .zero :: encN m := by
  simp [encN, enc, bits_two_mul m hm, toB]

lemma bval_cons (b : Bool) (l : List Bool) : bval (b :: l) = 2 * bval l + b.toNat := by
  cases b <;> simp [bval, Nat.bit] <;> ring

lemma runs_mulLoop (W : ℕ) : ∀ (l : List Bool) (m p : ℕ) (s : Store),
    s .c1 = [] → s .c2 = [] → s .tmp = [] → s .car = [] → s .sc = [] →
    s .mB = enc l → s .mA = encN m → s .acc = encN p →
    sz (m * 2 ^ l.length) ≤ W → sz (p + m * bval l) ≤ W →
    Runs mulLoop s (Function.update (Function.update (Function.update s .mB []) .mA
      (encN (m * 2 ^ l.length))) .acc (encN (p + m * bval l))) (l.length * (27 * W + 30) + 1) := by
  intro l
  induction l with
  | nil =>
    intro m p s h1 h2 h3 h4 h5 hB hA hacc _ _
    have : Function.update (Function.update (Function.update s .mB []) .mA
      (encN (m * 2 ^ ([] : List Bool).length))) .acc (encN (p + m * bval [])) = s := by
      funext k
      by_cases k1 : k = .acc
      · subst k1; simp [bval, hacc]
      by_cases k2 : k = .mA
      · subst k2; simp [hA]
      by_cases k3 : k = .mB
      · subst k3; simp [hB, enc]
      simp [k1, k2, k3]
    rw [this]
    exact (Runs.loopF (by simp [hB, enc])).mono (by simp)
  | cons b l ih =>
    intro m p s h1 h2 h3 h4 h5 hB hA hacc hW1 hW2
    have hmW : sz m ≤ W := le_trans (sz_mono (Nat.le_mul_of_pos_right _ (by positivity))) hW1
    have hpW : sz p ≤ W := le_trans (sz_mono (Nat.le_add_right _ _)) hW2
    set p' := p + (if b then m else 0) with hp'
    -- first branch
    have rb1 : Runs (.branch (fun h => bitOf (h .mB)) (addProg .mA .acc .acc) skipP) s
        (Function.update s .acc (encN p')) (27 * W + 21) := by
      have htest : bitOf (s .mB).head? = b := by rw [hB, bitOf_enc]; rfl
      cases b
      · have : Function.update s .acc (encN p') = s := by
          simp [p', ← hacc]
        rw [this]
        exact (Runs.brF htest (runs_skip s)).mono (by omega)
      · have := runs_add .mA .acc .acc (by unfold AFree; decide) (by unfold AFree; decide)
          (by unfold AFree; decide) s h1 h2 h3 h4 h5 m p hA hacc
        have e : m + p = p' := by simp [p']; omega
        rw [e] at this
        refine (Runs.brT htest this).mono ?_
        rw [hacc, length_encN']; omega
    set s1 := Function.update s .acc (encN p')
    have rp := runs_pop .mB s1
    set s2 := Function.update s1 .mB (s1 .mB).tail
    have rb2 : Runs (.branch (fun h => (h .mA).isSome) (pushProg .mA .zero) skipP) s2
        (Function.update s2 .mA (encN (2 * m))) 2 := by
      by_cases hm : m = 0
      · subst hm
        have : Function.update s2 .mA (encN (2 * 0)) = s2 := by
          simp [s2, s1, ← hA]
        rw [this]
        exact Runs.brF (by simp [s2, s1, hA, encN_zero]) (runs_skip s2)
      · have := runs_push .mA .zero s2
        have e : BSym.zero :: s2 .mA = encN (2 * m) := by
          rw [encN_two_mul m hm]; simp [s2, s1, hA]
        rw [e] at this
        refine Runs.brT ?_ this
        have hne : Nat.bits m ≠ [] := by
          intro h; have := bval_bits m; rw [h] at this; simp [bval] at this; exact hm this.symm
        rcases hb' : Nat.bits m with _ | ⟨c, l'⟩
        · exact absurd hb' hne
        · simp [s2, s1, hA, encN, enc, hb']
    set s3 := Function.update s2 .mA (encN (2 * m))
    have hval : p' + 2 * m * bval l = p + m * bval (b :: l) := by
      rw [bval_cons]; cases b <;> simp [p'] <;> ring
    have hpow : 2 * m * 2 ^ l.length = m * 2 ^ (b :: l).length := by
      simp [pow_succ]; ring
    have ih' := ih (2 * m) p' s3 (by simp [s3, s2, s1, h1]) (by simp [s3, s2, s1, h2])
      (by simp [s3, s2, s1, h3]) (by simp [s3, s2, s1, h4]) (by simp [s3, s2, s1, h5])
      (by simp [s3, s2, s1, hB, enc]) (by simp [s3]) (by simp [s3, s2, s1])
      (by rw [hpow]; exact hW1) (by rw [hval]; exact hW2)
    have hfin : Function.update (Function.update (Function.update s3 .mB []) .mA
        (encN (2 * m * 2 ^ l.length))) .acc (encN (p' + 2 * m * bval l)) =
        Function.update (Function.update (Function.update s .mB []) .mA
        (encN (m * 2 ^ (b :: l).length))) .acc (encN (p + m * bval (b :: l))) := by
      rw [hval, hpow]
      funext k
      by_cases k1 : k = .acc
      · subst k1; simp
      by_cases k2 : k = .mA
      · subst k2; simp
      by_cases k3 : k = .mB
      · subst k3; simp
      simp [k1, k2, k3, s3, s2, s1]
    rw [hfin] at ih'
    have hbody : Runs mulBody s s3 (27 * W + 27) :=
      (rb1.seq (rp.seq rb2)).mono (by omega)
    refine (Runs.loopT (by simp [hB, enc]) hbody ih').mono ?_
    simp only [List.length_cons]; ring_nf; omega

def mulProg (x y z : Key) : Prog :=
  .seq (copyProg x .mA .sc) (.seq (copyProg y .mB .sc) (.seq mulLoop (.seq (clearProg z)
    (.seq (transferProg .acc (fun k => decide (k = .sc)))
      (.seq (transferProg .sc (fun k => decide (k = z))) (clearProg .mA))))))

def MFree (k : Key) : Prop := AFree k ∧ k ≠ .mA ∧ k ≠ .mB ∧ k ≠ .acc

lemma runs_mul (x y z : Key) (hx : MFree x) (hy : MFree y) (hz : MFree z) (s : Store)
    (h1 : s .c1 = []) (h2 : s .c2 = []) (h3 : s .tmp = []) (h4 : s .car = []) (h5 : s .sc = [])
    (h6 : s .mA = []) (h7 : s .mB = []) (h8 : s .acc = [])
    (a b : ℕ) (ha : s x = encN a) (hb : s y = encN b) :
    Runs (mulProg x y z) s (Function.update s z (encN (a * b)))
      (30 * (sz a + sz b + 1) ^ 2 + 3 * (s z).length) := by
  obtain ⟨⟨hx1, hx2, hx3, hx4, hx5⟩, hx6, hx7, hx8⟩ := hx
  obtain ⟨⟨hy1, hy2, hy3, hy4, hy5⟩, hy6, hy7, hy8⟩ := hy
  obtain ⟨⟨hz1, hz2, hz3, hz4, hz5⟩, hz6, hz7, hz8⟩ := hz
  have r1 := runs_copy x .mA .sc hx6 hx5 (by decide) s h5
  set s1 := Function.update s .mA (s x ++ s .mA) with hs1
  have r2 := runs_copy y .mB .sc hy7 hy5 (by decide) s1 (by simp [s1, h5])
  set s2 := Function.update s1 .mB (s1 y ++ s1 .mB) with hs2
  set W := sz a + sz b
  have r3 := runs_mulLoop W (Nat.bits b) a 0 s2 (by simp [s2, s1, h1]) (by simp [s2, s1, h2])
    (by simp [s2, s1, h3]) (by simp [s2, s1, h4]) (by simp [s2, s1, h5])
    (by simp [s2, s1, hb, hy6, h7, encN]) (by simp [s2, s1, ha, h6]) (by simp [s2, s1, h8, encN_zero])
    (sz_mul_pow a _) (by rw [bval_bits, zero_add]; exact sz_mul_le a b)
  rw [bval_bits, zero_add] at r3
  set s3 := Function.update (Function.update (Function.update s2 .mB []) .mA
      (encN (a * 2 ^ (Nat.bits b).length))) .acc (encN (a * b))
  have r4 := runs_clear z s3
  set s4 := Function.update s3 z []
  have r5 := runs_move .acc .sc (by decide) s4
  set s5 := Function.update (Function.update s4 .acc []) .sc ((s4 .acc).reverse ++ s4 .sc)
  have r6 := runs_move .sc z (Ne.symm hz5) s5
  set s6 := Function.update (Function.update s5 .sc []) z ((s5 .sc).reverse ++ s5 z)
  have r7 := runs_clear .mA s6
  have e4acc : s4 .acc = encN (a * b) := by simp [s4, s3, Ne.symm hz8]
  have e4sc : s4 .sc = [] := by simp [s4, s3, Ne.symm hz5, s2, s1, h5]
  have e5sc : s5 .sc = (encN (a * b)).reverse := by simp [s5, e4acc, e4sc]
  have e5z : s5 z = [] := by simp [s5, hz8, hz5, s4]
  have e6mA : s6 .mA = encN (a * 2 ^ (Nat.bits b).length) := by
    simp [s6, s5, s4, s3, hz6.symm, Ne.symm hz6]
  have hfin : Function.update s6 .mA [] = Function.update s z (encN (a * b)) := by
    funext k
    by_cases k1 : k = z
    · subst k1; simp [s6, hz6, e5sc, e5z]
    by_cases k2 : k = .mA
    · subst k2; simp [Function.update_apply, k1, h6]
    by_cases k3 : k = .sc
    · subst k3; simp [s6, k1, h5]
    by_cases k4 : k = .acc
    · subst k4; simp [s6, s5, k1, h8]
    by_cases k5 : k = .mB
    · subst k5; simp [s6, s5, s4, s3, k1, h7]
    simp [s6, s5, s4, s3, s2, s1, k1, k2, k3, k4, k5]
  rw [hfin] at r7
  refine (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_
  have l1 : (s x).length = sz a := by rw [ha, length_encN']
  have l2 : (s1 y).length = sz b := by simp [s1, hy6, hb, length_encN']
  have l3 : (s3 z).length = (s z).length := by
    simp [s3, s2, s1, hz8, hz6, hz7]
  have l4 : (s4 .acc).length = sz (a * b) := by rw [e4acc, length_encN']
  have l5 : (s5 .sc).length = sz (a * b) := by rw [e5sc]; simp [length_encN']
  have l6 : (s6 .mA).length = sz (a * 2 ^ (Nat.bits b).length) := by rw [e6mA, length_encN']
  have q1 := sz_mul_le a b
  have q2 := sz_mul_pow a (Nat.bits b).length
  have q3 : (Nat.bits b).length = sz b := rfl
  simp only [l1, l2, l3, l4, l5, l6] at *
  rw [q3] at q2 ⊢
  have hsb : sz b * (27 * W + 30) ≤ W * (27 * W + 30) := Nat.mul_le_mul_right _ (by omega)
  have hW : W = sz a + sz b := rfl
  have hsq : (sz a + sz b + 1) ^ 2 = W * W + 2 * W + 1 := by rw [hW]; ring
  rw [hsq]
  have hexp : W * (27 * W + 30) = 27 * (W * W) + 30 * W := by ring
  rw [hexp] at hsb
  have q4 : sz b ≤ W := by omega
  nlinarith

/-! ## Reading a number from an input stack -/

def rdLoop (src : Key) : Prog :=
  .loop (fun h => isDig (h src)) (.act (transferAct src (fun k => decide (k = .tmp))))

lemma runs_rdLoop (src : Key) (hs : src ≠ .tmp) (r : List BSym) (hr : isDig r.head? = false) :
    ∀ (d : List Bool) (s : Store), s src = enc d ++ r →
    Runs (rdLoop src) s (Function.update (Function.update s src r) .tmp
      ((enc d).reverse ++ s .tmp)) (3 * d.length + 1) := by
  intro d
  induction d with
  | nil =>
    intro s h
    have : Function.update (Function.update s src r) .tmp ((enc []).reverse ++ s .tmp) = s := by
      funext k
      by_cases k1 : k = .tmp
      · subst k1; simp [enc]
      by_cases k2 : k = src
      · subst k2; simp [k1, h, enc]
      simp [k1, k2]
    rw [this]
    exact Runs.loopF (by simp only [h, enc, List.map_nil, List.nil_append]; exact hr)
  | cons b d ih =>
    intro s h
    set s1 := StackProg.applyAct (transferAct src (fun k => decide (k = .tmp))) s
    have e1 : s1 src = enc d ++ r := by
      simp [s1, StackProg.applyAct, transferAct, StackAct.apply, h, enc]
    have e2 : s1 .tmp = toB b :: s .tmp := by
      simp [s1, StackProg.applyAct, transferAct, StackAct.apply, h, enc, Ne.symm hs]
    have ih' := ih s1 e1
    have hpost : Function.update (Function.update s1 src r) .tmp ((enc d).reverse ++ s1 .tmp) =
        Function.update (Function.update s src r) .tmp ((enc (b :: d)).reverse ++ s .tmp) := by
      funext k
      by_cases k1 : k = .tmp
      · subst k1; simp [e2, enc]
      by_cases k2 : k = src
      · subst k2; simp [k1]
      simp [k1, k2, s1, StackProg.applyAct, transferAct, StackAct.apply]
    rw [hpost] at ih'
    refine (Runs.loopT (test := fun h => isDig (h src)) ?_ (Runs.act _ s) ih').mono
      (by simp; omega)
    show isDig (s src).head? = true
    rw [h]; cases b <;> rfl

def rdProg (src dst : Key) : Prog :=
  .seq (rdLoop src) (.seq (popProg src) (.seq (clearProg dst)
    (transferProg .tmp (fun k => decide (k = dst)))))

lemma runs_rd (src dst : Key) (hs : src ≠ .tmp) (hd : dst ≠ .tmp) (hsd : src ≠ dst) (s : Store)
    (htmp : s .tmp = []) (n : ℕ) (rest : List BSym) (h : s src = encNat n ++ rest) :
    Runs (rdProg src dst) s (Function.update (Function.update s src rest) dst (encN n))
      (6 * sz n + 3 * (s dst).length + 10) := by
  have h' : s src = enc (Nat.bits n) ++ (BSym.sep :: rest) := by
    rw [h, encNat_eq]; simp [encN]
  have r1 := runs_rdLoop src hs (BSym.sep :: rest) rfl (Nat.bits n) s h'
  set s1 := Function.update (Function.update s src (BSym.sep :: rest)) .tmp
    ((enc (Nat.bits n)).reverse ++ s .tmp)
  have r2 := runs_pop src s1
  set s2 := Function.update s1 src (s1 src).tail
  have r3 := runs_clear dst s2
  set s3 := Function.update s2 dst []
  have r4 := runs_move .tmp dst (Ne.symm hd) s3
  have e3 : s3 .tmp = (encN n).reverse := by
    simp [s3, s2, s1, Ne.symm hd, Ne.symm hs, htmp, encN]
  have hfin : Function.update (Function.update s3 .tmp []) dst ((s3 .tmp).reverse ++ s3 dst) =
      Function.update (Function.update s src rest) dst (encN n) := by
    rw [e3]
    funext k
    by_cases k1 : k = dst
    · subst k1; simp [s3]
    by_cases k2 : k = .tmp
    · subst k2; simp [k1, htmp, Ne.symm hs]
    by_cases k3 : k = src
    · subst k3; simp [k1, k2, s3, s2, s1]
    simp [k1, k2, k3, s3, s2, s1]
  rw [hfin] at r4
  refine (r1.seq (r2.seq (r3.seq r4))).mono ?_
  have l1 : (s2 dst).length = (s dst).length := by simp [s2, s1, hd, Ne.symm hsd]
  have l2 : (s3 .tmp).length = sz n := by rw [e3]; simp [length_encN']
  rw [l1, l2]; simp [sz]; omega

end P3R



namespace P3R

open CookPvsNP ProjSchedTW.Complexity
end P3R

namespace P3R

open CookPvsNP ProjSchedTW.Complexity

def isNum : Key → Bool
  | .ONE | .ZR | .A | .T | .Q | .X | .X2 | .S2 | .Q2 | .Y | .H => true
  | _ => false

def mk (v : Key → ℕ) (base : Store) : Store := fun k => if isNum k then encN (v k) else base k

def Clean (b : Store) : Prop :=
  b .c1 = [] ∧ b .c2 = [] ∧ b .tmp = [] ∧ b .car = [] ∧ b .sc = [] ∧ b .mA = [] ∧ b .mB = [] ∧
    b .acc = [] ∧ b .lt = [] ∧ b .gt = []

lemma num_free {k : Key} (h : isNum k = true) : MFree k ∧ k ≠ .lt ∧ k ≠ .gt := by
  cases k <;> simp [isNum] at h <;> refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> decide

lemma mk_num {v : Key → ℕ} {b : Store} {k : Key} (h : isNum k = true) : mk v b k = encN (v k) := by
  simp [mk, h]

lemma mk_base {v : Key → ℕ} {b : Store} {k : Key} (h : isNum k = false) : mk v b k = b k := by
  simp [mk, h]

lemma mk_upd_num {v : Key → ℕ} {b : Store} {k : Key} (h : isNum k = true) (n : ℕ) :
    Function.update (mk v b) k (encN n) = mk (Function.update v k n) b := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [mk, h]
  · simp [mk, hj]

lemma mk_upd_base {v : Key → ℕ} {b : Store} {k : Key} (h : isNum k = false) (l : List BSym) :
    Function.update (mk v b) k l = mk v (Function.update b k l) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [mk, h]
  · simp [mk, hj]

lemma Clean.upd {b : Store} (hc : Clean b) (k : Key) (l : List BSym)
    (hk : k ≠ .c1 ∧ k ≠ .c2 ∧ k ≠ .tmp ∧ k ≠ .car ∧ k ≠ .sc ∧ k ≠ .mA ∧ k ≠ .mB ∧ k ≠ .acc ∧
      k ≠ .lt ∧ k ≠ .gt) : Clean (Function.update b k l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Function.update_apply, Ne.symm k1, Ne.symm k2, Ne.symm k3, Ne.symm k4, Ne.symm k5,
      Ne.symm k6, Ne.symm k7, Ne.symm k8, Ne.symm k9, Ne.symm k10, *]

/-- scratch keys of `mk` stores. -/
lemma mk_scratch {v : Key → ℕ} {b : Store} (hc : Clean b) :
    mk v b .c1 = [] ∧ mk v b .c2 = [] ∧ mk v b .tmp = [] ∧ mk v b .car = [] ∧ mk v b .sc = [] ∧
    mk v b .mA = [] ∧ mk v b .mB = [] ∧ mk v b .acc = [] ∧ mk v b .lt = [] ∧ mk v b .gt = [] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hc
  simp only [mk, isNum, if_false]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

lemma mk_add (x y z : Key) (hx : isNum x = true) (hy : isNum y = true) (hz : isNum z = true)
    (v : Key → ℕ) (b : Store) (hc : Clean b) :
    Runs (addProg x y z) (mk v b) (mk (Function.update v z (v x + v y)) b)
      (12 * (sz (v x) + sz (v y)) + 3 * sz (v z) + 20) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := mk_scratch (v := v) hc
  have := runs_add x y z (num_free hx).1.1 (num_free hy).1.1 (num_free hz).1.1 (mk v b)
    h1 h2 h3 h4 h5 (v x) (v y) (mk_num hx) (mk_num hy)
  rw [mk_upd_num hz, mk_num hz, length_encN'] at this
  exact this

lemma mk_mul (x y z : Key) (hx : isNum x = true) (hy : isNum y = true) (hz : isNum z = true)
    (v : Key → ℕ) (b : Store) (hc : Clean b) :
    Runs (mulProg x y z) (mk v b) (mk (Function.update v z (v x * v y)) b)
      (30 * (sz (v x) + sz (v y) + 1) ^ 2 + 3 * sz (v z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := mk_scratch (v := v) hc
  have := runs_mul x y z (num_free hx).1 (num_free hy).1 (num_free hz).1 (mk v b)
    h1 h2 h3 h4 h5 h6 h7 h8 (v x) (v y) (mk_num hx) (mk_num hy)
  rw [mk_upd_num hz, mk_num hz, length_encN'] at this
  exact this

lemma mk_half (z : Key) (hz : isNum z = true) (v : Key → ℕ) (b : Store) :
    Runs (popProg z) (mk v b) (mk (Function.update v z (v z / 2)) b) 1 := by
  have := runs_pop z (mk v b)
  have e : (mk v b z).tail = encN (v z / 2) := by
    rw [mk_num hz]; simp [encN, enc, bits_div_two, List.map_tail]
  rw [e, mk_upd_num hz] at this
  exact this

lemma mk_clear (k : Key) (hk : isNum k = true) (v : Key → ℕ) (b : Store) :
    Runs (clearProg k) (mk v b) (mk (Function.update v k 0) b) (3 * sz (v k) + 1) := by
  have := runs_clear k (mk v b)
  rw [← encN_zero, mk_upd_num hk, mk_num hk, length_encN'] at this
  exact this

lemma mk_push (k : Key) (hk : isNum k = false) (a : BSym) (v : Key → ℕ) (b : Store) :
    Runs (pushProg k a) (mk v b) (mk v (Function.update b k (a :: b k))) 1 := by
  have := runs_push k a (mk v b)
  rw [mk_base hk, mk_upd_base hk] at this
  exact this

lemma mk_pop (k : Key) (hk : isNum k = false) (v : Key → ℕ) (b : Store) :
    Runs (popProg k) (mk v b) (mk v (Function.update b k (b k).tail)) 1 := by
  have := runs_pop k (mk v b)
  rw [mk_base hk, mk_upd_base hk] at this
  exact this

lemma mk_rd (src dst : Key) (hs : isNum src = false) (hst : src ≠ .tmp) (hd : isNum dst = true)
    (v : Key → ℕ) (b : Store) (hc : Clean b) (n : ℕ) (rest : List BSym)
    (h : b src = encNat n ++ rest) :
    Runs (rdProg src dst) (mk v b) (mk (Function.update v dst n) (Function.update b src rest))
      (6 * sz n + 3 * sz (v dst) + 10) := by
  obtain ⟨-, -, h3, -⟩ := mk_scratch (v := v) hc
  have hsd : src ≠ dst := by intro e; subst e; rw [hs] at hd; exact absurd hd (by decide)
  have := runs_rd src dst hst (num_free hd).1.1.2.2.1 hsd (mk v b) h3 n rest
    (by rw [mk_base hs]; exact h)
  rw [mk_upd_base hs, mk_upd_num hd, mk_num hd, length_encN'] at this
  exact this

def emitP (k : Key) : Prog :=
  .seq (transferProg k (fun j => decide (j = .R))) (pushProg .R .sep)

lemma mk_emit (k : Key) (hk : isNum k = true) (v : Key → ℕ) (b : Store) :
    Runs (emitP k) (mk v b) (mk (Function.update v k 0)
      (Function.update b .R ((encNat (v k)).reverse ++ b .R))) (3 * sz (v k) + 3) := by
  have hkR : k ≠ .R := by intro e; subst e; exact absurd hk (by decide)
  have r1 := runs_move k .R hkR (mk v b)
  have e1 : Function.update (Function.update (mk v b) k []) .R ((mk v b k).reverse ++ mk v b .R) =
      mk (Function.update v k 0) (Function.update b .R ((encN (v k)).reverse ++ b .R)) := by
    rw [← encN_zero, mk_upd_num hk, mk_num hk, mk_base (k := .R) rfl,
      mk_upd_base (k := .R) rfl]
  rw [e1] at r1
  have r2 := mk_push .R rfl .sep (Function.update v k 0)
    (Function.update b .R ((encN (v k)).reverse ++ b .R))
  have e2 : Function.update (Function.update b .R ((encN (v k)).reverse ++ b .R)) .R
      (BSym.sep :: Function.update b .R ((encN (v k)).reverse ++ b .R) .R) =
      Function.update b .R ((encNat (v k)).reverse ++ b .R) := by
    simp [encNat_eq]
  rw [e2] at r2
  refine (r1.seq r2).mono ?_
  rw [mk_num hk, length_encN']

/-! ## Straight-line operation lists -/

inductive Op
  | add (x y z : Key)
  | mul (x y z : Key)
  | half (z : Key)

def Op.prog : Op → Prog
  | .add x y z => addProg x y z
  | .mul x y z => mulProg x y z
  | .half z => popProg z

def Op.eval : Op → (Key → ℕ) → (Key → ℕ)
  | .add x y z, v => Function.update v z (v x + v y)
  | .mul x y z, v => Function.update v z (v x * v y)
  | .half z, v => Function.update v z (v z / 2)

def Op.ok : Op → Bool
  | .add x y z => isNum x && isNum y && isNum z
  | .mul x y z => isNum x && isNum y && isNum z
  | .half z => isNum z

def Op.cost : Op → (Key → ℕ) → ℕ
  | .add x y z, v => 30 * (sz (v x) + sz (v y) + sz (v z) + 1) ^ 2
  | .mul x y z, v => 30 * (sz (v x) + sz (v y) + sz (v z) + 1) ^ 2
  | .half _, _ => 1

lemma op_runs (o : Op) (ho : o.ok = true) (v : Key → ℕ) (b : Store) (hc : Clean b) :
    Runs o.prog (mk v b) (mk (o.eval v) b) (o.cost v) := by
  cases o with
  | add x y z =>
    simp only [Op.ok, Bool.and_eq_true] at ho
    refine (mk_add x y z ho.1.1 ho.1.2 ho.2 v b hc).mono ?_
    simp only [Op.cost]
    nlinarith
  | mul x y z =>
    simp only [Op.ok, Bool.and_eq_true] at ho
    refine (mk_mul x y z ho.1.1 ho.1.2 ho.2 v b hc).mono ?_
    simp only [Op.cost]
    generalize sz (v x) + sz (v y) = S
    generalize sz (v z) = Z
    have : (S + 1) ^ 2 + Z ≤ (S + Z + 1) ^ 2 := by
      have e : (S + Z + 1) ^ 2 = (S + 1) ^ 2 + Z * (2 * S + 2 + Z) := by ring
      rw [e]; have : Z ≤ Z * (2 * S + 2 + Z) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    omega
  | half z => exact mk_half z ho v b

def progL : List Op → Prog
  | [] => skipP
  | o :: os => .seq o.prog (progL os)

def evalL : List Op → (Key → ℕ) → (Key → ℕ)
  | [], v => v
  | o :: os, v => evalL os (o.eval v)

def costL : List Op → (Key → ℕ) → ℕ
  | [], _ => 1
  | o :: os, v => o.cost v + costL os (o.eval v) + 1

lemma opsL_runs (os : List Op) (ho : ∀ o ∈ os, o.ok = true) (v : Key → ℕ) (b : Store)
    (hc : Clean b) : Runs (progL os) (mk v b) (mk (evalL os v) b) (costL os v) := by
  induction os generalizing v with
  | nil => exact runs_skip _
  | cons o os ih =>
    exact (op_runs o (ho o (by simp)) v b hc).seq (ih (fun o h => ho o (by simp [h])) _)

def Bd (W : ℕ) (v : Key → ℕ) : Prop := ∀ k, sz (v k) ≤ W

lemma Bd.eval {W : ℕ} {v : Key → ℕ} (h : Bd W v) (o : Op) : Bd (2 * W + 1) (o.eval v) := by
  intro k
  cases o with
  | add x y z =>
    simp only [Op.eval, Function.update_apply]
    split_ifs
    · have := sz_add_le (v x) (v y); have := h x; have := h y; omega
    · have := h k; omega
  | mul x y z =>
    simp only [Op.eval, Function.update_apply]
    split_ifs
    · have := sz_mul_le (v x) (v y); have := h x; have := h y; omega
    · have := h k; omega
  | half z =>
    simp only [Op.eval, Function.update_apply]
    split_ifs
    · have := sz_div2 (v z); have := h z; omega
    · have := h k; omega

lemma Bd.cost {W : ℕ} {v : Key → ℕ} (h : Bd W v) (o : Op) : o.cost v ≤ 30 * (3 * W + 1) ^ 2 := by
  cases o with
  | add x y z =>
    simp only [Op.cost]
    have := h x; have := h y; have := h z
    have : sz (v x) + sz (v y) + sz (v z) + 1 ≤ 3 * W + 1 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  | mul x y z =>
    simp only [Op.cost]
    have := h x; have := h y; have := h z
    have : sz (v x) + sz (v y) + sz (v z) + 1 ≤ 3 * W + 1 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  | half z =>
    simp only [Op.cost]
    have : 1 ≤ (3 * W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

lemma Bd.mono {W W' : ℕ} {v : Key → ℕ} (h : Bd W v) (hW : W ≤ W') : Bd W' v :=
  fun k => le_trans (h k) hW

lemma costL_le (os : List Op) : ∀ (W : ℕ) (v : Key → ℕ), Bd W v →
    costL os v ≤ (os.length + 1) * (30 * (3 * (2 ^ os.length * (W + 1)) + 1) ^ 2 + 1) := by
  induction os with
  | nil => intro W v _; simp [costL]
  | cons o os ih =>
    intro W v h
    have h1 := h.cost o
    have h2 := ih (2 * W + 1) (o.eval v) (h.eval o)
    simp only [costL, List.length_cons]
    have e : 2 ^ os.length * (2 * W + 1 + 1) = 2 ^ (os.length + 1) * (W + 1) := by
      rw [pow_succ]; ring
    rw [e] at h2
    have h3 : 3 * W + 1 ≤ 3 * (2 ^ (os.length + 1) * (W + 1)) + 1 := by
      have : 1 ≤ 2 ^ (os.length + 1) := Nat.one_le_two_pow
      nlinarith
    have h4 := Nat.pow_le_pow_left h3 2
    nlinarith

lemma Bd_evalL (os : List Op) : ∀ (W : ℕ) (v : Key → ℕ), Bd W v →
    Bd (2 ^ os.length * (W + 1)) (evalL os v) := by
  induction os with
  | nil => intro W v h; simp only [evalL, List.length_nil, pow_zero, one_mul]; exact h.mono (by omega)
  | cons o os ih =>
    intro W v h
    have := ih (2 * W + 1) (o.eval v) (h.eval o)
    simp only [evalL, List.length_cons]
    have e : 2 ^ os.length * (2 * W + 1 + 1) = 2 ^ (os.length + 1) * (W + 1) := by
      rw [pow_succ]; ring
    rw [e] at this; exact this

end P3R



namespace P3R

open CookPvsNP ProjSchedTW.Complexity

lemma encNats_cons (n : ℕ) (l : List ℕ) : encNats (n :: l) = encNat n ++ encNats l := by
  simp [encNats]

lemma encNats_append (l1 l2 : List ℕ) : encNats (l1 ++ l2) = encNats l1 ++ encNats l2 := by
  simp [encNats]
lemma clean_inp {b : Store} (hc : Clean b) (l : List BSym) : Clean (Function.update b .inp l) :=
  hc.upd _ _ (by decide)

lemma clean_inp2 {b : Store} (hc : Clean b) (l : List BSym) : Clean (Function.update b .inp2 l) :=
  hc.upd _ _ (by decide)

lemma clean_R {b : Store} (hc : Clean b) (l : List BSym) : Clean (Function.update b .R l) :=
  hc.upd _ _ (by decide)

lemma clean_out {b : Store} (hc : Clean b) (l : List BSym) : Clean (Function.update b .out l) :=
  hc.upd _ _ (by decide)

/-! ## The validation automaton: pending digits, last digit is one, bad -/

def vstep : Bool × Bool × Bool → BSym → Bool × Bool × Bool
  | (_, _, bd), .zero => (true, false, bd)
  | (_, _, bd), .one => (true, true, bd)
  | (p, l, _), .minus => (p, l, true)
  | (_, l, bd), .sep => (false, false, bd || !l)

def vOK (x : List BSym) : Prop :=
  (x.foldl vstep (false, false, false)).2.2 = false ∧
    (x.foldl vstep (false, false, false)).1 = false

lemma bad_mono (y : List BSym) : ∀ (p l : Bool), (y.foldl vstep (p, l, true)).2.2 = true := by
  induction y with
  | nil => intro p l; rfl
  | cons a y ih => intro p l; cases a <;> simp [vstep, ih]

lemma canon_iff (d : List Bool) : Canon d ↔ d = [] ∨ d.getLast? = some true := by
  induction d with
  | nil => simp [Canon]
  | cons b d ih =>
    simp only [Canon, ih]
    rcases d with _ | ⟨c, d⟩
    · simp
    · simp [List.getLast?_cons_cons]

def stOf (d : List Bool) : Bool × Bool × Bool := (!d.isEmpty, d.getLast? == some true, false)

lemma toB_val (b : Bool) : (if b then BSym.one else BSym.zero) = toB b := rfl

lemma vOK_decode : ∀ (x : List BSym) (d : List Bool),
    (x.foldl vstep (stOf d)).2.2 = false → (x.foldl vstep (stOf d)).1 = false →
    ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ enc d ++ x = encNats l := by
  intro x
  induction x with
  | nil =>
    intro d _ h1
    simp only [List.foldl_nil, stOf, Bool.not_eq_false', List.isEmpty_iff] at h1
    subst h1
    exact ⟨[], by simp, by simp [enc, encNats]⟩
  | cons a x ih =>
    intro d h2 h1
    cases a with
    | zero =>
      have e : vstep (stOf d) .zero = stOf (d ++ [false]) := by simp [vstep, stOf]
      rw [List.foldl_cons, e] at h1 h2
      obtain ⟨l, hl, he⟩ := ih _ h2 h1
      exact ⟨l, hl, by rw [← he]; simp [enc, toB]⟩
    | one =>
      have e : vstep (stOf d) .one = stOf (d ++ [true]) := by simp [vstep, stOf]
      rw [List.foldl_cons, e] at h1 h2
      obtain ⟨l, hl, he⟩ := ih _ h2 h1
      exact ⟨l, hl, by rw [← he]; simp [enc, toB]⟩
    | minus =>
      exfalso
      have e : vstep (stOf d) .minus = (!d.isEmpty, d.getLast? == some true, true) := by
        simp [vstep, stOf]
      rw [List.foldl_cons, e, bad_mono] at h2
      exact absurd h2 (by decide)
    | sep =>
      by_cases hd : d.getLast? = some true
      · have e : vstep (stOf d) .sep = stOf [] := by simp [vstep, stOf, hd]
        rw [List.foldl_cons, e] at h1 h2
        obtain ⟨l, hl, he⟩ := ih _ h2 h1
        simp only [enc, List.map_nil, List.nil_append] at he
        have hc : Canon d := (canon_iff d).2 (Or.inr hd)
        have hne : d ≠ [] := by intro h; subst h; simp at hd
        refine ⟨bval d :: l, ?_, ?_⟩
        · intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact bval_pos hc hne
          · exact hl v hv
        · rw [encNats_cons, encNat_eq, encN, bits_bval hc, ← he]; simp
      · exfalso
        have e : vstep (stOf d) .sep = (false, false, true) := by simp [vstep, stOf, hd]
        rw [List.foldl_cons, e, bad_mono] at h2
        exact absurd h2 (by decide)

lemma foldl_enc (d : List Bool) (hd : d ≠ []) : ∀ (p l bd : Bool),
    (enc d).foldl vstep (p, l, bd) = (true, d.getLast hd, bd) := by
  induction d with
  | nil => exact absurd rfl hd
  | cons b d ih =>
    intro p l bd
    by_cases h : d = []
    · subst h; cases b <;> simp [enc, toB, vstep]
    · simp only [enc, List.map_cons, List.foldl_cons] at ih ⊢
      cases b <;> simp only [toB, vstep] <;> rw [ih h] <;> simp [List.getLast_cons h]

lemma foldl_encNats (l : List ℕ) (hl : ∀ v ∈ l, 0 < v) : ∀ (p q bd : Bool),
    l ≠ [] → (encNats l).foldl vstep (p, q, bd) = (false, false, bd) := by
  induction l with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons v l ih =>
    intro p q bd _
    have hv : 0 < v := hl v (by simp)
    have hne : Nat.bits v ≠ [] := by
      intro h; have := bval_bits v; rw [h] at this; simp [bval] at this; omega
    have hlast : (Nat.bits v).getLast hne = true := by
      have := (canon_iff _).1 (canon_bits_bval v).1
      rcases this with h | h
      · exact absurd h hne
      · rw [List.getLast?_eq_some_getLast hne] at h; simpa using h
    rw [encNats_cons, encNat_eq, List.foldl_append, List.foldl_append, encN, foldl_enc _ hne,
      hlast]
    simp only [List.foldl_cons, List.foldl_nil, vstep, Bool.not_true, Bool.or_false]
    by_cases h : l = []
    · subst h; simp [encNats]
    · exact ih (fun w hw => hl w (by simp [hw])) _ _ _ h

lemma vOK_iff (x : List BSym) :
    vOK x ↔ ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ x = encNats l := by
  constructor
  · rintro ⟨h2, h1⟩
    have := vOK_decode x [] (by simpa [stOf] using h2) (by simpa [stOf] using h1)
    obtain ⟨l, hl, he⟩ := this
    simp only [enc, List.map_nil, List.nil_append] at he
    exact ⟨l, hl, he⟩
  · rintro ⟨l, hl, rfl⟩
    by_cases hne : l = []
    · subst hne; exact ⟨rfl, rfl⟩
    have := foldl_encNats l hl false false false hne
    exact ⟨by rw [this], by rw [this]⟩

/-! ## The validation loop -/

def vAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  let st := vstep ((h .pend).isSome, (h .last1).isSome, (h .bad).isSome) ((h .inpC).getD .sep)
  if k = .inpC then .pop
  else if k = .pend then setFlag (h .pend).isSome st.1
  else if k = .last1 then setFlag (h .last1).isSome st.2.1
  else if k = .bad then setFlag (h .bad).isSome st.2.2
  else .keep

def valLoop : Prog := .loop (fun h => (h .inpC).isSome) (.act vAct)

def vPost (st : Bool × Bool × Bool) (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s .inpC []) .pend
    (flag st.1)) .last1 (flag st.2.1)) .bad (flag st.2.2)

lemma runs_valLoop : ∀ (x : List BSym) (st : Bool × Bool × Bool) (s : Store),
    s .inpC = x → s .pend = flag st.1 → s .last1 = flag st.2.1 → s .bad = flag st.2.2 →
    Runs valLoop s (vPost (x.foldl vstep st) s) (3 * x.length + 1) := by
  intro x
  induction x with
  | nil =>
    intro st s h0 h1 h2 h3
    have : vPost (([] : List BSym).foldl vstep st) s = s := by
      funext k
      simp only [vPost, List.foldl_nil, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    rw [this]
    exact Runs.loopF (by simp [h0])
  | cons a x ih =>
    intro st s h0 h1 h2 h3
    obtain ⟨p, l, bd⟩ := st
    set st' := vstep (p, l, bd) a
    set s1 := StackProg.applyAct vAct s
    have hp : ((s .pend).head?).isSome = p := by rw [h1]; exact flag_isSome p
    have hl : ((s .last1).head?).isSome = l := by rw [h2]; exact flag_isSome l
    have hb : ((s .bad).head?).isSome = bd := by rw [h3]; exact flag_isSome bd
    have ha : ((s .inpC).head?).getD .sep = a := by rw [h0]; rfl
    have e0 : s1 .inpC = x := by simp [s1, StackProg.applyAct, vAct, StackAct.apply, h0]
    have e1 : s1 .pend = flag st'.1 := by
      simp only [s1, StackProg.applyAct, vAct, hp, hl, hb, ha]; simp only [reduceCtorEq,
        if_false, if_true]; rw [h1]; exact setFlag_apply _ _
    have e2 : s1 .last1 = flag st'.2.1 := by
      simp only [s1, StackProg.applyAct, vAct, hp, hl, hb, ha]; simp only [reduceCtorEq,
        if_false, if_true]; rw [h2]; exact setFlag_apply _ _
    have e3 : s1 .bad = flag st'.2.2 := by
      simp only [s1, StackProg.applyAct, vAct, hp, hl, hb, ha]; simp only [reduceCtorEq,
        if_false, if_true]; rw [h3]; exact setFlag_apply _ _
    have e4 : ∀ k, k ≠ .inpC → k ≠ .pend → k ≠ .last1 → k ≠ .bad → s1 k = s k := by
      intro k k1 k2 k3 k4
      simp [s1, StackProg.applyAct, vAct, k1, k2, k3, k4, StackAct.apply]
    have ih' := ih st' s1 e0 e1 e2 e3
    have hpost : vPost (x.foldl vstep st') s1 = vPost ((a :: x).foldl vstep (p, l, bd)) s := by
      rw [List.foldl_cons]
      funext k
      simp only [vPost, Function.update_apply]
      by_cases k1 : k = .bad
      · simp [k1, st']
      by_cases k2 : k = .last1
      · simp [k2, st']
      by_cases k3 : k = .pend
      · simp [k3, st']
      by_cases k4 : k = .inpC
      · simp [k4]
      simp [k1, k2, k3, k4, e4 k k4 k3 k2 k1]
    rw [hpost] at ih'
    exact (Runs.loopT (by simp [h0]) (Runs.act vAct s) ih').mono (by simp; omega)

def phaseA : Prog :=
  .seq (copyProg .inp .inpC .sc) (.seq valLoop
    (.branch (fun h => (h .pend).isSome) (pushProg .bad .one) skipP))

def s0 (x : List BSym) : Store := fun j => if j = .inp then x else []

lemma runs_phaseA (x : List BSym) : ∃ sA, Runs phaseA (s0 x) sA (9 * x.length + 12) ∧
    sA .out = [] ∧ ((sA .bad).head?.isSome = true ↔ ¬ vOK x) ∧ (vOK x → sA = s0 x) := by
  have r1 := runs_copy .inp .inpC .sc (by decide) (by decide) (by decide) (s0 x) (by simp [s0])
  set s1 := Function.update (s0 x) .inpC (s0 x .inp ++ s0 x .inpC)
  have hs1 : s1 .inpC = x := by simp [s1, s0]
  set st := x.foldl vstep (false, false, false)
  have r3 := runs_valLoop x (false, false, false) s1 hs1
    (by simp [s1, s0, flag]) (by simp [s1, s0, flag]) (by simp [s1, s0, flag])
  set s3 := vPost st s1
  set sA := if st.1 then Function.update s3 .bad (BSym.one :: s3 .bad) else s3
  have r4 : Runs (.branch (fun h => (h .pend).isSome) (pushProg .bad .one) skipP) s3 sA 2 := by
    by_cases hp : st.1 = true
    · have := runs_push .bad .one s3
      simp only [sA, hp, if_true]
      exact Runs.brT (by simp [s3, vPost, hp, flag]) this
    · simp only [sA, hp]
      exact Runs.brF (by simp [s3, vPost, flag]; simpa using hp) (runs_skip s3)
  refine ⟨sA, (r1.seq (r3.seq r4)).mono ?_, ?_, ?_, ?_⟩
  · simp [s0, hs1]; omega
  · simp only [sA]; split_ifs <;> simp [s3, vPost, s1, s0]
  · have hbad : (sA .bad).head?.isSome = (st.2.2 || st.1) := by
      simp only [sA]; split_ifs with h <;> simp [s3, vPost, h, flag] <;> cases st.2.2 <;> rfl
    rw [hbad]
    unfold vOK
    simp only [st]
    cases (x.foldl vstep (false, false, false)).2.2 <;>
      cases (x.foldl vstep (false, false, false)).1 <;> simp
  · intro hv
    have hst : st = (false, false, false) := by
      obtain ⟨h2, h1⟩ := hv
      simp only [st]
      rcases e : x.foldl vstep (false, false, false) with ⟨a, b, c⟩
      rw [e] at h1 h2
      simp only at h1 h2
      subst h1 h2
      cases b
      · rfl
      · exfalso
        obtain ⟨l, hl, hx⟩ := (vOK_iff x).1 ⟨by rw [e], by rw [e]⟩
        by_cases hne : l = []
        · subst hne; subst hx; simp [encNats] at e
        · rw [hx, foldl_encNats l hl false false false hne] at e; simp at e
    have hsA : sA = s3 := by simp [sA, hst]
    rw [hsA]
    funext k
    by_cases k1 : k = .bad
    · subst k1; simp [s3, vPost, hst, flag, s0]
    by_cases k2 : k = .last1
    · subst k2; simp [s3, vPost, hst, flag, s0]
    by_cases k3 : k = .pend
    · subst k3; simp [s3, vPost, hst, flag, s0]
    by_cases k4 : k = .inpC
    · subst k4; simp [s3, vPost, s0]
    simp [s3, vPost, s1, k1, k2, k3, k4]

end P3R



namespace P3R

open CookPvsNP ProjSchedTW.Complexity

/-! ## Injectivity of the codes -/

lemma isDig_sep (r : List BSym) : isDig (BSym.sep :: r).head? = false := rfl

lemma enc_append_inj {y y' : List Bool} {r r' : List BSym} (hr : isDig r.head? = false)
    (hr' : isDig r'.head? = false) (h : enc y ++ r = enc y' ++ r') : y = y' ∧ r = r' := by
  induction y generalizing y' with
  | nil =>
    rcases y' with _ | ⟨b, y'⟩
    · simpa [enc] using h
    · exfalso; simp [enc] at h; subst h; cases b <;> simp [toB, isDig] at hr
  | cons b y ih =>
    rcases y' with _ | ⟨b', y'⟩
    · exfalso; simp [enc] at h; subst h; cases b <;> simp [toB, isDig] at hr'
    · simp only [enc, List.map_cons, List.cons_append, List.cons.injEq] at h
      have hb : b = b' := by cases b <;> cases b' <;> simp_all [toB]
      obtain ⟨h1, h2⟩ := ih (y' := y') h.2
      exact ⟨by rw [hb, h1], h2⟩

lemma encNat_append_inj {v v' : ℕ} {r r' : List BSym} (h : encNat v ++ r = encNat v' ++ r') :
    v = v' ∧ r = r' := by
  rw [encNat_eq, encNat_eq] at h
  simp only [encN, List.append_assoc, List.singleton_append] at h
  obtain ⟨h1, h2⟩ := enc_append_inj (isDig_sep r) (isDig_sep r') h
  refine ⟨?_, by simpa using h2⟩
  rw [← bval_bits v, ← bval_bits v', h1]

lemma encNats_inj : ∀ {l l' : List ℕ}, encNats l = encNats l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rcases l' with _ | ⟨v, l'⟩
    · rfl
    · rw [encNats_cons, encNat_eq] at h; simp [encNats] at h
  | cons v l ih =>
    intro l' h
    rcases l' with _ | ⟨v', l'⟩
    · rw [encNats_cons, encNat_eq] at h; simp [encNats] at h
    · rw [encNats_cons, encNats_cons] at h
      obtain ⟨h1, h2⟩ := encNat_append_inj h
      rw [h1, ih h2]

/-! ## Size facts -/

lemma len_encNats_cons (v : ℕ) (l : List ℕ) :
    (encNats (v :: l)).length = sz v + 1 + (encNats l).length := by
  rw [encNats_cons, encNat_eq]; simp [length_encN']; omega

lemma sz_le_self (n : ℕ) : sz n ≤ n := by
  rw [sz_le_iff]; exact Nat.lt_two_pow_self

lemma sum_lt_pow (l : List ℕ) : l.sum < 2 ^ (encNats l).length := by
  induction l with
  | nil => simp [encNats]
  | cons v l ih =>
    rw [len_encNats_cons, List.sum_cons]
    have h1 := lt_pow_sz v
    have h2 : 2 ^ sz v ≤ 2 ^ (sz v + (encNats l).length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (encNats l).length ≤ 2 ^ (sz v + (encNats l).length) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show sz v + 1 + (encNats l).length = (sz v + (encNats l).length) + 1 by ring, pow_succ]
    omega

lemma length_le_encNats (l : List ℕ) : l.length ≤ (encNats l).length := by
  induction l with
  | nil => simp
  | cons v l ih => rw [len_encNats_cons]; simp; omega

lemma sz_le_of_mem {v : ℕ} {l : List ℕ} (h : v ∈ l) : sz v ≤ (encNats l).length := by
  induction l with
  | nil => simp at h
  | cons w l ih =>
    rw [len_encNats_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

lemma len_encNats_le (l : List ℕ) (Z : ℕ) (h : ∀ v ∈ l, sz v ≤ Z) :
    (encNats l).length ≤ l.length * (Z + 1) := by
  induction l with
  | nil => simp [encNats]
  | cons v l ih =>
    rw [len_encNats_cons]
    have := h v (by simp)
    have := ih (fun w hw => h w (by simp [hw]))
    simp only [List.length_cons]; nlinarith

lemma encN_one : encN 1 = [BSym.one] := by
  have : (1 : ℕ) = Nat.bit true 0 := rfl
  rw [this, encN, Nat.bits_append_bit _ _ (fun _ => rfl)]; rfl

lemma encN_three : encN 3 = [BSym.one, BSym.one] := by
  have : (3 : ℕ) = Nat.bit true 1 := rfl
  rw [this, encN, Nat.bits_append_bit _ _ (fun h => absurd h (by norm_num))]
  have h1 : (1 : ℕ) = Nat.bit true 0 := rfl
  rw [h1, Nat.bits_append_bit _ _ (fun _ => rfl)]; rfl

lemma mk_pushNum (k : Key) (hk : isNum k = true) (v : Key → ℕ) (b : Store) (n : ℕ)
    (h : BSym.one :: encN (v k) = encN n) :
    Runs (pushProg k .one) (mk v b) (mk (Function.update v k n) b) 1 := by
  have := runs_push k .one (mk v b)
  rw [mk_num hk, h, mk_upd_num hk] at this
  exact this

lemma mk_copyBase (src dst : Key) (hs : isNum src = false) (hd : isNum dst = false)
    (h1 : src ≠ dst) (h2 : src ≠ .sc) (h3 : dst ≠ .sc) (v : Key → ℕ) (b : Store)
    (hc : Clean b) :
    Runs (copyProg src dst .sc) (mk v b) (mk v (Function.update b dst (b src ++ b dst)))
      (6 * (b src).length + 3) := by
  have := runs_copy src dst .sc h1 h2 h3 (mk v b) (by simpa [mk, isNum] using hc.2.2.2.2.1)
  rw [mk_base hs, mk_base hd, mk_upd_base hd] at this
  exact this

end P3R
namespace P3R

open CookPvsNP ProjSchedTW.Complexity

/-! ## First pass over the items: `A = Σ a`, `t`, `Q = Σ a²` -/

def sqs (l : List ℕ) : ℕ := (l.map (fun n => n * n)).sum

lemma sqs_cons (n : ℕ) (l : List ℕ) : sqs (n :: l) = n * n + sqs l := by simp [sqs]

lemma sqs_le (l : List ℕ) : sqs l ≤ l.sum * l.sum := by
  induction l with
  | nil => simp [sqs]
  | cons n l ih => rw [sqs_cons, List.sum_cons]; nlinarith [ih, Nat.zero_le (n * l.sum)]

def body1 : Prog :=
  .seq (rdProg .inp .X) (.seq (addProg .A .X .A) (.seq (addProg .T .ONE .T)
    (.seq (mulProg .X .X .X2) (.seq (addProg .Q .X2 .Q) (.seq (clearProg .X) (clearProg .X2))))))

def loop1 : Prog := .loop (fun h => (h .inp).isSome) body1

lemma runs_loop1 (W : ℕ) : ∀ (rest : List ℕ) (v : Key → ℕ) (b : Store), Clean b →
    b .inp = encNats rest → v .X = 0 → v .X2 = 0 → v .ONE = 1 →
    sz (v .A + rest.sum) ≤ W → sz (v .T + rest.length) ≤ W → sz (v .Q + sqs rest) ≤ W →
    (∀ n ∈ rest, sz n ≤ W) →
    Runs loop1 (mk v b) (mk (Function.update (Function.update (Function.update v .A
      (v .A + rest.sum)) .T (v .T + rest.length)) .Q (v .Q + sqs rest))
      (Function.update b .inp [])) (rest.length * (300 * (W + 1) ^ 2) + 1) := by
  intro rest
  induction rest with
  | nil =>
    intro v b hc hb hX hX2 hO _ _ _ _
    have e1 : Function.update (Function.update (Function.update v .A
      (v .A + ([] : List ℕ).sum)) .T (v .T + ([] : List ℕ).length)) .Q
        (v .Q + sqs []) = v := by
      simp [sqs]
    have e2 : Function.update b .inp [] = b := by
      rw [Function.update_eq_self_iff]; simpa [encNats] using hb
    rw [e1, e2]
    exact (Runs.loopF (by simp [mk, isNum, hb, encNats])).mono (by simp)
  | cons n rest ih =>
    intro v b hc hb hX hX2 hO hA hT hQ hall
    have hb' : b .inp = encNat n ++ encNats rest := by rw [hb, encNats_cons]
    have hn : sz n ≤ W := hall n (by simp)
    have hvA : sz (v .A) ≤ W := le_trans (sz_mono (by simp)) hA
    have hvT : sz (v .T) ≤ W := le_trans (sz_mono (by simp)) hT
    have hvQ : sz (v .Q) ≤ W := le_trans (sz_mono (by simp)) hQ
    have hnn : sz (n * n) ≤ W := le_trans (sz_mono (by rw [sqs_cons]; omega)) hQ
    have r1 := mk_rd .inp .X rfl (by decide) rfl v b hc n (encNats rest) hb'
    set b1 := Function.update b .inp (encNats rest)
    have hc1 : Clean b1 := clean_inp hc _
    set v1 := Function.update v .X n
    have r2 := mk_add .A .X .A rfl rfl rfl v1 b1 hc1
    set v2 := Function.update v1 .A (v1 .A + v1 .X)
    have r3 := mk_add .T .ONE .T rfl rfl rfl v2 b1 hc1
    set v3 := Function.update v2 .T (v2 .T + v2 .ONE)
    have r4 := mk_mul .X .X .X2 rfl rfl rfl v3 b1 hc1
    set v4 := Function.update v3 .X2 (v3 .X * v3 .X)
    have r5 := mk_add .Q .X2 .Q rfl rfl rfl v4 b1 hc1
    set v5 := Function.update v4 .Q (v4 .Q + v4 .X2)
    have r6 := mk_clear .X rfl v5 b1
    set v6 := Function.update v5 .X 0
    have r7 := mk_clear .X2 rfl v6 b1
    set v7 := Function.update v6 .X2 0
    have q1 : v7 .A = v .A + n := by simp [v7, v6, v5, v4, v3, v2, v1]
    have q2 : v7 .T = v .T + 1 := by simp [v7, v6, v5, v4, v3, v2, v1, hO]
    have q3 : v7 .Q = v .Q + n * n := by simp [v7, v6, v5, v4, v3, v2, v1]
    have ih' := ih v7 b1 hc1 (by simp [b1]) (by simp [v7, v6]) (by simp [v7])
      (by simp [v7, v6, v5, v4, v3, v2, v1, hO])
      (by rw [q1]; refine le_trans (le_of_eq ?_) hA; congr 1; simp; ring)
      (by rw [q2]; refine le_trans (le_of_eq ?_) hT; congr 1; simp; ring)
      (by rw [q3]; refine le_trans (le_of_eq ?_) hQ; congr 1; rw [sqs_cons]; ring)
      (fun m hm => hall m (by simp [hm]))
    have hfin : mk (Function.update (Function.update (Function.update v7 .A (v7 .A + rest.sum))
        .T (v7 .T + rest.length)) .Q (v7 .Q + sqs rest)) (Function.update b1 .inp []) =
        mk (Function.update (Function.update (Function.update v .A (v .A + (n :: rest).sum))
        .T (v .T + (n :: rest).length)) .Q (v .Q + sqs (n :: rest)))
        (Function.update b .inp []) := by
      rw [q1, q2, q3]
      have : Function.update b1 .inp [] = Function.update b .inp [] := by simp [b1]
      rw [this]
      congr 1
      funext k
      simp only [Function.update_apply, List.sum_cons, List.length_cons, sqs_cons]
      by_cases k1 : k = .Q
      · simp [k1]; ring
      by_cases k2 : k = .T
      · simp [k2]; ring
      by_cases k3 : k = .A
      · simp [k3]; ring
      by_cases k4 : k = .X
      · subst k4; simp [v7, v6, hX]
      by_cases k5 : k = .X2
      · subst k5; simp [v7, hX2]
      simp [k1, k2, k3, k4, k5, v7, v6, v5, v4, v3, v2, v1]
    rw [hfin] at ih'
    have hbody : Runs body1 (mk v b) (mk v7 b1) (300 * (W + 1) ^ 2 - 2) := by
      refine (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_
      have s1 : sz (v1 .X) = sz n := by simp [v1]
      have s2 : sz (v1 .A) = sz (v .A) := by simp [v1]
      have s3 : sz (v2 .T) = sz (v .T) := by simp [v2, v1]
      have s4 : sz (v2 .ONE) = 1 := by simp [v2, v1, hO, sz]
      have s5 : sz (v3 .X) = sz n := by simp [v3, v2, v1]
      have s6 : sz (v3 .X2) = 0 := by simp [v3, v2, v1, hX2, sz]
      have s7 : sz (v4 .Q) = sz (v .Q) := by simp [v4, v3, v2, v1]
      have s8 : sz (v4 .X2) = sz (n * n) := by simp [v4, v3, v2, v1]
      have s9 : sz (v5 .X) = sz n := by simp [v5, v4, v3, v2, v1]
      have s10 : sz (v6 .X2) = sz (n * n) := by simp [v6, v5, v4, v3, v2, v1]
      have s11 : sz (v .X) = 0 := by simp [hX, sz]
      have s12 : sz (v2 .T) ≤ W := by rw [s3]; exact hvT
      have s13 : sz (v1 .A) ≤ W := by rw [s2]; exact hvA
      rw [s1, s4, s5, s6, s7, s8, s9, s10, s11]
      have hsq : (sz n + sz n + 1) ^ 2 ≤ 4 * (W + 1) ^ 2 := by
        have := Nat.pow_le_pow_left (show sz n + sz n + 1 ≤ 2 * (W + 1) by omega) 2
        rw [mul_pow] at this; norm_num at this; exact this
      have hsq3 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      generalize (W + 1) ^ 2 = P at hsq hsq3
      generalize (sz n + sz n + 1) ^ 2 = P2 at hsq
      omega
    refine (Runs.loopT (by simp [mk, isNum, hb', encNat]) hbody ih').mono ?_
    have hsq2 : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    simp only [List.length_cons]; ring_nf; ring_nf at hsq2; omega

/-! ## Second pass: the processing times (and weights) of the jobs -/

def rowsL (m : Bool) (rest : List ℕ) : List ℕ := rest.flatMap (fun a => if m then [a, a] else [a])

def body2 (m : Bool) : Prog :=
  .seq (rdProg .inp2 .X) (.seq (addProg .X .ZR .X2) (.seq (emitP .X)
    (if m then emitP .X2 else clearProg .X2)))

def loop2 (m : Bool) : Prog := .loop (fun h => (h .inp2).isSome) (body2 m)

lemma runs_loop2 (m : Bool) (W : ℕ) : ∀ (rest : List ℕ) (v : Key → ℕ) (b : Store), Clean b →
    b .inp2 = encNats rest → v .X = 0 → v .X2 = 0 → v .ZR = 0 → (∀ n ∈ rest, sz n ≤ W) →
    Runs (loop2 m) (mk v b) (mk v (Function.update (Function.update b .inp2 []) .R
      ((encNats (rowsL m rest)).reverse ++ b .R))) (rest.length * (50 * W + 100) + 1) := by
  intro rest
  induction rest with
  | nil =>
    intro v b hc hb hX hX2 hZ _
    have e2 : Function.update (Function.update b .inp2 []) .R
        ((encNats (rowsL m [])).reverse ++ b .R) = b := by
      funext k
      by_cases k1 : k = .R
      · subst k1; simp [rowsL, encNats]
      by_cases k2 : k = .inp2
      · subst k2; simp [hb, encNats]
      simp [k1, k2]
    rw [e2]
    exact (Runs.loopF (by simp [mk, isNum, hb, encNats])).mono (by simp)
  | cons n rest ih =>
    intro v b hc hb hX hX2 hZ hall
    have hb' : b .inp2 = encNat n ++ encNats rest := by rw [hb, encNats_cons]
    have hn : sz n ≤ W := hall n (by simp)
    have r1 := mk_rd .inp2 .X rfl (by decide) rfl v b hc n (encNats rest) hb'
    set b3 := Function.update b .inp2 (encNats rest)
    have hc3 : Clean b3 := clean_inp2 hc _
    set v1 := Function.update v .X n
    have r2 := mk_add .X .ZR .X2 rfl rfl rfl v1 b3 hc3
    set v2 := Function.update v1 .X2 (v1 .X + v1 .ZR)
    have hv2X2 : v2 .X2 = n := by simp [v2, v1, hZ]
    have hv2X : v2 .X = n := by simp [v2, v1]
    have r3 := mk_emit .X rfl v2 b3
    set v3 := Function.update v2 .X 0
    set b4 := Function.update b3 .R ((encNat (v2 .X)).reverse ++ b3 .R)
    have hc4 : Clean b4 := clean_R hc3 _
    have hv3X2 : v3 .X2 = n := by simp [v3, hv2X2]
    -- the last step depends on the mode
    set b5 := Function.update b3 .R ((encNats (rowsL m [n])).reverse ++ b .R)
    have r4 : Runs (if m then emitP .X2 else clearProg .X2) (mk v3 b4) (mk v b5) (3 * W + 3) := by
      have hv : Function.update v3 .X2 0 = v := by
        funext k; by_cases k1 : k = .X2
        · subst k1; simp [hX2]
        by_cases k2 : k = .X
        · subst k2; simp [v3, k1, hX]
        simp [v3, v2, v1, k1, k2]
      cases m
      · simp only [Bool.false_eq_true, if_false]
        have := mk_clear .X2 rfl v3 b4
        rw [hv, hv3X2] at this
        have e : b4 = b5 := by simp [b4, b5, b3, hv2X, rowsL, encNats]
        rw [← e]
        refine this.mono ?_
        simp [hv3X2]; omega
      · simp only [if_true]
        have := mk_emit .X2 rfl v3 b4
        rw [hv, hv3X2] at this
        have e : Function.update b4 .R ((encNat n).reverse ++ b4 .R) = b5 := by
          simp [b4, b5, b3, hv2X, rowsL, encNats]
        rw [e] at this
        refine this.mono ?_
        simp [hv3X2]; omega
    have hc5 : Clean b5 := clean_R hc3 _
    have ih' := ih v b5 hc5 (by simp [b5, b3]) hX hX2 hZ (fun k hk => hall k (by simp [hk]))
    have hfin : Function.update (Function.update b5 .inp2 []) .R
        ((encNats (rowsL m rest)).reverse ++ b5 .R) =
        Function.update (Function.update b .inp2 []) .R
        ((encNats (rowsL m (n :: rest))).reverse ++ b .R) := by
      funext k
      by_cases k1 : k = .R
      · subst k1
        have : rowsL m (n :: rest) = rowsL m [n] ++ rowsL m rest := by simp [rowsL]
        simp only [Function.update_self, this, encNats_append, List.reverse_append, b5,
          List.append_assoc]
      by_cases k2 : k = .inp2
      · subst k2; simp [k1]
      simp [k1, k2, b5, b3]
    rw [hfin] at ih'
    have hbody : Runs (body2 m) (mk v b) (mk v b5) (50 * W + 98) := by
      refine (r1.seq (r2.seq (r3.seq r4))).mono ?_
      have s1 : sz (v1 .X) = sz n := by simp [v1]
      have s2 : sz (v1 .ZR) = 0 := by simp [v1, hZ, sz]
      have s3 : sz (v1 .X2) = 0 := by simp [v1, hX2, sz]
      have s4 : sz (v2 .X) = sz n := by rw [hv2X]
      have s5 : sz (v .X) = 0 := by simp [hX, sz]
      rw [s1, s2, s3, s4, s5]
      omega
    refine (Runs.loopT (by simp [mk, isNum, hb', encNat]) hbody ih').mono ?_
    simp only [List.length_cons]; ring_nf; omega

lemma emit_R' (k : Key) (hk : isNum k = true) (v : Key → ℕ) (b : Store) (n : ℕ) (hn : v k = n)
    (W : ℕ) (hW : sz n ≤ W) (L : List ℕ) (hR : b .R = (encNats L).reverse) :
    Runs (emitP k) (mk v b) (mk (Function.update v k 0) (Function.update b .R
      (encNats (L ++ [n])).reverse)) (3 * W + 3) := by
  have := mk_emit k hk v b
  rw [hn, hR] at this
  have e : (encNat n).reverse ++ (encNats L).reverse = (encNats (L ++ [n])).reverse := by
    rw [encNats_append]; simp [encNats]
  rw [e] at this
  exact this.mono (by omega)

/-! ## The thresholds -/

def compOps : List Op :=
  [.mul .A .A .S2, .add .Q .Q .Q2, .add .S2 .Q2 .Y, .half .Y, .half .Y, .add .A .ZR .H, .half .H]

lemma compOps_ok : ∀ o ∈ compOps, o.ok = true := by decide

lemma compOps_length : compOps.length = 7 := rfl

def yOut (m : Bool) (as : List ℕ) : ℕ :=
  if m then (as.sum * as.sum + (sqs as + sqs as)) / 2 / 2 else as.sum / 2

def outKey (m : Bool) : Key := if m then .Y else .H

lemma outKey_num (m : Bool) : isNum (outKey m) = true := by cases m <;> rfl

lemma compOps_eval (m : Bool) (v : Key → ℕ) (as : List ℕ) (hZ : v .ZR = 0)
    (hA : v .A = as.sum) (hQ : v .Q = sqs as) :
    evalL compOps v (outKey m) = yOut m as ∧ evalL compOps v .T = v .T ∧
    evalL compOps v .X = v .X ∧ evalL compOps v .X2 = v .X2 ∧ evalL compOps v .ZR = 0 := by
  cases m <;>
  simp only [compOps, evalL, Op.eval, Function.update_apply, reduceCtorEq, if_false, if_true,
    hZ, hA, hQ, outKey, yOut, Bool.false_eq_true, add_zero] <;> simp

def fullL (m : Bool) (as : List ℕ) : List ℕ := as.length :: (rowsL m as ++ [yOut m as])

def ltBranch (m : Bool) : Prog :=
  .seq (progL compOps) (.seq (emitP .T) (.seq (loop2 m) (.seq (emitP (outKey m))
    (transferProg .R (fun k => decide (k = .out))))))

lemma rowsL_length (m : Bool) (as : List ℕ) : (rowsL m as).length ≤ 2 * as.length := by
  induction as with
  | nil => simp [rowsL]
  | cons a as ih =>
    have : rowsL m (a :: as) = (if m then [a, a] else [a]) ++ rowsL m as := by simp [rowsL]
    rw [this, List.length_append]; cases m <;> simp at * <;> omega

lemma mem_rowsL {m : Bool} {as : List ℕ} {z : ℕ} (h : z ∈ rowsL m as) : z ∈ as := by
  simp only [rowsL, List.mem_flatMap] at h
  obtain ⟨a, ha, hz⟩ := h
  cases m <;> simp at hz <;> (try rcases hz with rfl | rfl) <;> (try subst hz) <;> exact ha

lemma runs_ltBranch (m : Bool) (as : List ℕ) (W : ℕ) (v : Key → ℕ) (base : Store)
    (hc : Clean base) (hZ : v .ZR = 0) (hT : v .T = as.length) (hA : v .A = as.sum)
    (hQ : v .Q = sqs as) (hX : v .X = 0) (hX2 : v .X2 = 0) (hBd : Bd W v)
    (has : ∀ a ∈ as, sz a ≤ W)
    (hi : base .inp2 = encNats as) (hR : base .R = []) (hout : base .out = []) :
    ∃ s, Runs (ltBranch m) (mk v base) s
      (8 * (30 * (3 * (2 ^ 7 * (W + 1)) + 1) ^ 2 + 1) +
        as.length * (50 * (2 ^ 7 * (W + 1)) + 100) +
        3 * ((2 * as.length + 2) * (2 ^ 7 * (W + 1) + 1)) + 6 * (2 ^ 7 * (W + 1)) + 20) ∧
      s .out = encNats (fullL m as) := by
  obtain ⟨W2, hW2⟩ : ∃ W2, W2 = 2 ^ 7 * (W + 1) := ⟨_, rfl⟩
  rw [← hW2]
  have hWW : W ≤ W2 := by
    rw [hW2]; nlinarith
  have r1 := opsL_runs compOps compOps_ok v base hc
  have c1 := costL_le compOps W v hBd
  rw [compOps_length, ← hW2] at c1
  obtain ⟨vC, hvC⟩ : ∃ vC, vC = evalL compOps v := ⟨_, rfl⟩
  rw [← hvC] at r1
  have hBd2 : Bd W2 vC := by rw [hvC, hW2]; exact Bd_evalL compOps W v hBd
  obtain ⟨eY, eT, eX, eX2, eZ⟩ := compOps_eval m v as hZ hA hQ
  rw [← hvC] at eY eT eX eX2 eZ
  rw [hT] at eT
  -- emit t
  have r2 := emit_R' .T rfl vC base as.length eT W2 (by rw [← eT]; exact hBd2 .T) []
    (by simp [hR, encNats])
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = Function.update vC .T 0 := ⟨_, rfl⟩
  rw [← hv1] at r2
  set b1 := Function.update base .R (encNats ([] ++ [as.length])).reverse
  have hc1 : Clean b1 := clean_R hc _
  have r3 := runs_loop2 m W2 as v1 b1 hc1 (by simp [b1, hi]) (by simp [hv1, eX, hX])
    (by simp [hv1, eX2, hX2]) (by simp [hv1, eZ]) (fun a ha => le_trans (has a ha) hWW)
  set b2 := Function.update (Function.update b1 .inp2 []) .R
      ((encNats (rowsL m as)).reverse ++ b1 .R)
  have hR2 : b2 .R = (encNats ([as.length] ++ rowsL m as)).reverse := by
    rw [encNats_append, List.reverse_append]
    simp [b2, b1]
  have hy1 : v1 (outKey m) = yOut m as := by
    have : outKey m ≠ .T := by cases m <;> decide
    simp [hv1, this, eY]
  have r5 := emit_R' (outKey m) (outKey_num m) v1 b2 (yOut m as) hy1 W2
    (by rw [← eY]; exact hBd2 _) _ hR2
  have hLF : [as.length] ++ rowsL m as ++ [yOut m as] = fullL m as := by simp [fullL]
  rw [hLF] at r5
  set v7 := Function.update v1 (outKey m) 0
  set b15 := Function.update b2 .R (encNats (fullL m as)).reverse
  -- final transfer
  have r4 := runs_move .R .out (by decide) (mk v7 b15)
  have hRout : mk v7 b15 .R = (encNats (fullL m as)).reverse := by simp [mk, isNum, b15]
  have hout' : mk v7 b15 .out = [] := by
    simp [mk, isNum, b15, b2, b1, hout]
  have hlen : (encNats (fullL m as)).length ≤ (2 * as.length + 2) * (W2 + 1) := by
    have h1 := len_encNats_le (fullL m as) W2 (by
      intro z hz
      simp only [fullL, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | hz | rfl
      · rw [← eT]; exact hBd2 .T
      · exact le_trans (has z (mem_rowsL hz)) hWW
      · rw [← eY]; exact hBd2 _)
    have h2 : (fullL m as).length ≤ 2 * as.length + 2 := by
      have := rowsL_length m as
      simp [fullL]; omega
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)
  have big := r1.seq (r2.seq (r3.seq (r5.seq r4)))
  refine ⟨_, big.mono ?_, ?_⟩
  · rw [hRout, List.length_reverse]
    omega
  · simp only [Function.update_self, hout', List.append_nil]
    rw [hRout, List.reverse_reverse]

/-! ## The whole machine -/

def phaseB (m : Bool) : Prog :=
  .seq (pushProg .ONE .one) (.seq (copyProg .inp .inp2 .sc) (.seq loop1 (ltBranch m)))

def mainProg (m : Bool) : Prog := .seq phaseA (.branch (fun h => (h .bad).isSome) skipP (phaseB m))

lemma s0_mk (x : List BSym) : s0 x = mk (fun _ => 0) (s0 x) := by
  funext k
  by_cases hk : isNum k = true
  · rw [mk_num hk, encN_zero]
    have : k ≠ .inp := by intro h; subst h; exact absurd hk (by decide)
    simp [s0, this]
  · rw [mk_base (by simpa using hk)]

lemma clean_s0 (x : List BSym) : Clean (s0 x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s0]

def LTb (W L : ℕ) : ℕ :=
  8 * (30 * (3 * (2 ^ 7 * (W + 1)) + 1) ^ 2 + 1) + L * (50 * (2 ^ 7 * (W + 1)) + 100) +
    3 * ((2 * L + 2) * (2 ^ 7 * (W + 1) + 1)) + 6 * (2 ^ 7 * (W + 1)) + 20

def PBb (L : ℕ) : ℕ := 6 * L + 10 + L * (300 * (2 * L + 3) ^ 2) + LTb (2 * L + 2) L

lemma runs_phaseB (m : Bool) (as : List ℕ) :
    ∃ s, Runs (phaseB m) (s0 (encNats as)) s (PBb (encNats as).length) ∧
      s .out = encNats (fullL m as) := by
  set x := encNats as
  set L := x.length
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * L + 2 := ⟨_, rfl⟩
  have hasL : ∀ a ∈ as, sz a ≤ L := fun a ha => sz_le_of_mem ha
  have hsum : sz as.sum ≤ L := sz_le_iff.mpr (sum_lt_pow as)
  have hsq : sz (sqs as) ≤ 2 * L := by
    have := sz_mul_le as.sum as.sum
    have := sz_mono (sqs_le as)
    omega
  have hlen : as.length ≤ L := length_le_encNats as
  set base0 := s0 x
  have hc0 : Clean base0 := clean_s0 x
  have p1 := mk_pushNum .ONE rfl (fun _ => 0) base0 1 (by rw [encN_zero, encN_one])
  set v1 := Function.update (fun _ : Key => (0 : ℕ)) .ONE 1
  have r2 := mk_copyBase .inp .inp2 rfl rfl (by decide) (by decide) (by decide) v1 base0 hc0
  set base2 := Function.update base0 .inp2 (base0 .inp ++ base0 .inp2)
  have hb2 : base2 .inp2 = encNats as := by simp [base2, base0, s0, x]
  have hc2 : Clean base2 := clean_inp2 hc0 _
  have r3 := runs_loop1 W as v1 base2 hc2 (by simp [base2, base0, s0, x]) (by simp [v1])
    (by simp [v1]) (by simp [v1]) (by simp [v1]; omega)
    (by simp [v1]; have := sz_le_self as.length; omega)
    (by simp [v1]; omega) (fun a ha => by have := hasL a ha; omega)
  set vL := Function.update (Function.update (Function.update v1 .A (v1 .A + as.sum)) .T
    (v1 .T + as.length)) .Q (v1 .Q + sqs as)
  set base3 := Function.update base2 .inp []
  have hc3 : Clean base3 := clean_inp hc2 _
  have eA : vL .A = as.sum := by simp [vL, v1]
  have eT : vL .T = as.length := by simp [vL, v1]
  have eQ : vL .Q = sqs as := by simp [vL, v1]
  have eZ : vL .ZR = 0 := by simp [vL, v1]
  have eX : vL .X = 0 := by simp [vL, v1]
  have eX2 : vL .X2 = 0 := by simp [vL, v1]
  have hBd : Bd W vL := by
    intro k
    simp only [vL, v1, Function.update_apply]
    have h1' : sz 1 ≤ 1 := by rw [← length_encN', encN_one]; simp
    have hl' := sz_le_self as.length
    split_ifs <;> simp [sz] at * <;> omega
  obtain ⟨s, r6, hout⟩ := runs_ltBranch m as W vL base3 hc3 eZ eT eA eQ eX eX2 hBd
    (fun a ha => by have := hasL a ha; omega) (by simp [base3, hb2])
    (by simp [base3, base2, base0, s0]) (by simp [base3, base2, base0, s0])
  have full := p1.seq (r2.seq (r3.seq r6))
  rw [← s0_mk x] at full
  refine ⟨s, full.mono ?_, hout⟩
  have e2 : (base0 .inp).length = L := by simp [base0, s0, L]
  rw [e2]
  unfold PBb LTb
  rw [← hW]
  have : as.length * (300 * (W + 1) ^ 2) ≤ L * (300 * (2 * L + 3) ^ 2) := by
    rw [hW]; exact Nat.mul_le_mul_right _ hlen
  have : as.length * (50 * (2 ^ 7 * (W + 1)) + 100) ≤ L * (50 * (2 ^ 7 * (W + 1)) + 100) :=
    Nat.mul_le_mul_right _ hlen
  have : (2 * as.length + 2) * (2 ^ 7 * (W + 1) + 1) ≤ W * (2 ^ 7 * (W + 1) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

open Classical in
noncomputable def F (m : Bool) (x : List BSym) : List BSym :=
  if h : ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ x = encNats l then encNats (fullL m h.choose) else []

lemma F_code (m : Bool) (as : List ℕ) (hpos : ∀ v ∈ as, 0 < v) :
    F m (encNats as) = encNats (fullL m as) := by
  have h : ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ encNats as = encNats l := ⟨as, hpos, rfl⟩
  unfold F
  rw [dif_pos h]
  have : h.choose = as := (encNats_inj h.choose_spec.2).symm
  rw [this]

lemma F_bad (m : Bool) (x : List BSym) (h : ¬ ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ x = encNats l) :
    F m x = [] := by
  unfold F; rw [dif_neg h]

lemma main_runs (m : Bool) (x : List BSym) :
    ∃ s, Runs (mainProg m) (s0 x) s (9 * x.length + 12 + PBb x.length + 2) ∧ s .out = F m x := by
  obtain ⟨sA, rA, hout, hbad, hval⟩ := runs_phaseA x
  by_cases hv : vOK x
  · have hsA := hval hv
    subst hsA
    obtain ⟨l, hl, hx⟩ := (vOK_iff x).1 hv
    obtain ⟨s, rB, hoB⟩ := runs_phaseB m l
    rw [← hx] at rB
    have htest : (s0 x .bad).head?.isSome = false := by
      by_contra h; exact (hbad.1 (by simpa using h)) hv
    refine ⟨s, (rA.seq (Runs.brF (test := fun h => (h .bad).isSome) (p := skipP) htest rB)).mono
      (by omega), ?_⟩
    rw [hoB, hx, F_code m l hl]
  · have htest : (sA .bad).head?.isSome = true := hbad.2 hv
    have : 1 ≤ PBb x.length := by unfold PBb; omega
    refine ⟨sA, (rA.seq (Runs.brT (test := fun h => (h .bad).isSome) (q := phaseB m) htest
      (runs_skip sA))).mono (by omega), ?_⟩
    rw [hout, F_bad]
    intro h; exact hv ((vOK_iff x).2 h)

lemma total_bound (L : ℕ) : 9 * L + 12 + PBb L + 2 ≤ 2 ^ 40 * (L + 1) ^ 3 + 0 := by
  unfold PBb LTb
  ring_nf
  omega

lemma F_poly (m : Bool) : PolyTimeComputable (F m) := by
  obtain ⟨k, hk⟩ := polynomial_absorb (2 ^ 40) 3 0
  refine stack_program_polytime (mainProg m) .inp .out (F m) k ?_
  intro w
  obtain ⟨s, ⟨n, hn, he⟩, hout⟩ := main_runs m w
  exact ⟨s, n, le_trans hn (le_trans (total_bound _) (hk _)), he, hout⟩

end P3R

namespace P3R

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Partition

/-! ## Correctness of the outputs -/

lemma le_div_iff_real (C N d : ℕ) (hd : 0 < d) : C ≤ N / d ↔ (C : ℝ) ≤ (N : ℝ) / d := by
  rw [Nat.le_div_iff_mul_le hd, le_div_iff₀ (by exact_mod_cast hd)]
  norm_cast

lemma totalA_eq (a : List ℕ) : totalA a = a.sum := by
  unfold totalA
  rw [← List.sum_ofFn, List.ofFn_get]

lemma sqs_eq (a : List ℕ) : sqs a = ∑ j : Fin a.length, a.get j * a.get j := by
  unfold sqs
  rw [← List.sum_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get a]
  rw [List.map_ofFn]
  rfl

lemma two_pairSum (a : List ℕ) : 2 * pairSum a = a.sum * a.sum + sqs a := by
  set f : Fin a.length → ℕ := fun j => a.get j
  have hP : pairSum a = ∑ j, ∑ k, if j ≤ k then f j * f k else 0 := rfl
  have hP' : pairSum a = ∑ j, ∑ k, if k ≤ j then f j * f k else 0 := by
    rw [hP, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hpt : ∀ j k : Fin a.length, ((if j ≤ k then f j * f k else 0) +
      (if k ≤ j then f j * f k else 0)) = f j * f k + (if j = k then f j * f k else 0) := by
    intro j k
    rcases lt_trichotomy j k with h | h | h
    · simp [h.le, not_le.mpr h, h.ne]
    · subst h; simp
    · simp [h.le, not_le.mpr h, h.ne']
  have hS : a.sum = ∑ j, f j := by rw [← totalA_eq]; rfl
  calc 2 * pairSum a = pairSum a + pairSum a := by ring
    _ = ∑ j, ∑ k, ((if j ≤ k then f j * f k else 0) + (if k ≤ j then f j * f k else 0)) := by
        rw [show pairSum a + pairSum a = (∑ j, ∑ k, if j ≤ k then f j * f k else 0) +
          (∑ j, ∑ k, if k ≤ j then f j * f k else 0) from congrArg₂ (· + ·) hP hP']
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib]
    _ = ∑ j, ∑ k, (f j * f k + (if j = k then f j * f k else 0)) := by
        simp only [hpt]
    _ = a.sum * a.sum + sqs a := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [hS, Finset.sum_mul_sum, sqs_eq]

lemma yB_eq (a : List ℕ) :
    yB a = ((a.sum * a.sum + (sqs a + sqs a) : ℕ) : ℝ) / 4 := by
  unfold yB
  have h := two_pairSum a
  have h' : (2 : ℝ) * (pairSum a : ℝ) = (a.sum : ℝ) * a.sum + sqs a := by exact_mod_cast h
  rw [totalA_eq]
  have hp : (pairSum a : ℝ) = ((a.sum : ℝ) * a.sum + sqs a) / 2 := by linarith
  rw [hp]
  simp only [Nat.cast_add, Nat.cast_mul]
  ring

lemma yA_eq (a : List ℕ) : yA a = (a.sum : ℝ) / 2 := by
  unfold yA; rw [totalA_eq]

lemma rowsL_false (as : List ℕ) : rowsL false as = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have : rowsL false (a :: as) = a :: rowsL false as := by simp [rowsL]
    rw [this, ih]

lemma rowsL_true (as : List ℕ) :
    rowsL true as = (List.ofFn fun j : Fin as.length => [as.get j, as.get j]).flatten := by
  unfold rowsL
  simp only [if_true]
  conv_lhs => rw [← List.ofFn_get as]
  rw [List.flatMap_def, List.map_ofFn]
  rfl

lemma pairs_inj : ∀ (n : ℕ) (p w : Fin n → ℕ) (l : List ℕ),
    (List.ofFn fun j => [p j, w j]).flatten = l.flatMap (fun a => [a, a]) →
    List.ofFn p = l ∧ List.ofFn w = l := by
  intro n
  induction n with
  | zero =>
    intro p w l h
    rcases l with _ | ⟨a, l⟩
    · simp
    · simp at h
  | succ n ih =>
    intro p w l h
    rcases l with _ | ⟨a, l⟩
    · simp [List.ofFn_succ] at h
    · rw [List.ofFn_succ] at h
      simp only [List.flatten_cons, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨e1, e2⟩ := ih (fun i => p i.succ) (fun i => w i.succ) l h3
      rw [List.ofFn_succ, List.ofFn_succ, h1, h2, e1, e2]
      exact ⟨rfl, rfl⟩

lemma ofFn_procA (a : List ℕ) : List.ofFn (procA a) = a := List.ofFn_get a

lemma ofFn_procB (a : List ℕ) : List.ofFn (procB a) = a := List.ofFn_get a

lemma fullL_false (as : List ℕ) :
    encNats (fullL false as) = cmaxCode as.length (procA as) (as.sum / 2) := by
  simp only [fullL, cmaxCode, rowsL_false, yOut, Bool.false_eq_true, if_false, ofFn_procA,
    List.cons_append]

lemma fullL_true (as : List ℕ) :
    encNats (fullL true as) = sumWCCode as.length (procB as) (procB as)
      ((as.sum * as.sum + (sqs as + sqs as)) / 4) := by
  simp only [fullL, sumWCCode, rowsL_true, yOut, if_true, procB, List.cons_append,
    Nat.div_div_eq_div_mul]

lemma encNats_cons_ne_nil (n : ℕ) (l : List ℕ) : encNats (n :: l) ≠ [] := by
  rw [encNats_cons, encNat_eq]; simp

lemma F_specA (c : List BSym) :
    (∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧
      (∃ σ : Schedule a.length, σ.IsFeasible (procA a) ∧
        ∀ j, (σ.completion (procA a) j : ℝ) ≤ yA a) ∧
      c = encNats a) ↔ F false c ∈ cmaxLang := by
  constructor
  · rintro ⟨a, hpos, ⟨σ, hf, hb⟩, rfl⟩
    rw [F_code false a hpos, fullL_false]
    refine ⟨a.length, procA a, a.sum / 2, ⟨σ, hf, fun j => ?_⟩, rfl⟩
    rw [le_div_iff_real _ _ _ (by norm_num)]
    have := hb j; rw [yA_eq] at this; exact_mod_cast this
  · intro h
    by_cases hd : ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ c = encNats l
    · obtain ⟨l, hl, rfl⟩ := hd
      rw [F_code false l hl] at h
      obtain ⟨n, p, y, ⟨σ, hf, hb⟩, hcode⟩ := h
      have he := encNats_inj hcode
      simp only [fullL, rowsL_false, yOut, Bool.false_eq_true, if_false, List.cons.injEq,
        List.cons_append] at he
      obtain ⟨h1, h2⟩ := he
      subst h1
      obtain ⟨h3, h4⟩ := List.append_inj' h2 rfl
      have hp : p = procA l := by
        apply List.ofFn_injective
        rw [← h3, ofFn_procA]
      subst hp
      have hy : l.sum / 2 = y := by simpa using h4
      subst hy
      refine ⟨l, hl, ⟨σ, hf, fun j => ?_⟩, rfl⟩
      have := hb j
      rw [le_div_iff_real _ _ _ (by norm_num)] at this
      rw [yA_eq]; exact_mod_cast this
    · rw [F_bad false c hd] at h
      obtain ⟨n, p, y, -, hcode⟩ := h
      exact (encNats_cons_ne_nil _ _ hcode.symm).elim

lemma F_specB (c : List BSym) :
    (∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧
      (∃ σ : Schedule a.length, σ.IsFeasible (procB a) ∧
        (σ.sumWC (procB a) (procB a) : ℝ) ≤ yB a) ∧
      c = encNats a) ↔ F true c ∈ sumWCLang := by
  constructor
  · rintro ⟨a, hpos, ⟨σ, hf, hb⟩, rfl⟩
    rw [F_code true a hpos, fullL_true]
    refine ⟨a.length, procB a, procB a, _, ⟨σ, hf, ?_⟩, rfl⟩
    rw [le_div_iff_real _ _ _ (by norm_num)]
    rw [yB_eq] at hb; exact_mod_cast hb
  · intro h
    by_cases hd : ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ c = encNats l
    · obtain ⟨l, hl, rfl⟩ := hd
      rw [F_code true l hl] at h
      obtain ⟨n, p, w, y, ⟨σ, hf, hb⟩, hcode⟩ := h
      have he := encNats_inj hcode
      simp only [fullL, yOut, if_true, List.cons.injEq, List.cons_append] at he
      obtain ⟨h1, h2⟩ := he
      subst h1
      obtain ⟨h3, h4⟩ := List.append_inj' h2 rfl
      have h3' : (List.ofFn fun j => [p j, w j]).flatten = l.flatMap (fun a => [a, a]) := by
        rw [← h3]; simp [rowsL]
      obtain ⟨e1, e2⟩ := pairs_inj _ p w l h3'
      have hp : p = procB l := by
        apply List.ofFn_injective; rw [e1, ofFn_procB]
      have hw : w = procB l := by
        apply List.ofFn_injective; rw [e2, ofFn_procB]
      subst hp hw
      have hy : (l.sum * l.sum + (sqs l + sqs l)) / 2 / 2 = y := by simpa using h4
      subst hy
      refine ⟨l, hl, ⟨σ, hf, ?_⟩, rfl⟩
      rw [Nat.div_div_eq_div_mul, le_div_iff_real _ _ _ (by norm_num)] at hb
      rw [yB_eq]; exact_mod_cast hb
    · rw [F_bad true c hd] at h
      obtain ⟨n, p, w, y, -, hcode⟩ := h
      exact (encNats_cons_ne_nil _ _ hcode.symm).elim

end P3R

open SchedComplexity.Partition
open ProjSchedTW.Complexity (BSym encNats)

theorem solution :
    (∃ fA : List BSym → List BSym, CookPvsNP.PolyTimeComputable fA ∧
      ∀ c : List BSym,
        (∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧
          (∃ σ : Schedule a.length, σ.IsFeasible (procA a) ∧
            ∀ j, (σ.completion (procA a) j : ℝ) ≤ yA a) ∧
          c = encNats a) ↔ fA c ∈ cmaxLang) ∧
    (∃ fB : List BSym → List BSym, CookPvsNP.PolyTimeComputable fB ∧
      ∀ c : List BSym,
        (∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧
          (∃ σ : Schedule a.length, σ.IsFeasible (procB a) ∧
            (σ.sumWC (procB a) (procB a) : ℝ) ≤ yB a) ∧
          c = encNats a) ↔ fB c ∈ sumWCLang) :=
  ⟨⟨P3R.F false, P3R.F_poly false, P3R.F_specA⟩, ⟨P3R.F true, P3R.F_poly true, P3R.F_specB⟩⟩
