-- Prove2me | solution 1 for SchedComplexity.Tardiness.knapsack_wt_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:51:28.150643+00:00
-- url     : https://prove2.me/submissions/4665f33f-a41b-4ba8-9a32-a26e1cc53e9a

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_Tardiness_Knapsack
import Definitions.Def_SchedComplexity_Tardiness_MultLang
import Definitions.Def_SchedComplexity_Tardiness_Construction
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false



namespace K4d

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
  | ONE | Bv | A | T | M | X | T1 | D | Q | M2 | P1 | P2 | TP | TAU | DD | TP1 | Y1 | TAU1
  | Y2 | Y | K | Z
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .inp2, .inpC, .c1, .c2, .tmp, .car, .sc, .mA, .mB, .acc, .lt, .gt, .pend, .last1,
    .bad, .R, .out, .ONE, .Bv, .A, .T, .M, .X, .T1, .D, .Q, .M2, .P1, .P2, .TP, .TAU, .DD, .TP1,
    .Y1, .TAU1, .Y2, .Y, .K, .Z}
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

end K4d



namespace K4d

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

/-! ## Comparison -/

def cstep (a b l : Bool) : Bool := if a == b then l else b

def cmpL : List Bool → List Bool → Bool → Bool
  | [], [], l => l
  | [], b :: y, l => cmpL [] y (cstep false b l)
  | a :: x, [], l => cmpL x [] (cstep a false l)
  | a :: x, b :: y, l => cmpL x y (cstep a b l)

lemma cmpL_spec (x y : List Bool) (l : Bool) :
    cmpL x y l = true ↔ bval x < bval y ∨ (bval x = bval y ∧ l = true) := by
  induction x, y, l using cmpL.induct with
  | case1 l => simp [cmpL, bval]
  | case2 b y l ih =>
    rw [cmpL, ih, bval_cons]; simp only [bval]
    cases b <;> cases l <;> simp [cstep] <;> omega
  | case3 a x l ih =>
    rw [cmpL, ih, bval_cons]; simp only [bval]
    cases a <;> cases l <;> simp [cstep] <;> omega
  | case4 a x b y l ih =>
    rw [cmpL, ih, bval_cons, bval_cons]
    cases a <;> cases b <;> cases l <;> simp [cstep] <;> omega

lemma cmpL_step (x y : List Bool) (l : Bool) (h : ¬ (x = [] ∧ y = [])) :
    cmpL x y l = cmpL x.tail y.tail (cstep (x.headD false) (y.headD false) l) := by
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩
  · simp at h
  all_goals simp [cmpL]

def cmpAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .c1 then .pop else if k = .c2 then .pop
  else if k = .lt then setFlag (h .lt).isSome (cstep (bitOf (h .c1)) (bitOf (h .c2)) (h .lt).isSome)
  else if k = .gt then setFlag (h .gt).isSome (cstep (bitOf (h .c2)) (bitOf (h .c1)) (h .gt).isSome)
  else .keep

def cmpLoop : Prog := .loop (fun h => (h .c1).isSome || (h .c2).isSome) (.act cmpAct)

lemma runs_cmpLoop : ∀ (N : ℕ) (x y : List Bool) (l g : Bool) (s : Store),
    x.length + y.length ≤ N →
    s .c1 = enc x → s .c2 = enc y → s .lt = flag l → s .gt = flag g →
    Runs cmpLoop s (Function.update (Function.update (Function.update (Function.update s .c1 [])
      .c2 []) .lt (flag (cmpL x y l))) .gt (flag (cmpL y x g))) (3 * (x.length + y.length) + 1) := by
  intro N
  induction N with
  | zero =>
    intro x y l g s hN hx hy hl hg
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx0 hy0
    have : Function.update (Function.update (Function.update (Function.update s .c1 [])
      .c2 []) .lt (flag (cmpL [] [] l))) .gt (flag (cmpL [] [] g)) = s := by
      funext k
      simp only [Function.update_apply, cmpL]
      split_ifs <;> subst_vars <;> simp_all [enc]
    rw [this]
    exact Runs.loopF (by simp [hx, hy, enc])
  | succ N ih =>
    intro x y l g s hN hx hy hl hg
    by_cases h0 : x = [] ∧ y = []
    · obtain ⟨rfl, rfl⟩ := h0
      have : Function.update (Function.update (Function.update (Function.update s .c1 [])
        .c2 []) .lt (flag (cmpL [] [] l))) .gt (flag (cmpL [] [] g)) = s := by
        funext k
        simp only [Function.update_apply, cmpL]
        split_ifs <;> subst_vars <;> simp_all [enc]
      rw [this]
      exact Runs.loopF (by simp [hx, hy, enc])
    · have hhx : bitOf (s .c1).head? = x.headD false := by rw [hx]; exact bitOf_enc x
      have hhy : bitOf (s .c2).head? = y.headD false := by rw [hy]; exact bitOf_enc y
      have hls : ((s .lt).head?).isSome = l := by rw [hl]; exact flag_isSome l
      have hgs : ((s .gt).head?).isSome = g := by rw [hg]; exact flag_isSome g
      set a := x.headD false
      set b := y.headD false
      set s1 := StackProg.applyAct cmpAct s with hs1
      have e1 : s1 .c1 = enc x.tail := by
        simp [s1, StackProg.applyAct, cmpAct, StackAct.apply, hx, enc, List.map_tail]
      have e2 : s1 .c2 = enc y.tail := by
        simp [s1, StackProg.applyAct, cmpAct, StackAct.apply, hy, enc, List.map_tail]
      have e3 : s1 .lt = flag (cstep a b l) := by
        simp only [s1, StackProg.applyAct, cmpAct]
        simp only [reduceCtorEq, if_false, if_true, hhx, hhy, hls]
        rw [hl]; exact setFlag_apply l _
      have e4 : s1 .gt = flag (cstep b a g) := by
        simp only [s1, StackProg.applyAct, cmpAct]
        simp only [reduceCtorEq, if_false, if_true, hhx, hhy, hgs]
        rw [hg]; exact setFlag_apply g _
      have e5 : ∀ k, k ≠ .c1 → k ≠ .c2 → k ≠ .lt → k ≠ .gt → s1 k = s k := by
        intro k h1 h2 h3 h4
        simp [s1, StackProg.applyAct, cmpAct, h1, h2, h3, h4, StackAct.apply]
      have hlen : x.tail.length + y.tail.length + 1 ≤ x.length + y.length := by
        rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> simp_all <;> omega
      have ih' := ih x.tail y.tail (cstep a b l) (cstep b a g) s1 (by omega) e1 e2 e3 e4
      have hpost : Function.update (Function.update (Function.update (Function.update s1 .c1 [])
          .c2 []) .lt (flag (cmpL x.tail y.tail (cstep a b l)))) .gt
            (flag (cmpL y.tail x.tail (cstep b a g))) =
          Function.update (Function.update (Function.update (Function.update s .c1 [])
          .c2 []) .lt (flag (cmpL x y l))) .gt (flag (cmpL y x g)) := by
        rw [cmpL_step x y l h0, cmpL_step y x g (by tauto)]
        funext k
        by_cases k1 : k = .gt
        · subst k1; simp only [Function.update_self]; rfl
        by_cases k2 : k = .lt
        · subst k2; simp only [Function.update_self, Function.update_of_ne k1]; rfl
        by_cases k3 : k = .c2
        · subst k3; simp
        by_cases k4 : k = .c1
        · subst k4; simp
        simp [k1, k2, k3, k4, e5 k k4 k3 k2 k1]
      rw [hpost] at ih'
      have htest : ((s .c1).head?.isSome || (s .c2).head?.isSome) = true := by
        rw [hx, hy, isSome_enc, isSome_enc]
        rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> simp_all
      exact (Runs.loopT (test := fun h => (h .c1).isSome || (h .c2).isSome) htest
        (Runs.act cmpAct s) ih').mono (by omega)

def cmpProg (x y : Key) : Prog := .seq (copyProg x .c1 .sc) (.seq (copyProg y .c2 .sc) cmpLoop)

lemma runs_cmp (x y : Key) (hx : AFree x) (hy : AFree y) (hxl : x ≠ .lt) (hyl : y ≠ .lt)
    (hxg : x ≠ .gt) (hyg : y ≠ .gt) (s : Store)
    (h1 : s .c1 = []) (h2 : s .c2 = []) (h5 : s .sc = []) (h6 : s .lt = []) (h7 : s .gt = [])
    (a b : ℕ) (ha : s x = encN a) (hb : s y = encN b) :
    Runs (cmpProg x y) s (Function.update (Function.update s .lt (flag (decide (a < b)))) .gt
      (flag (decide (b < a)))) (9 * (sz a + sz b) + 10) := by
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  have r1 := runs_copy x .c1 .sc hx1 hx5 (by decide) s h5
  set s1 := Function.update s .c1 (s x ++ s .c1) with hs1
  have r2 := runs_copy y .c2 .sc hy2 hy5 (by decide) s1 (by simp [s1, h5])
  set s2 := Function.update s1 .c2 (s1 y ++ s1 .c2) with hs2
  have r3 := runs_cmpLoop _ (Nat.bits a) (Nat.bits b) false false s2 le_rfl
    (by simp [s2, s1, ha, h1, encN]) (by simp [s2, s1, hb, h2, hy1, encN])
    (by simp [s2, s1, h6, flag]) (by simp [s2, s1, h7, flag])
  have c1 : cmpL (Nat.bits a) (Nat.bits b) false = decide (a < b) := by
    have := cmpL_spec (Nat.bits a) (Nat.bits b) false
    rw [bval_bits, bval_bits] at this
    by_cases h : a < b <;> simp_all
  have c2 : cmpL (Nat.bits b) (Nat.bits a) false = decide (b < a) := by
    have := cmpL_spec (Nat.bits b) (Nat.bits a) false
    rw [bval_bits, bval_bits] at this
    by_cases h : b < a <;> simp_all
  rw [c1, c2] at r3
  have hfin : Function.update (Function.update (Function.update (Function.update s2 .c1 [])
      .c2 []) .lt (flag (decide (a < b)))) .gt (flag (decide (b < a))) =
      Function.update (Function.update s .lt (flag (decide (a < b)))) .gt
        (flag (decide (b < a))) := by
    funext k
    by_cases k1 : k = .gt
    · subst k1; simp
    by_cases k2 : k = .lt
    · subst k2; simp
    by_cases k3 : k = .c2
    · subst k3; simp [h2]
    by_cases k4 : k = .c1
    · subst k4; simp [h1]
    simp [k1, k2, k3, k4, s2, s1]
  rw [hfin] at r3
  refine (r1.seq (r2.seq r3)).mono ?_
  have l1 : (s x).length = sz a := by rw [ha, length_encN']
  have l2 : (s1 y).length = sz b := by simp [s1, hy1, hb, length_encN']
  simp only [l1, l2, sz] at *
  omega

def maxProg (m x : Key) : Prog :=
  .seq (cmpProg m x) (.seq (.branch (fun h => (h .lt).isSome) (.seq (clearProg m) (copyProg x m .sc))
    skipP) (.seq (popProg .lt) (popProg .gt)))

lemma runs_max (m x : Key) (hm : AFree m) (hx : AFree x) (hml : m ≠ .lt) (hxl : x ≠ .lt)
    (hmg : m ≠ .gt) (hxg : x ≠ .gt) (hmx : m ≠ x) (s : Store)
    (h1 : s .c1 = []) (h2 : s .c2 = []) (h5 : s .sc = []) (h6 : s .lt = []) (h7 : s .gt = [])
    (a b : ℕ) (ha : s m = encN a) (hb : s x = encN b) :
    Runs (maxProg m x) s (Function.update s m (encN (max a b))) (20 * (sz a + sz b) + 30) := by
  have r1 := runs_cmp m x hm hx hml hxl hmg hxg s h1 h2 h5 h6 h7 a b ha hb
  set s1 := Function.update (Function.update s .lt (flag (decide (a < b)))) .gt
      (flag (decide (b < a)))
  have hb' : Runs (.branch (fun h => (h .lt).isSome) (.seq (clearProg m) (copyProg x m .sc))
      skipP) s1 (Function.update s1 m (encN (max a b))) (9 * (sz a + sz b) + 10) := by
    by_cases hab : a < b
    · have q1 := runs_clear m s1
      have q2 := runs_copy x m .sc (Ne.symm hmx) hx.2.2.2.2 hm.2.2.2.2 (Function.update s1 m [])
        (by simp [s1, Ne.symm hm.2.2.2.2, h5])
      have e : Function.update (Function.update s1 m []) m
          (Function.update s1 m [] x ++ Function.update s1 m [] m) =
          Function.update s1 m (encN (max a b)) := by
        simp [Function.update_of_ne (Ne.symm hmx), s1, hxg, hxl, hb, max_eq_right hab.le]
      rw [e] at q2
      refine (Runs.brT (by simp [s1, hab, flag]) (q1.seq q2)).mono ?_
      have l1 : (s1 m).length = sz a := by simp [s1, hmg, hml, ha, length_encN']
      have l2 : (Function.update s1 m [] x).length = sz b := by
        simp [Function.update_of_ne (Ne.symm hmx), s1, hxg, hxl, hb, length_encN']
      rw [l1, l2]; omega
    · have e : Function.update s1 m (encN (max a b)) = s1 := by
        rw [max_eq_left (not_lt.mp hab)]; simp [s1, hmg, hml, ha]
      rw [e]
      exact (Runs.brF (by simp [s1, hab, flag]) (runs_skip s1)).mono (by omega)
  set s2 := Function.update s1 m (encN (max a b))
  have r3 := runs_pop .lt s2
  have r4 := runs_pop .gt (Function.update s2 .lt (s2 .lt).tail)
  have hfin : Function.update (Function.update s2 .lt (s2 .lt).tail) .gt
      ((Function.update s2 .lt (s2 .lt).tail) .gt).tail = Function.update s m (encN (max a b)) := by
    funext k
    by_cases k1 : k = .gt
    · subst k1; by_cases hba : b < a <;> simp [s2, s1, Ne.symm hmg, h7, hba, flag]
    by_cases k2 : k = .lt
    · subst k2; by_cases hba : a < b <;> simp [s2, s1, Ne.symm hml, h6, hba, flag]
    by_cases k3 : k = m
    · subst k3; rw [Function.update_of_ne k1, Function.update_of_ne k2]; simp [s2]
    simp [k1, k2, k3, s2, s1]
  rw [hfin] at r4
  exact (r1.seq (hb'.seq (r3.seq r4))).mono (by omega)

/-! ## Subtraction (truncated) -/

def bor (x y c : Bool) : Bool := if x then (y && c) else (y || c)

def subB : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | x :: xs, [], c => (x ^^ c) :: subB xs [] (bor x false c)
  | [], y :: ys, c => (y ^^ c) :: subB [] ys (bor false y c)
  | x :: xs, y :: ys, c => (x ^^ y ^^ c) :: subB xs ys (bor x y c)

def subBor : List Bool → List Bool → Bool → Bool
  | [], [], c => c
  | x :: xs, [], c => subBor xs [] (bor x false c)
  | [], y :: ys, c => subBor [] ys (bor false y c)
  | x :: xs, y :: ys, c => subBor xs ys (bor x y c)

lemma bval_subB (x y : List Bool) (c : Bool) (h : bval y + c.toNat ≤ bval x) :
    bval (subB x y c) = bval x - bval y - c.toNat := by
  induction x, y, c using subB.induct with
  | case1 c => simp [subB, bval]
  | case2 x xs c ih =>
    simp only [subB, bval_cons] at h ⊢
    simp only [bval] at h ⊢
    have h' : bval [] + (bor x false c).toNat ≤ bval xs := by
      simp only [bval]; cases x <;> cases c <;> simp [bor] at h ⊢ <;> omega
    rw [ih h']; cases x <;> cases c <;> simp [bor, bval] at h ⊢ <;> omega
  | case3 y ys c ih =>
    simp only [subB, bval_cons] at h ⊢
    simp only [bval] at h ⊢
    have h' : bval ys + (bor false y c).toNat ≤ bval [] := by
      simp only [bval]; cases y <;> cases c <;> simp [bor] at h ⊢ <;> omega
    rw [ih h']; cases y <;> cases c <;> simp [bor, bval] at h ⊢ <;> omega
  | case4 x xs y ys c ih =>
    simp only [subB, bval_cons] at h ⊢
    have h' : bval ys + (bor x y c).toNat ≤ bval xs := by
      cases x <;> cases y <;> cases c <;> simp [bor] at h ⊢ <;> omega
    rw [ih h']; cases x <;> cases y <;> cases c <;> simp [bor] at h ⊢ <;> omega

lemma subB_step (x y : List Bool) (c : Bool) (h : ¬ (x = [] ∧ y = [])) :
    subB x y c = (x.headD false ^^ y.headD false ^^ c) ::
      subB x.tail y.tail (bor (x.headD false) (y.headD false) c) := by
  match x, y with
  | [], [] => simp at h
  | x :: xs, [] => simp [subB]
  | [], y :: ys => simp [subB]
  | x :: xs, y :: ys => simp [subB]

lemma subBor_step (x y : List Bool) (c : Bool) (h : ¬ (x = [] ∧ y = [])) :
    subBor x y c = subBor x.tail y.tail (bor (x.headD false) (y.headD false) c) := by
  match x, y with
  | [], [] => simp at h
  | x :: xs, [] => simp [subBor]
  | [], y :: ys => simp [subBor]
  | x :: xs, y :: ys => simp [subBor]

lemma length_subB (x y : List Bool) (c : Bool) :
    (subB x y c).length ≤ x.length + y.length := by
  induction x, y, c using subB.induct with
  | case1 c => simp [subB]
  | case2 x xs c ih => simp only [subB, List.length_cons] at ih ⊢; omega
  | case3 y ys c ih => simp only [subB, List.length_cons] at ih ⊢; omega
  | case4 x xs y ys c ih => simp only [subB, List.length_cons] at ih ⊢; omega

lemma canon_iff (d : List Bool) : Canon d ↔ d = [] ∨ d.getLast? = some true := by
  induction d with
  | nil => simp [Canon]
  | cons b d ih =>
    simp only [Canon, ih]
    rcases d with _ | ⟨c, d⟩
    · simp
    · simp [List.getLast?_cons_cons]

/-- strip the most significant zero bits. -/
def trimB (r : List Bool) : List Bool := (r.reverse.dropWhile (fun b => !b)).reverse

lemma bval_append (l m : List Bool) : bval (l ++ m) = bval l + 2 ^ l.length * bval m := by
  induction l with
  | nil => simp [bval]
  | cons b l ih => rw [List.cons_append, bval_cons, bval_cons, ih]; simp [pow_succ]; ring

lemma bval_allFalse (l : List Bool) (h : ∀ b ∈ l, b = false) : bval l = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [bval_cons, ih (fun c hc => h c (by simp [hc])), h b (by simp)]; rfl

lemma bval_trimB (r : List Bool) : bval (trimB r) = bval r := by
  have h0 := List.takeWhile_append_dropWhile (p := fun b => !b) (l := r.reverse)
  have e : r = trimB r ++ (r.reverse.takeWhile (fun b => !b)).reverse := by
    unfold trimB
    calc r = r.reverse.reverse := by simp
      _ = (r.reverse.takeWhile (fun b => !b) ++ r.reverse.dropWhile (fun b => !b)).reverse := by
          rw [h0]
      _ = _ := by rw [List.reverse_append]
  conv_rhs => rw [e]
  rw [bval_append, bval_allFalse ((r.reverse.takeWhile (fun b => !b)).reverse) (by
    intro b hb
    have := List.mem_takeWhile_imp (List.mem_reverse.mp hb)
    simpa using this)]
  simp

lemma head_dropWhile_not (l : List Bool) :
    (l.dropWhile (fun b => !b)) = [] ∨ (l.dropWhile (fun b => !b)).head? = some true := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b
    · rw [List.dropWhile_cons_of_pos (by simp)]; exact ih
    · rw [List.dropWhile_cons_of_neg (by simp)]; simp

lemma canon_trimB (r : List Bool) : Canon (trimB r) := by
  rw [canon_iff]
  unfold trimB
  rcases head_dropWhile_not r.reverse with h | h
  · left; rw [h]; rfl
  · right; rw [List.getLast?_reverse]; exact h

lemma bits_sub (a b : ℕ) (h : b ≤ a) :
    Nat.bits (a - b) = trimB (subB (Nat.bits a) (Nat.bits b) false) := by
  rw [← bits_bval (canon_trimB _), bval_trimB, bval_subB _ _ _ (by simp [bval_bits]; omega)]
  simp [bval_bits]

lemma dw_enc (l : List Bool) :
    (enc l).dropWhile (fun a => decide (a = BSym.zero)) = enc (l.dropWhile (fun b => !b)) := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [enc, toB] at ih ⊢ <;> exact ih

lemma enc_reverse (l : List Bool) : (enc l).reverse = enc l.reverse := by simp [enc]

lemma dw_trim (r : List Bool) :
    (enc r).reverse.dropWhile (fun a => decide (a = BSym.zero)) = (enc (trimB r)).reverse := by
  rw [enc_reverse, dw_enc, enc_reverse, trimB, List.reverse_reverse]

def subAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .c1 then .pop else if k = .c2 then .pop
  else if k = .tmp then .push (toB (bitOf (h .c1) ^^ bitOf (h .c2) ^^ (h .car).isSome))
  else if k = .car then setFlag (h .car).isSome (bor (bitOf (h .c1)) (bitOf (h .c2)) (h .car).isSome)
  else .keep

def subLoop : Prog := .loop (fun h => (h .c1).isSome || (h .c2).isSome) (.act subAct)

def subPost (x y : List Bool) (c : Bool) (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s .c1 []) .c2 []) .car
    (flag (subBor x y c))) .tmp ((enc (subB x y c)).reverse ++ s .tmp)

lemma runs_subLoop : ∀ (N : ℕ) (x y : List Bool) (c : Bool) (s : Store),
    x.length + y.length ≤ N →
    s .c1 = enc x → s .c2 = enc y → s .car = flag c →
    Runs subLoop s (subPost x y c s) (3 * (x.length + y.length) + 1) := by
  intro N
  induction N with
  | zero =>
    intro x y c s hN hx hy hc
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx0 hy0
    have hpost : subPost [] [] c s = s := by
      funext k
      simp only [subPost, subB, subBor, enc, List.map_nil, List.reverse_nil, List.nil_append,
        Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [flag, enc]
    rw [hpost]
    exact (Runs.loopF (by simp [hx, hy, enc])).mono (by simp)
  | succ N ih =>
    intro x y c s hN hx hy hc
    by_cases h0 : x = [] ∧ y = []
    · obtain ⟨rfl, rfl⟩ := h0
      have hpost : subPost [] [] c s = s := by
        funext k
        simp only [subPost, subB, subBor, enc, List.map_nil, List.reverse_nil, List.nil_append,
          Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [flag, enc]
      rw [hpost]
      exact (Runs.loopF (by simp [hx, hy, enc])).mono (by simp)
    · have hstep := subB_step x y c h0
      have hstepB := subBor_step x y c h0
      have hhx : bitOf (s .c1).head? = x.headD false := by rw [hx]; exact bitOf_enc x
      have hhy : bitOf (s .c2).head? = y.headD false := by rw [hy]; exact bitOf_enc y
      have hcs : ((s .car).head?).isSome = c := by rw [hc]; exact flag_isSome c
      set a := x.headD false
      set b := y.headD false
      set s1 := StackProg.applyAct subAct s with hs1
      have e1 : s1 .c1 = enc x.tail := by
        simp [s1, StackProg.applyAct, subAct, StackAct.apply, hx, enc, List.map_tail]
      have e2 : s1 .c2 = enc y.tail := by
        simp [s1, StackProg.applyAct, subAct, StackAct.apply, hy, enc, List.map_tail]
      have e3 : s1 .tmp = toB (a ^^ b ^^ c) :: s .tmp := by
        simp only [s1, StackProg.applyAct, subAct]
        simp [hhx, hhy, hcs, StackAct.apply]
      have e4 : s1 .car = flag (bor a b c) := by
        simp only [s1, StackProg.applyAct, subAct]
        simp only [reduceCtorEq, if_false, if_true, hhx, hhy, hcs]
        rw [hc]; exact setFlag_apply c _
      have e5 : ∀ k, k ≠ .c1 → k ≠ .c2 → k ≠ .tmp → k ≠ .car → s1 k = s k := by
        intro k h1 h2 h3 h4
        simp [s1, StackProg.applyAct, subAct, h1, h2, h3, h4, StackAct.apply]
      have hlen : x.tail.length + y.tail.length + 1 ≤ x.length + y.length := by
        rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> simp_all <;> omega
      have ih' := ih x.tail y.tail (bor a b c) s1 (by omega) e1 e2 e4
      have hpost : subPost x.tail y.tail (bor a b c) s1 = subPost x y c s := by
        funext k
        simp only [subPost, Function.update_apply]
        by_cases k1 : k = .tmp
        · subst k1; simp only [if_true, e3, hstep]; simp [enc]
        by_cases k2 : k = .car
        · simp [k2, hstepB]
        by_cases k3 : k = .c2
        · simp [k3]
        by_cases k4 : k = .c1
        · simp [k4]
        simp [k1, k2, k3, k4, e5 k k4 k3 k1 k2]
      rw [hpost] at ih'
      have htest : ((s .c1).head?.isSome || (s .c2).head?.isSome) = true := by
        rw [hx, hy, isSome_enc, isSome_enc]
        rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> simp_all
      exact (Runs.loopT (test := fun h => (h .c1).isSome || (h .c2).isSome) htest
        (Runs.act subAct s) ih').mono (by omega)

def dzLoop : Prog := .loop (fun h => decide (h .tmp = some BSym.zero)) (popProg .tmp)

lemma runs_dz : ∀ (l : List BSym) (s : Store), s .tmp = l →
    Runs dzLoop s (Function.update s .tmp (l.dropWhile (fun a => decide (a = BSym.zero))))
      (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro s h
    have : Function.update s .tmp (([] : List BSym).dropWhile (fun a => decide (a = BSym.zero)))
        = s := by rw [Function.update_eq_self_iff]; simp [h]
    rw [this]
    exact Runs.loopF (by simp [h])
  | cons a l ih =>
    intro s h
    by_cases ha : a = BSym.zero
    · subst ha
      have r1 := runs_pop .tmp s
      have ih' := ih (Function.update s .tmp (s .tmp).tail) (by simp [h])
      rw [Function.update_idem] at ih'
      have e : (BSym.zero :: l).dropWhile (fun a => decide (a = BSym.zero)) =
          l.dropWhile (fun a => decide (a = BSym.zero)) := by simp
      rw [e]
      exact (Runs.loopT (test := fun h => decide (h .tmp = some BSym.zero)) (by simp [h]) r1
        ih').mono (by simp; omega)
    · have e : (a :: l).dropWhile (fun a => decide (a = BSym.zero)) = a :: l := by simp [ha]
      have : Function.update s .tmp (a :: l) = s := by rw [Function.update_eq_self_iff, h]
      rw [e, this]
      exact (Runs.loopF (by simp [h, ha])).mono (by omega)

def subCore (x y z : Key) : Prog :=
  .seq (copyProg x .c1 .sc) (.seq (copyProg y .c2 .sc) (.seq subLoop (.seq (clearProg .car)
    (.seq dzLoop (.seq (clearProg z) (transferProg .tmp (fun k => decide (k = z))))))))

lemma runs_subCore (x y z : Key) (hx : AFree x) (hy : AFree y) (hz : AFree z) (s : Store)
    (h1 : s .c1 = []) (h2 : s .c2 = []) (h3 : s .tmp = []) (h4 : s .car = []) (h5 : s .sc = [])
    (a b : ℕ) (ha : s x = encN a) (hb : s y = encN b) (hab : b ≤ a) :
    Runs (subCore x y z) s (Function.update s z (encN (a - b)))
      (30 * (sz a + sz b) + 3 * (s z).length + 30) := by
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
  have r1 := runs_copy x .c1 .sc hx1 hx5 (by decide) s h5
  set s1 := Function.update s .c1 (s x ++ s .c1) with hs1
  have r2 := runs_copy y .c2 .sc hy2 hy5 (by decide) s1 (by simp [s1, h5])
  set s2 := Function.update s1 .c2 (s1 y ++ s1 .c2) with hs2
  have r3 := runs_subLoop _ (Nat.bits a) (Nat.bits b) false s2 le_rfl
    (by simp [s2, s1, ha, h1, encN]) (by simp [s2, s1, hb, h2, hy1, encN])
    (by simp [s2, s1, h4, flag])
  set r := subB (Nat.bits a) (Nat.bits b) false with hr
  set s3 := subPost (Nat.bits a) (Nat.bits b) false s2 with hs3
  have r4 := runs_clear .car s3
  set s4 := Function.update s3 .car [] with hs4
  have e4tmp : s4 .tmp = (enc r).reverse := by
    simp [s4, s3, subPost, s2, s1, h3, r]
  have r5 := runs_dz (s4 .tmp) s4 rfl
  rw [e4tmp, dw_trim, ← bits_sub a b hab] at r5
  set s5 := Function.update s4 .tmp (encN (a - b)).reverse with hs5
  have r6 := runs_clear z s5
  set s6 := Function.update s5 z [] with hs6
  have r7 := runs_move .tmp z (Ne.symm hz3) s6
  have e6tmp : s6 .tmp = (encN (a - b)).reverse := by simp [s6, s5, Ne.symm hz3]
  have hfin : Function.update (Function.update s6 .tmp []) z ((s6 .tmp).reverse ++ s6 z) =
      Function.update s z (encN (a - b)) := by
    rw [e6tmp]
    funext k
    by_cases k1 : k = z
    · subst k1; simp [s6]
    by_cases k2 : k = .tmp
    · subst k2; simp [k1, h3]
    simp only [Function.update_apply, k1, k2, if_false, s6, s5, s4, s3, subPost, s2, s1]
    by_cases k3 : k = .car
    · subst k3; simp [h4]
    by_cases k4 : k = .c2
    · subst k4; simp [h2]
    by_cases k5 : k = .c1
    · subst k5; simp [h1]
    simp [k3, k4, k5]
  rw [hfin] at r7
  refine (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_
  have l1 : (s x).length = sz a := by rw [ha, length_encN']
  have l2 : (s1 y).length = sz b := by simp [s1, hy1, hb, length_encN']
  have l3 : (s3 .car).length ≤ 1 := by
    simp only [s3, subPost, Function.update_apply]; simp [flag]; split <;> simp
  have l4 : (enc r).reverse.length ≤ sz a + sz b := by
    simp only [List.length_reverse, enc, List.length_map, r]
    exact length_subB _ _ _
  have l5 : (s5 z).length = (s z).length := by
    simp [s5, s4, s3, subPost, hz3, hz4, hz2, hz1, s2, s1]
  have l6 : (s6 .tmp).length = sz (a - b) := by rw [e6tmp]; simp [length_encN']
  have l7 : sz (a - b) ≤ sz a := sz_mono (Nat.sub_le a b)
  simp only [l1, l2, l5, l6, sz] at *
  omega

def subProg (x y z : Key) : Prog :=
  .seq (cmpProg x y) (.seq (.branch (fun h => (h .lt).isSome) (clearProg z) (subCore x y z))
    (.seq (popProg .lt) (popProg .gt)))

lemma runs_sub (x y z : Key) (hx : AFree x) (hy : AFree y) (hz : AFree z)
    (hxl : x ≠ .lt) (hyl : y ≠ .lt) (hxg : x ≠ .gt) (hyg : y ≠ .gt) (hzl : z ≠ .lt) (hzg : z ≠ .gt)
    (s : Store)
    (h1 : s .c1 = []) (h2 : s .c2 = []) (h3 : s .tmp = []) (h4 : s .car = []) (h5 : s .sc = [])
    (h6 : s .lt = []) (h7 : s .gt = [])
    (a b : ℕ) (ha : s x = encN a) (hb : s y = encN b) :
    Runs (subProg x y z) s (Function.update s z (encN (a - b)))
      (40 * (sz a + sz b) + 3 * (s z).length + 50) := by
  have r1 := runs_cmp x y hx hy hxl hyl hxg hyg s h1 h2 h5 h6 h7 a b ha hb
  set s1 := Function.update (Function.update s .lt (flag (decide (a < b)))) .gt
      (flag (decide (b < a)))
  have hz1 : s1 z = s z := by simp [s1, hzl, hzg]
  have hb' : Runs (.branch (fun h => (h .lt).isSome) (clearProg z) (subCore x y z)) s1
      (Function.update s1 z (encN (a - b))) (30 * (sz a + sz b) + 3 * (s z).length + 31) := by
    by_cases hab : a < b
    · have q1 := runs_clear z s1
      rw [show (a - b) = 0 by omega, encN_zero]
      refine (Runs.brT (by simp [s1, hab, flag]) q1).mono ?_
      rw [hz1]; omega
    · have q := runs_subCore x y z hx hy hz s1 (by simp [s1, h1]) (by simp [s1, h2])
        (by simp [s1, h3]) (by simp [s1, h4]) (by simp [s1, h5]) a b
        (by simp [s1, hxl, hxg, ha]) (by simp [s1, hyl, hyg, hb]) (by omega)
      rw [hz1] at q
      exact (Runs.brF (by simp [s1, hab, flag]) q).mono (by omega)
  set s2 := Function.update s1 z (encN (a - b))
  have r3 := runs_pop .lt s2
  have r4 := runs_pop .gt (Function.update s2 .lt (s2 .lt).tail)
  have hfin : Function.update (Function.update s2 .lt (s2 .lt).tail) .gt
      ((Function.update s2 .lt (s2 .lt).tail) .gt).tail = Function.update s z (encN (a - b)) := by
    funext k
    by_cases k1 : k = .gt
    · subst k1; by_cases hba : b < a <;> simp [s2, s1, Ne.symm hzg, h7, hba, flag]
    by_cases k2 : k = .lt
    · subst k2; by_cases hba : a < b <;> simp [s2, s1, Ne.symm hzl, h6, hba, flag]
    by_cases k3 : k = z
    · subst k3; rw [Function.update_of_ne k1, Function.update_of_ne k2]; simp [s2]
    simp [k1, k2, k3, s2, s1]
  rw [hfin] at r4
  exact (r1.seq (hb'.seq (r3.seq r4))).mono (by omega)

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

end K4d



namespace K4d

open CookPvsNP ProjSchedTW.Complexity

def isNum : Key → Bool
  | .ONE | .Bv | .A | .T | .M | .X | .T1 | .D | .Q | .M2 | .P1 | .P2 | .TP | .TAU | .DD | .TP1
  | .Y1 | .TAU1 | .Y2 | .Y | .K | .Z => true
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

lemma mk_sub (x y z : Key) (hx : isNum x = true) (hy : isNum y = true) (hz : isNum z = true)
    (v : Key → ℕ) (b : Store) (hc : Clean b) :
    Runs (subProg x y z) (mk v b) (mk (Function.update v z (v x - v y)) b)
      (40 * (sz (v x) + sz (v y)) + 3 * sz (v z) + 50) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, h9, h10⟩ := mk_scratch (v := v) hc
  have := runs_sub x y z (num_free hx).1.1 (num_free hy).1.1 (num_free hz).1.1
    (num_free hx).2.1 (num_free hy).2.1 (num_free hx).2.2 (num_free hy).2.2
    (num_free hz).2.1 (num_free hz).2.2 (mk v b)
    h1 h2 h3 h4 h5 h9 h10 (v x) (v y) (mk_num hx) (mk_num hy)
  rw [mk_upd_num hz, mk_num hz, length_encN'] at this
  exact this

lemma mk_half (z : Key) (hz : isNum z = true) (v : Key → ℕ) (b : Store) :
    Runs (popProg z) (mk v b) (mk (Function.update v z (v z / 2)) b) 1 := by
  have := runs_pop z (mk v b)
  have e : (mk v b z).tail = encN (v z / 2) := by
    rw [mk_num hz]; simp [encN, enc, bits_div_two, List.map_tail]
  rw [e, mk_upd_num hz] at this
  exact this

lemma mk_max (m x : Key) (hm : isNum m = true) (hx : isNum x = true) (hmx : m ≠ x)
    (v : Key → ℕ) (b : Store) (hc : Clean b) :
    Runs (maxProg m x) (mk v b) (mk (Function.update v m (max (v m) (v x))) b)
      (20 * (sz (v m) + sz (v x)) + 30) := by
  obtain ⟨h1, h2, -, -, h5, -, -, -, h9, h10⟩ := mk_scratch (v := v) hc
  have := runs_max m x (num_free hm).1.1 (num_free hx).1.1 (num_free hm).2.1 (num_free hx).2.1
    (num_free hm).2.2 (num_free hx).2.2 hmx (mk v b) h1 h2 h5 h9 h10 (v m) (v x)
    (mk_num hm) (mk_num hx)
  rw [mk_upd_num hm] at this
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
  | sub (x y z : Key)
  | half (z : Key)

def Op.prog : Op → Prog
  | .add x y z => addProg x y z
  | .mul x y z => mulProg x y z
  | .sub x y z => subProg x y z
  | .half z => popProg z

def Op.eval : Op → (Key → ℕ) → (Key → ℕ)
  | .add x y z, v => Function.update v z (v x + v y)
  | .mul x y z, v => Function.update v z (v x * v y)
  | .sub x y z, v => Function.update v z (v x - v y)
  | .half z, v => Function.update v z (v z / 2)

def Op.ok : Op → Bool
  | .add x y z => isNum x && isNum y && isNum z
  | .mul x y z => isNum x && isNum y && isNum z
  | .sub x y z => isNum x && isNum y && isNum z
  | .half z => isNum z

def Op.cost : Op → (Key → ℕ) → ℕ
  | .add x y z, v => 30 * (sz (v x) + sz (v y) + sz (v z) + 1) ^ 2
  | .mul x y z, v => 30 * (sz (v x) + sz (v y) + sz (v z) + 1) ^ 2
  | .sub x y z, v => 60 * (sz (v x) + sz (v y) + sz (v z) + 1) ^ 2
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
  | sub x y z =>
    simp only [Op.ok, Bool.and_eq_true] at ho
    refine (mk_sub x y z ho.1.1 ho.1.2 ho.2 v b hc).mono ?_
    simp only [Op.cost]
    nlinarith
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
  | sub x y z =>
    simp only [Op.eval, Function.update_apply]
    split_ifs
    · have := sz_mono (Nat.sub_le (v x) (v y)); have := h x; omega
    · have := h k; omega
  | half z =>
    simp only [Op.eval, Function.update_apply]
    split_ifs
    · have := sz_div2 (v z); have := h z; omega
    · have := h k; omega

lemma Bd.cost {W : ℕ} {v : Key → ℕ} (h : Bd W v) (o : Op) : o.cost v ≤ 60 * (3 * W + 1) ^ 2 := by
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
  | sub x y z =>
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
    costL os v ≤ (os.length + 1) * (60 * (3 * (2 ^ os.length * (W + 1)) + 1) ^ 2 + 1) := by
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

end K4d



namespace K4d

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

/-! ## First pass over the items: `A`, `t`, `a_*` -/

def body1 : Prog :=
  .seq (rdProg .inp .X) (.seq (addProg .A .X .A) (.seq (addProg .T .ONE .T)
    (.seq (maxProg .M .X) (clearProg .X))))

def loop1 : Prog := .loop (fun h => (h .inp).isSome) body1

lemma runs_loop1 (W : ℕ) : ∀ (rest : List ℕ) (v : Key → ℕ) (b : Store), Clean b →
    b .inp = encNats rest → v .X = 0 → v .ONE = 1 →
    sz (v .A + rest.sum) ≤ W → sz (v .T + rest.length) ≤ W → sz (v .M) ≤ W →
    (∀ n ∈ rest, sz n ≤ W) →
    Runs loop1 (mk v b) (mk (Function.update (Function.update (Function.update v .A
      (v .A + rest.sum)) .T (v .T + rest.length)) .M (rest.foldl max (v .M)))
      (Function.update b .inp [])) (rest.length * (100 * W + 100) + 1) := by
  intro rest
  induction rest with
  | nil =>
    intro v b hc hb hX hO _ _ _ _
    have e1 : Function.update (Function.update (Function.update v .A
      (v .A + ([] : List ℕ).sum)) .T (v .T + ([] : List ℕ).length)) .M
        (([] : List ℕ).foldl max (v .M)) = v := by
      simp
    have e2 : Function.update b .inp [] = b := by
      rw [Function.update_eq_self_iff]; simpa [encNats] using hb
    rw [e1, e2]
    exact (Runs.loopF (by simp [mk, isNum, hb, encNats])).mono (by simp)
  | cons n rest ih =>
    intro v b hc hb hX hO hA hT hM hall
    have hb' : b .inp = encNat n ++ encNats rest := by rw [hb, encNats_cons]
    have hn : sz n ≤ W := hall n (by simp)
    have hvA : sz (v .A) ≤ W := le_trans (sz_mono (by simp)) hA
    have hvT : sz (v .T) ≤ W := le_trans (sz_mono (by simp)) hT
    have r1 := mk_rd .inp .X rfl (by decide) rfl v b hc n (encNats rest) hb'
    set b1 := Function.update b .inp (encNats rest)
    have hc1 : Clean b1 := clean_inp hc _
    set v1 := Function.update v .X n
    have r2 := mk_add .A .X .A rfl rfl rfl v1 b1 hc1
    set v2 := Function.update v1 .A (v1 .A + v1 .X)
    have r3 := mk_add .T .ONE .T rfl rfl rfl v2 b1 hc1
    set v3 := Function.update v2 .T (v2 .T + v2 .ONE)
    have r4 := mk_max .M .X rfl rfl (by decide) v3 b1 hc1
    set v4 := Function.update v3 .M (max (v3 .M) (v3 .X))
    have r5 := mk_clear .X rfl v4 b1
    set v5 := Function.update v4 .X 0
    have q1 : v5 .A = v .A + n := by simp [v5, v4, v3, v2, v1]
    have q2 : v5 .T = v .T + 1 := by simp [v5, v4, v3, v2, v1, hO]
    have q3 : v5 .M = max (v .M) n := by simp [v5, v4, v3, v2, v1]
    have ih' := ih v5 b1 hc1 (by simp [b1]) (by simp [v5]) (by simp [v5, v4, v3, v2, v1, hO])
      (by rw [q1]; refine le_trans (le_of_eq ?_) hA; congr 1; simp; ring)
      (by rw [q2]; refine le_trans (le_of_eq ?_) hT; congr 1; simp; ring)
      (by rw [q3]; rcases le_total (v .M) n with h | h
          · rw [max_eq_right h]; exact hn
          · rw [max_eq_left h]; exact hM)
      (fun m hm => hall m (by simp [hm]))
    have hfin : mk (Function.update (Function.update (Function.update v5 .A (v5 .A + rest.sum))
        .T (v5 .T + rest.length)) .M (rest.foldl max (v5 .M))) (Function.update b1 .inp []) =
        mk (Function.update (Function.update (Function.update v .A (v .A + (n :: rest).sum))
        .T (v .T + (n :: rest).length)) .M ((n :: rest).foldl max (v .M)))
        (Function.update b .inp []) := by
      rw [q1, q2, q3]
      have : Function.update b1 .inp [] = Function.update b .inp [] := by simp [b1]
      rw [this]
      congr 1
      funext k
      simp only [Function.update_apply, List.sum_cons, List.length_cons, List.foldl_cons]
      by_cases k1 : k = .M
      · simp [k1]
      by_cases k2 : k = .T
      · simp [k2]; ring
      by_cases k3 : k = .A
      · simp [k3]; ring
      by_cases k4 : k = .X
      · subst k4; simp [v5, hX]
      simp [k1, k2, k3, k4, v5, v4, v3, v2, v1]
    rw [hfin] at ih'
    have hbody : Runs body1 (mk v b) (mk v5 b1) (100 * W + 98) := by
      refine (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_
      have s1 : sz (v1 .X) = sz n := by simp [v1]
      have s2 : sz (v1 .A) = sz (v .A) := by simp [v1]
      have s3 : sz (v2 .T) = sz (v .T) := by simp [v2, v1]
      have s4 : sz (v2 .ONE) = 1 := by simp [v2, v1, hO, sz]
      have s5 : sz (v3 .M) = sz (v .M) := by simp [v3, v2, v1]
      have s6 : sz (v3 .X) = sz n := by simp [v3, v2, v1]
      have s7 : sz (v4 .X) = sz n := by simp [v4, v3, v2, v1]
      have s8 : sz (v .X) = 0 := by simp [hX, sz]
      rw [s1, s2, s3, s4, s5, s6, s7, s8]
      omega
    refine (Runs.loopT (by simp [mk, isNum, hb', encNat]) hbody ih').mono ?_
    simp only [List.length_cons]; ring_nf; omega

/-! ## Second pass: the rows `(1, τ + a_j, τ + a_j + 1, tτ + b)` of the items -/

def rowsL (τ dd : ℕ) (rest : List ℕ) : List ℕ := rest.flatMap (fun a => [1, τ + a, τ + a + 1, dd])

def body2 : Prog :=
  .seq (pushProg .R .one) (.seq (pushProg .R .sep) (.seq (rdProg .inp2 .X)
    (.seq (addProg .TAU .X .X) (.seq (addProg .X .ONE .Z) (.seq (emitP .X) (.seq (emitP .Z)
      (.seq (addProg .DD .Z .Z) (emitP .Z))))))))

def loop2 : Prog := .loop (fun h => (h .inp2).isSome) body2

lemma runs_loop2 (W : ℕ) : ∀ (rest : List ℕ) (v : Key → ℕ) (b : Store), Clean b →
    b .inp2 = encNats rest → v .X = 0 → v .Z = 0 → v .ONE = 1 → sz (v .TAU) ≤ W →
    sz (v .DD) ≤ W → (∀ n ∈ rest, sz n ≤ W) →
    Runs loop2 (mk v b) (mk v (Function.update (Function.update b .inp2 []) .R
      ((encNats (rowsL (v .TAU) (v .DD) rest)).reverse ++ b .R)))
      (rest.length * (100 * W + 200) + 1) := by
  intro rest
  induction rest with
  | nil =>
    intro v b hc hb hX hZ hO _ _ _
    have e2 : Function.update (Function.update b .inp2 []) .R
        ((encNats (rowsL (v .TAU) (v .DD) [])).reverse ++ b .R) = b := by
      funext k
      by_cases k1 : k = .R
      · subst k1; simp [rowsL, encNats]
      by_cases k2 : k = .inp2
      · subst k2; simp [hb, encNats]
      simp [k1, k2]
    rw [e2]
    exact (Runs.loopF (by simp [mk, isNum, hb, encNats])).mono (by simp)
  | cons n rest ih =>
    intro v b hc hb hX hZ hO hTau hDD hall
    have hb' : b .inp2 = encNat n ++ encNats rest := by rw [hb, encNats_cons]
    have hn : sz n ≤ W := hall n (by simp)
    have p1 := mk_push .R rfl .one v b
    set b1 := Function.update b .R (BSym.one :: b .R)
    have p2 := mk_push .R rfl .sep v b1
    set b2 := Function.update b1 .R (BSym.sep :: b1 .R)
    have hc2 : Clean b2 := clean_R (clean_R hc _) _
    have r1 := mk_rd .inp2 .X rfl (by decide) rfl v b2 hc2 n (encNats rest)
      (by simp [b2, b1, hb'])
    set b3 := Function.update b2 .inp2 (encNats rest)
    have hc3 : Clean b3 := clean_inp2 hc2 _
    set v1 := Function.update v .X n
    have r2 := mk_add .TAU .X .X rfl rfl rfl v1 b3 hc3
    set v2 := Function.update v1 .X (v1 .TAU + v1 .X)
    have r2b := mk_add .X .ONE .Z rfl rfl rfl v2 b3 hc3
    set v2b := Function.update v2 .Z (v2 .X + v2 .ONE)
    have r3 := mk_emit .X rfl v2b b3
    set v3 := Function.update v2b .X 0
    set b4 := Function.update b3 .R ((encNat (v2b .X)).reverse ++ b3 .R)
    have hc4 : Clean b4 := clean_R hc3 _
    have r3b := mk_emit .Z rfl v3 b4
    set v4 := Function.update v3 .Z 0
    set b5 := Function.update b4 .R ((encNat (v3 .Z)).reverse ++ b4 .R)
    have hc5 : Clean b5 := clean_R hc4 _
    have r4 := mk_add .DD .Z .Z rfl rfl rfl v4 b5 hc5
    set v5 := Function.update v4 .Z (v4 .DD + v4 .Z)
    have r5 := mk_emit .Z rfl v5 b5
    set v6 := Function.update v5 .Z 0
    set b6 := Function.update b5 .R ((encNat (v5 .Z)).reverse ++ b5 .R)
    have hv6 : v6 = v := by
      funext k
      by_cases k1 : k = .Z
      · subst k1; simp [v6, hZ]
      by_cases k2 : k = .X
      · subst k2; simp [v6, v5, v4, v3, hX]
      · simp [v6, v5, v4, v3, v2b, v2, v1, k1, k2]
    rw [hv6] at r5
    have hc6 : Clean b6 := clean_R hc5 _
    have ih' := ih v b6 hc6 (by simp [b6, b5, b4, b3]) hX hZ hO hTau hDD
      (fun m hm => hall m (by simp [hm]))
    have hv2X : v2b .X = v .TAU + n := by simp [v2b, v2, v1]
    have hv3Z : v3 .Z = v .TAU + n + 1 := by simp [v3, v2b, v2, v1, hO]
    have hv5Z : v5 .Z = v .DD := by simp [v5, v4, v3, v2b, v2, v1]
    have hfin : Function.update (Function.update b6 .inp2 []) .R
        ((encNats (rowsL (v .TAU) (v .DD) rest)).reverse ++ b6 .R) =
        Function.update (Function.update b .inp2 []) .R
        ((encNats (rowsL (v .TAU) (v .DD) (n :: rest))).reverse ++ b .R) := by
      have eR : b6 .R = (encNats [1, v .TAU + n, v .TAU + n + 1, v .DD]).reverse ++ b .R := by
        simp [b6, b5, b4, b3, b2, b1, hv2X, hv3Z, hv5Z, encNats, encNat_eq, encN, enc, toB,
          Nat.bits]
      funext k
      by_cases k1 : k = .R
      · subst k1
        simp only [Function.update_self, eR, rowsL, List.flatMap_cons]
        rw [encNats_append]; simp
      by_cases k2 : k = .inp2
      · subst k2; simp [k1]
      simp [k1, k2, b6, b5, b4, b3, b2, b1]
    rw [hfin] at ih'
    have hbody : Runs body2 (mk v b) (mk v b6) (100 * W + 198) := by
      refine (p1.seq (p2.seq (r1.seq (r2.seq (r2b.seq (r3.seq (r3b.seq (r4.seq r5)))))))).mono ?_
      have s1 : sz (v1 .TAU) = sz (v .TAU) := by simp [v1]
      have s2 : sz (v1 .X) = sz n := by simp [v1]
      have s3 : sz (v2 .X) ≤ 2 * W + 1 := by
        have e : v2 .X = v .TAU + n := by simp [v2, v1]
        rw [e]; have := sz_add_le (v .TAU) n; omega
      have s3' : sz (v2b .X) ≤ 2 * W + 1 := by rw [hv2X]; have := sz_add_le (v .TAU) n; omega
      have s4 : sz (v .X) = 0 := by simp [hX, sz]
      have s5 : sz (v2 .ONE) = 1 := by simp [v2, v1, hO, sz]
      have s6 : sz (v2 .Z) = 0 := by simp [v2, v1, hZ, sz]
      have s7 : sz (v3 .Z) ≤ 2 * W + 3 := by
        rw [hv3Z]; have := sz_add_le (v .TAU + n) 1; have := sz_add_le (v .TAU) n
        have : sz 1 = 1 := by simp [sz]
        omega
      have s8 : sz (v4 .DD) = sz (v .DD) := by simp [v4, v3, v2b, v2, v1]
      have s9 : sz (v4 .Z) = 0 := by simp [v4, sz]
      have s10 : sz (v5 .Z) = sz (v .DD) := by rw [hv5Z]
      rw [s1, s2, s4, s5, s6, s8, s9, s10]
      omega
    refine (Runs.loopT (by simp [mk, isNum, hb', encNat]) hbody ih').mono ?_
    simp only [List.length_cons]; ring_nf; omega

end K4d



namespace K4d

open CookPvsNP ProjSchedTW.Complexity

/-! ## The validation automaton: pending digits, last digit is one, bad -/

def vstep : Bool × Bool × Bool → BSym → Bool × Bool × Bool
  | (_, _, bd), .zero => (true, false, bd)
  | (_, _, bd), .one => (true, true, bd)
  | (p, l, _), .minus => (p, l, true)
  | (_, l, bd), .sep => (false, false, bd || !l)

def vOK (x : List BSym) : Prop :=
  x ≠ [] ∧ (x.foldl vstep (false, false, false)).2.2 = false ∧
    (x.foldl vstep (false, false, false)).1 = false

lemma bad_mono (y : List BSym) : ∀ (p l : Bool), (y.foldl vstep (p, l, true)).2.2 = true := by
  induction y with
  | nil => intro p l; rfl
  | cons a y ih => intro p l; cases a <;> simp [vstep, ih]


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
    vOK x ↔ ∃ l : List ℕ, l ≠ [] ∧ (∀ v ∈ l, 0 < v) ∧ x = encNats l := by
  constructor
  · rintro ⟨hne, h2, h1⟩
    have := vOK_decode x [] (by simpa [stOf] using h2) (by simpa [stOf] using h1)
    obtain ⟨l, hl, he⟩ := this
    simp only [enc, List.map_nil, List.nil_append] at he
    refine ⟨l, ?_, hl, he⟩
    rintro rfl; exact hne (by simpa [encNats] using he)
  · rintro ⟨l, hne, hl, rfl⟩
    have := foldl_encNats l hl false false false hne
    refine ⟨?_, by rw [this], by rw [this]⟩
    rcases l with _ | ⟨v, l⟩
    · exact absurd rfl hne
    · rw [encNats_cons, encNat_eq]; simp

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
  .seq (copyProg .inp .inpC .sc) (.seq (.branch (fun h => (h .inpC).isNone) (pushProg .bad .one)
    skipP) (.seq valLoop (.branch (fun h => (h .pend).isSome) (pushProg .bad .one) skipP)))

def s0 (x : List BSym) : Store := fun j => if j = .inp then x else []

lemma runs_phaseA (x : List BSym) : ∃ sA, Runs phaseA (s0 x) sA (9 * x.length + 12) ∧
    sA .out = [] ∧ ((sA .bad).head?.isSome = true ↔ ¬ vOK x) ∧ (vOK x → sA = s0 x) := by
  have r1 := runs_copy .inp .inpC .sc (by decide) (by decide) (by decide) (s0 x) (by simp [s0])
  set s1 := Function.update (s0 x) .inpC (s0 x .inp ++ s0 x .inpC)
  have hs1 : s1 .inpC = x := by simp [s1, s0]
  set s2 := Function.update s1 .bad (flag x.isEmpty)
  have r2 : Runs (.branch (fun h => (h .inpC).isNone) (pushProg .bad .one) skipP) s1 s2 2 := by
    by_cases hx : x = []
    · subst hx
      have := runs_push .bad .one s1
      have e : Function.update s1 .bad (BSym.one :: s1 .bad) = s2 := by
        simp [s2, s1, s0, flag]
      rw [e] at this
      exact Runs.brT (by simp [hs1]) this
    · have e : s2 = s1 := by
        simp only [s2]; rw [Function.update_eq_self_iff]; simp [s1, s0, flag, hx]
      rw [e]
      refine Runs.brF ?_ (runs_skip s1)
      simp [hs1]; exact hx
  set st := x.foldl vstep (false, false, x.isEmpty)
  have r3 := runs_valLoop x (false, false, x.isEmpty) s2 (by simp [s2, hs1])
    (by simp [s2, s1, s0, flag]) (by simp [s2, s1, s0, flag]) (by simp [s2])
  set s3 := vPost st s2
  set sA := if st.1 then Function.update s3 .bad (BSym.one :: s3 .bad) else s3
  have r4 : Runs (.branch (fun h => (h .pend).isSome) (pushProg .bad .one) skipP) s3 sA 2 := by
    by_cases hp : st.1 = true
    · have := runs_push .bad .one s3
      simp only [sA, hp, if_true]
      exact Runs.brT (by simp [s3, vPost, hp, flag]) this
    · simp only [sA, hp]
      exact Runs.brF (by simp [s3, vPost, flag]; simpa using hp) (runs_skip s3)
  refine ⟨sA, (r1.seq (r2.seq (r3.seq r4))).mono ?_, ?_, ?_, ?_⟩
  · simp [s0, hs1]; omega
  · simp only [sA]; split_ifs <;> simp [s3, vPost, s2, s1, s0]
  · have hbad : (sA .bad).head?.isSome = (st.2.2 || st.1) := by
      simp only [sA]; split_ifs with h <;> simp [s3, vPost, h, flag] <;> cases st.2.2 <;> rfl
    rw [hbad]
    unfold vOK
    by_cases hx : x = []
    · subst hx; simp [st]
    · have : x.isEmpty = false := by simpa using hx
      simp only [st, this]
      cases (x.foldl vstep (false, false, false)).2.2 <;>
        cases (x.foldl vstep (false, false, false)).1 <;> simp [hx]
  · intro hv
    obtain ⟨l, hne, hl, hx⟩ := (vOK_iff x).1 hv
    have hxne : x ≠ [] := hv.1
    have hst : st = (false, false, false) := by
      simp only [st]; rw [show x.isEmpty = false by simpa using hxne, hx]
      exact foldl_encNats l hl false false false hne
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
    simp [s3, vPost, s2, s1, k1, k2, k3, k4]

end K4d



namespace K4d

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Tardiness

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

def rowOf (ty : JobType) : List ℕ := [ty.count, ty.p, ty.w, ty.d]

lemma rows_inj : ∀ {ts ts' : List JobType}, ts.length = ts'.length →
    ts.flatMap rowOf = ts'.flatMap rowOf → ts = ts' := by
  intro ts
  induction ts with
  | nil => intro ts' h _; rcases ts' with _ | _ <;> simp_all
  | cons ty ts ih =>
    intro ts' hl h
    rcases ts' with _ | ⟨ty', ts'⟩
    · simp at hl
    · simp only [List.flatMap_cons, rowOf, List.cons_append, List.cons.injEq,
        List.nil_append] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have : ty = ty' := by cases ty; cases ty'; simp_all
      rw [this, ih (by simpa using hl) h5]

lemma length_rows (ts : List JobType) : (ts.flatMap rowOf).length = 4 * ts.length := by
  induction ts with
  | nil => simp
  | cons ty ts ih => simp [rowOf, ih]; ring

lemma multCode_inj {ts ts' : List JobType} {y y' : ℕ} (h : multCode ts y = multCode ts' y') :
    ts = ts' ∧ y = y' := by
  unfold multCode at h
  have h1 := encNats_inj h
  simp only [List.cons_append, List.cons.injEq] at h1
  obtain ⟨hl, h2⟩ := h1
  have e1 : ts.flatMap (fun ty => [ty.count, ty.p, ty.w, ty.d]) = ts.flatMap rowOf := rfl
  have e2 : ts'.flatMap (fun ty => [ty.count, ty.p, ty.w, ty.d]) = ts'.flatMap rowOf := rfl
  rw [e1, e2] at h2
  have hlen : (ts.flatMap rowOf).length = (ts'.flatMap rowOf).length := by
    rw [length_rows, length_rows, hl]
  obtain ⟨h3, h4⟩ := List.append_inj h2 hlen
  exact ⟨rows_inj hl h3, by simpa using h4⟩

lemma multCode_ne_nil (ts : List JobType) (y : ℕ) : multCode ts y ≠ [] := by
  unfold multCode; rw [List.cons_append, encNats_cons, encNat_eq]; simp

/-! ## The construction on lists -/

def tL (as : List ℕ) : ℕ := as.length
def aSL (as : List ℕ) : ℕ := as.foldl max 0
def dL (as : List ℕ) (b : ℕ) : ℕ := as.sum - b
def tPL (as : List ℕ) (b : ℕ) : ℕ :=
  ((tL as + 1) * dL as b + tL as * (tL as + 1) * (aSL as * aSL as) + 1) / 2
def tauL (as : List ℕ) (b : ℕ) : ℕ := tPL as b + tPL as b + as.sum + 1
def ddL (as : List ℕ) (b : ℕ) : ℕ := tL as * tauL as b + b
def yL (as : List ℕ) (b : ℕ) : ℕ :=
  tPL as b * (tPL as b + 1) * tauL as b * (tauL as b + 1) / 2 +
    (tPL as b + 1) * tauL as b * dL as b + tPL as b

def itemType (b : ℕ) (as : List ℕ) (a : ℕ) : JobType :=
  ⟨1, tauL as b + a, tauL as b + a + 1, ddL as b⟩

def dummyType (b : ℕ) (as : List ℕ) : JobType :=
  ⟨tPL as b, tauL as b, tauL as b + 1, ddL as b⟩

def typesL (b : ℕ) (as : List ℕ) : List JobType :=
  as.map (itemType b as) ++ [dummyType b as]

def Fl (b : ℕ) (as : List ℕ) : List BSym :=
  if b < as.sum then multCode (typesL b as) (yL as b)
  else if b = as.sum then [BSym.sep, BSym.sep] else []

open Classical in
noncomputable def F (x : List BSym) : List BSym :=
  if h : ∃ l : List ℕ, l ≠ [] ∧ (∀ v ∈ l, 0 < v) ∧ x = encNats l then
    match h.choose with
    | [] => []
    | b :: as => Fl b as
  else []

lemma F_code (b : ℕ) (as : List ℕ) (hpos : ∀ v ∈ b :: as, 0 < v) :
    F (encNats (b :: as)) = Fl b as := by
  have h : ∃ l : List ℕ, l ≠ [] ∧ (∀ v ∈ l, 0 < v) ∧ encNats (b :: as) = encNats l :=
    ⟨b :: as, by simp, hpos, rfl⟩
  unfold F
  rw [dif_pos h]
  have : h.choose = b :: as := (encNats_inj h.choose_spec.2.2).symm
  rw [this]

lemma F_bad (x : List BSym) (h : ¬ ∃ l : List ℕ, l ≠ [] ∧ (∀ v ∈ l, 0 < v) ∧ x = encNats l) :
    F x = [] := by
  unfold F; rw [dif_neg h]

/-! ## Relation to the platform construction -/

lemma foldl_max_spec (l : List ℕ) : ∀ m : ℕ, m ≤ l.foldl max m ∧ (∀ v ∈ l, v ≤ l.foldl max m) ∧
    ∀ c, m ≤ c → (∀ v ∈ l, v ≤ c) → l.foldl max m ≤ c := by
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
    intro m
    obtain ⟨h1, h2, h3⟩ := ih (max m a)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨le_trans (le_max_left _ _) h1, ⟨le_trans (le_max_right _ _) h1, h2⟩, ?_⟩
    intro c hm ⟨ha, hl⟩
    exact h3 c (max_le hm ha) hl

lemma aStar_eq {t : ℕ} (a : Fin t → ℕ) : aStar a = aSL (List.ofFn a) := by
  unfold aStar aSL
  obtain ⟨h1, h2, h3⟩ := foldl_max_spec (List.ofFn a) 0
  apply le_antisymm
  · exact Finset.sup_le (fun i _ => h2 (a i) (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · apply h3 _ (Nat.zero_le _)
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact Finset.le_sup (f := a) (Finset.mem_univ i)

section consts
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

lemma tL_ofFn : tL (List.ofFn a) = t := by simp [tL]
lemma sum_ofFn' : (List.ofFn a).sum = bigA a := by simp [bigA, List.sum_ofFn]
lemma tPL_eq : tPL (List.ofFn a) b = tPrime a b := by
  simp [tPL, tPrime, tL_ofFn, aStar_eq, dL, sum_ofFn', sq]
lemma tauL_eq : tauL (List.ofFn a) b = 2 * tPrime a b + bigA a + 1 := by
  simp [tauL, tPL_eq, sum_ofFn']; ring
lemma ddL_eq : ddL (List.ofFn a) b = t * (2 * tPrime a b + bigA a + 1) + b := by
  simp [ddL, tauL_eq, tL_ofFn]
lemma yL_eq : yL (List.ofFn a) b = yThr a b (2 * tPrime a b + bigA a + 1) := by
  simp [yL, yThr, tPL_eq, tauL_eq, dL, sum_ofFn']

end consts

lemma hasSched_equiv {J J' : Type} [Fintype J] [Fintype J'] (e : J ≃ J') (p w d : J' → ℕ)
    (y : ℕ) : HasScheduleLE (p ∘ e) (w ∘ e) (d ∘ e) y ↔ HasScheduleLE p w d y := by
  constructor
  · rintro ⟨S, hF, hT⟩
    refine ⟨S ∘ e.symm, ?_, ?_⟩
    · intro i j hij
      have := hF (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))
      simpa [Function.comp] using this
    · unfold totalWeightedTardiness tardiness completion at hT ⊢
      rw [← Equiv.sum_comp e]
      simpa [Function.comp] using hT
  · rintro ⟨S, hF, hT⟩
    refine ⟨S ∘ e, ?_, ?_⟩
    · intro i j hij
      exact hF (e i) (e j) (fun h => hij (e.injective h))
    · unfold totalWeightedTardiness tardiness completion at hT ⊢
      rw [← Equiv.sum_comp e] at hT
      simpa [Function.comp] using hT

section reindex
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

lemma typesL_length : (typesL b (List.ofFn a)).length = t + 1 := by simp [typesL]

lemma typesL_getElem_lt (i : ℕ) (hi : i < (typesL b (List.ofFn a)).length) (h : i < t) :
    (typesL b (List.ofFn a))[i] = itemType b (List.ofFn a) (a ⟨i, h⟩) := by
  simp [typesL, List.getElem_append, h]

lemma typesL_getElem_ge (i : ℕ) (hi : i < (typesL b (List.ofFn a)).length) (h : ¬ i < t) :
    (typesL b (List.ofFn a))[i] = dummyType b (List.ofFn a) := by
  have e := typesL_length a b
  have hit : i - t = 0 := by omega
  simp [typesL, List.getElem_append, h, hit]

lemma typesL_get_lt (i : Fin (typesL b (List.ofFn a)).length) (h : i.val < t) :
    (typesL b (List.ofFn a)).get i = itemType b (List.ofFn a) (a ⟨i.val, h⟩) := by
  rw [List.get_eq_getElem]; exact typesL_getElem_lt a b i.val i.isLt h

lemma typesL_get_ge (i : Fin (typesL b (List.ofFn a)).length) (h : ¬ i.val < t) :
    (typesL b (List.ofFn a)).get i = dummyType b (List.ofFn a) := by
  rw [List.get_eq_getElem]; exact typesL_getElem_ge a b i.val i.isLt h

lemma count_lt (i : Fin (typesL b (List.ofFn a)).length) (h : i.val < t) :
    ((typesL b (List.ofFn a)).get i).count = 1 := by
  rw [typesL_get_lt a b i h]; rfl

lemma count_ge (i : Fin (typesL b (List.ofFn a)).length) (h : ¬ i.val < t) :
    ((typesL b (List.ofFn a)).get i).count = tPrime a b := by
  rw [typesL_get_ge a b i h]; simp [dummyType, tPL_eq]

/-- the expanded job `(i, k)` as a job of the platform instance. -/
def fwd (x : ExpandedJob (typesL b (List.ofFn a))) : Fin (t + tPrime a b) :=
  if h : x.1.val < t then ⟨x.1.val, by omega⟩
  else ⟨t + x.2.val, by have := x.2.isLt; have e := count_ge a b x.1 h; omega⟩

lemma fwd_bij : Function.Bijective (fwd a b) := by
  constructor
  · rintro ⟨i, k⟩ ⟨i', k'⟩ hx
    have hi := i.isLt; have hi' := i'.isLt
    have eL := typesL_length a b
    simp only [fwd] at hx
    by_cases h1 : i.val < t <;> by_cases h2 : i'.val < t
    · rw [dif_pos h1, dif_pos h2] at hx
      have hv : i.val = i'.val := by simpa using congrArg Fin.val hx
      have hii : i = i' := Fin.ext hv
      subst hii
      have hk := k.isLt; have hk' := k'.isLt
      have ec := count_lt a b i h1
      have : k = k' := Fin.ext (by omega)
      rw [this]
    · rw [dif_pos h1, dif_neg h2] at hx
      have := congrArg Fin.val hx; simp at this; omega
    · rw [dif_neg h1, dif_pos h2] at hx
      have := congrArg Fin.val hx; simp at this; omega
    · rw [dif_neg h1, dif_neg h2] at hx
      have hii : i = i' := Fin.ext (by omega)
      subst hii
      have : k = k' := Fin.ext (by have := congrArg Fin.val hx; simp at this; omega)
      rw [this]
  · intro j
    by_cases hj : j.val < t
    · let i : Fin (typesL b (List.ofFn a)).length := ⟨j.val, by rw [typesL_length]; omega⟩
      have hi : i.val < t := hj
      refine ⟨⟨i, ⟨0, by rw [count_lt a b i hi]; omega⟩⟩, ?_⟩
      simp only [fwd, dif_pos hi]; rfl
    · let i : Fin (typesL b (List.ofFn a)).length := ⟨t, by rw [typesL_length]; omega⟩
      have hi : ¬ i.val < t := by simp [i]
      have hj2 := j.isLt
      refine ⟨⟨i, ⟨j.val - t, by rw [count_ge a b i hi]; omega⟩⟩, ?_⟩
      simp only [fwd, dif_neg hi]
      ext; simp; omega

lemma fwd_data (x : ExpandedJob (typesL b (List.ofFn a))) :
    wtP a b (2 * tPrime a b + bigA a + 1) (fwd a b x) = expandP _ x ∧
    wtW a b (2 * tPrime a b + bigA a + 1) (fwd a b x) = expandW _ x ∧
    wtD a b (2 * tPrime a b + bigA a + 1) (fwd a b x) = expandD _ x := by
  obtain ⟨i, k⟩ := x
  simp only [expandP, expandW, expandD, wtP, wtW, wtD]
  by_cases h : i.val < t
  · simp only [fwd, dif_pos h, aExt]
    simp only [typesL_get_lt a b i h, itemType, tauL_eq, ddL_eq]
    simp [h]
  · simp only [fwd, dif_neg h, aExt]
    simp only [typesL_get_ge a b i h, dummyType, tauL_eq, ddL_eq]
    simp

lemma hasSched_iff :
    HasScheduleLE (expandP (typesL b (List.ofFn a))) (expandW (typesL b (List.ofFn a)))
      (expandD (typesL b (List.ofFn a))) (yL (List.ofFn a) b) ↔
    HasScheduleLE (wtP a b (2 * tPrime a b + bigA a + 1)) (wtW a b (2 * tPrime a b + bigA a + 1))
      (wtD a b (2 * tPrime a b + bigA a + 1)) (yThr a b (2 * tPrime a b + bigA a + 1)) := by
  rw [yL_eq]
  have e1 : expandP (typesL b (List.ofFn a)) =
      wtP a b (2 * tPrime a b + bigA a + 1) ∘ (Equiv.ofBijective _ (fwd_bij a b)) := by
    funext x; exact ((fwd_data a b x).1).symm
  have e2 : expandW (typesL b (List.ofFn a)) =
      wtW a b (2 * tPrime a b + bigA a + 1) ∘ (Equiv.ofBijective _ (fwd_bij a b)) := by
    funext x; exact ((fwd_data a b x).2.1).symm
  have e3 : expandD (typesL b (List.ofFn a)) =
      wtD a b (2 * tPrime a b + bigA a + 1) ∘ (Equiv.ofBijective _ (fwd_bij a b)) := by
    funext x; exact ((fwd_data a b x).2.2).symm
  rw [e1, e2, e3]
  exact hasSched_equiv _ _ _ _ _

end reindex

end K4d



namespace K4d

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Tardiness

def compOps : List Op :=
  [.sub .A .Bv .D, .add .T .ONE .T1, .mul .T1 .D .Q, .mul .M .M .M2, .mul .T .T1 .P1,
   .mul .P1 .M2 .P2, .add .Q .P2 .TP, .add .TP .ONE .TP, .half .TP, .add .TP .TP .TAU,
   .add .TAU .A .TAU, .add .TAU .ONE .TAU, .mul .T .TAU .DD, .add .DD .Bv .DD,
   .add .TP .ONE .TP1, .mul .TP .TP1 .Y1, .mul .Y1 .TAU .Y1, .add .TAU .ONE .TAU1,
   .mul .Y1 .TAU1 .Y1, .half .Y1, .mul .TP1 .TAU .Y2, .mul .Y2 .D .Y2, .add .Y1 .Y2 .Y,
   .add .Y .TP .Y, .add .T .ONE .K]

lemma compOps_ok : ∀ o ∈ compOps, o.ok = true := by decide

lemma compOps_length : compOps.length = 25 := rfl

lemma compOps_eval (v : Key → ℕ) (b : ℕ) (as : List ℕ) (hO : v .ONE = 1)
    (hT : v .T = as.length) (hM : v .M = aSL as) (hA : v .A = as.sum) (hB : v .Bv = b) :
    evalL compOps v .TP = tPL as b ∧ evalL compOps v .TAU = tauL as b ∧
    evalL compOps v .TAU1 = tauL as b + 1 ∧ evalL compOps v .DD = ddL as b ∧
    evalL compOps v .Y = yL as b ∧
    evalL compOps v .K = tL as + 1 ∧ evalL compOps v .X = v .X ∧ evalL compOps v .Z = v .Z := by
  simp only [compOps, evalL, Op.eval, Function.update_apply, reduceCtorEq, if_false, if_true,
    hO, hT, hM, hA, hB]
  simp only [tPL, tauL, ddL, yL, dL, tL]
  simp only [and_self]

end K4d



namespace K4d

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Tardiness

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

lemma aSL_le_sum (as : List ℕ) : aSL as ≤ as.sum := by
  obtain ⟨-, -, h3⟩ := foldl_max_spec as 0
  exact h3 _ (Nat.zero_le _) (fun v hv => List.le_sum_of_mem hv)

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

/-! ## Phase B -/

def tailP : Prog :=
  .seq (emitP .TP) (.seq (emitP .TAU) (.seq (emitP .TAU1) (.seq (emitP .DD) (emitP .Y))))

def ltBranch : Prog :=
  .seq (progL compOps) (.seq (emitP .K) (.seq loop2 (.seq tailP
    (transferProg .R (fun k => decide (k = .out))))))

lemma emit_R (k : Key) (hk : isNum k = true) (v : Key → ℕ) (b : Store) (n : ℕ) (hn : v k = n)
    (W : ℕ) (hW : sz n ≤ W) (L : List ℕ) (hR : b .R = (encNats L).reverse) :
    Runs (emitP k) (mk v b) (mk (Function.update v k 0) (Function.update b .R
      (encNats (L ++ [n])).reverse)) (3 * W + 3) := by
  have := mk_emit k hk v b
  rw [hn, hR] at this
  have e : (encNat n).reverse ++ (encNats L).reverse = (encNats (L ++ [n])).reverse := by
    rw [encNats_append]; simp [encNats]
  rw [e] at this
  exact this.mono (by omega)

def fullL (b : ℕ) (as : List ℕ) : List ℕ :=
  [tL as + 1] ++ rowsL (tauL as b) (ddL as b) as ++
    [tPL as b, tauL as b, tauL as b + 1, ddL as b, yL as b]

lemma fullL_eq (b : ℕ) (as : List ℕ) :
    encNats (fullL b as) = multCode (typesL b as) (yL as b) := by
  simp [fullL, multCode, typesL, rowsL, List.flatMap_append, List.flatMap_map, tL, itemType,
    dummyType]

lemma emitU (k : Key) (hk : isNum k = true) (v : Key → ℕ) (b : Store) (n : ℕ) (hn : v k = n)
    (W : ℕ) (hW : sz n ≤ W) (L : List ℕ) :
    Runs (emitP k) (mk v (Function.update b .R (encNats L).reverse))
      (mk (Function.update v k 0) (Function.update b .R (encNats (L ++ [n])).reverse))
      (3 * W + 3) := by
  have := emit_R k hk v (Function.update b .R (encNats L).reverse) n hn W hW L (by simp)
  rwa [Function.update_idem] at this

lemma runs_tail (v : Key → ℕ) (b : Store) (L0 : List ℕ) (hR : b .R = (encNats L0).reverse)
    (W2 : ℕ) (h1 : sz (v .TP) ≤ W2) (h2 : sz (v .TAU) ≤ W2) (h3 : sz (v .TAU1) ≤ W2)
    (h4 : sz (v .DD) ≤ W2) (h5 : sz (v .Y) ≤ W2) :
    ∃ v', Runs tailP (mk v b) (mk v' (Function.update b .R (encNats (L0 ++ [v .TP, v .TAU,
      v .TAU1, v .DD, v .Y])).reverse)) (20 * (W2 + 3)) := by
  set v2 := Function.update v .TP 0
  set v3 := Function.update v2 .TAU 0
  set v4 := Function.update v3 .TAU1 0
  set v5 := Function.update v4 .DD 0
  have t1 := emit_R .TP rfl v b (v .TP) rfl W2 h1 L0 hR
  have t2 := emitU .TAU rfl v2 b (v .TAU) (by simp [v2]) W2 h2 (L0 ++ [v .TP])
  have t3 := emitU .TAU1 rfl v3 b (v .TAU1) (by simp [v3, v2]) W2 h3 (L0 ++ [v .TP] ++ [v .TAU])
  have t4 := emitU .DD rfl v4 b (v .DD) (by simp [v4, v3, v2]) W2 h4
    (L0 ++ [v .TP] ++ [v .TAU] ++ [v .TAU1])
  have t5 := emitU .Y rfl v5 b (v .Y) (by simp [v5, v4, v3, v2]) W2 h5
    (L0 ++ [v .TP] ++ [v .TAU] ++ [v .TAU1] ++ [v .DD])
  have e : L0 ++ [v .TP] ++ [v .TAU] ++ [v .TAU1] ++ [v .DD] ++ [v .Y] =
      L0 ++ [v .TP, v .TAU, v .TAU1, v .DD, v .Y] := by simp
  rw [e] at t5
  have big := t1.seq (t2.seq (t3.seq (t4.seq t5)))
  refine ⟨Function.update v5 .Y 0, big.mono ?_⟩
  omega

lemma fullL_len (b : ℕ) (as : List ℕ) (W W2 : ℕ) (hWW : W ≤ W2) (has : ∀ a ∈ as, sz a ≤ W)
    (bK : sz (tL as + 1) ≤ W2) (bTP : sz (tPL as b) ≤ W2) (bTAU : sz (tauL as b) ≤ W2)
    (bTAU1 : sz (tauL as b + 1) ≤ W2) (bDD : sz (ddL as b) ≤ W2) (bY : sz (yL as b) ≤ W2) :
    (encNats (fullL b as)).length ≤ (4 * as.length + 6) * (2 * W2 + 4) := by
  have s1 : sz 1 = 1 := by rw [← length_encN', encN_one]; rfl
  have h1 := len_encNats_le (fullL b as) (2 * W2 + 3) (by
    intro z hz
    simp only [fullL, rowsL, List.mem_append, List.mem_cons, List.mem_flatMap,
      List.not_mem_nil, or_false] at hz
    rcases hz with (hz | ⟨a, ha, hz⟩) | hz
    · subst hz; omega
    · rcases hz with rfl | rfl | rfl | rfl
      · omega
      · have := sz_add_le (tauL as b) a; have := has a ha; omega
      · have := sz_add_le (tauL as b + a) 1; have := sz_add_le (tauL as b) a
        have := has a ha; omega
      · omega
    · rcases hz with rfl | rfl | rfl | rfl | rfl
      all_goals omega)
  have h2 : (fullL b as).length = 4 * as.length + 6 := by
    simp [fullL, rowsL]; ring
  rw [h2] at h1; exact h1

lemma runs_ltBranch (b : ℕ) (as : List ℕ) (W : ℕ) (v : Key → ℕ) (base : Store) (hc : Clean base)
    (hO : v .ONE = 1) (hT : v .T = as.length) (hM : v .M = aSL as)
    (hA : v .A = as.sum) (hB : v .Bv = b) (hX : v .X = 0) (hZ : v .Z = 0) (hBd : Bd W v)
    (has : ∀ a ∈ as, sz a ≤ W)
    (hi : base .inp2 = encNats as) (hR : base .R = []) (hout : base .out = []) :
    ∃ s, Runs ltBranch (mk v base) s
      ((compOps.length + 1) * (60 * (3 * (2 ^ compOps.length * (W + 1)) + 1) ^ 2 + 1) +
        20 * (2 ^ compOps.length * (W + 1) + 3) + (3 * (2 ^ compOps.length * (W + 1)) + 3) +
        as.length * (100 * (2 ^ compOps.length * (W + 1)) + 200) +
        3 * ((4 * as.length + 6) * (2 * (2 ^ compOps.length * (W + 1)) + 4)) + 10) ∧
      s .out = multCode (typesL b as) (yL as b) := by
  obtain ⟨W2, hW2⟩ : ∃ W2, W2 = 2 ^ compOps.length * (W + 1) := ⟨_, rfl⟩
  rw [← hW2]
  have hWW : W ≤ W2 := by
    rw [hW2]; have := Nat.one_le_two_pow (n := compOps.length); nlinarith
  have r1 := opsL_runs compOps compOps_ok v base hc
  have c1 := costL_le compOps W v hBd
  rw [← hW2] at c1
  obtain ⟨vC, hvC⟩ : ∃ vC, vC = evalL compOps v := ⟨_, rfl⟩
  rw [← hvC] at r1
  have hBd2 : Bd W2 vC := by rw [hvC, hW2]; exact Bd_evalL compOps W v hBd
  obtain ⟨eTP, eTAU, eTAU1, eDD, eY, eK, eX, eZ⟩ := compOps_eval v b as hO hT hM hA hB
  rw [← hvC] at eTP eTAU eTAU1 eDD eY eK eX eZ
  -- emit K
  have r2 := emit_R .K rfl vC base (tL as + 1) eK W2 (by rw [← eK]; exact hBd2 .K) []
    (by simp [hR, encNats])
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = Function.update vC .K 0 := ⟨_, rfl⟩
  rw [← hv1] at r2
  set b1 := Function.update base .R (encNats ([] ++ [tL as + 1])).reverse
  have hc1 : Clean b1 := clean_R hc _
  have hTau1 : v1 .TAU = tauL as b := by simp [hv1, eTAU]
  have hDD1 : v1 .DD = ddL as b := by simp [hv1, eDD]
  have hO1 : v1 .ONE = 1 := by
    have : evalL compOps v .ONE = v .ONE := by
      simp only [compOps, evalL, Op.eval, Function.update_apply, reduceCtorEq, if_false]
    simp [hv1, hvC, this, hO]
  have r3 := runs_loop2 W2 as v1 b1 hc1 (by simp [b1, hi]) (by simp [hv1, eX, hX])
    (by simp [hv1, eZ, hZ]) hO1
    (by rw [hTau1, ← eTAU]; exact hBd2 .TAU) (by rw [hDD1, ← eDD]; exact hBd2 .DD)
    (fun a ha => le_trans (has a ha) hWW)
  rw [hTau1, hDD1] at r3
  set b2 := Function.update (Function.update b1 .inp2 []) .R
      ((encNats (rowsL (tauL as b) (ddL as b) as)).reverse ++ b1 .R)
  set L0 := [tL as + 1] ++ rowsL (tauL as b) (ddL as b) as
  have hR2 : b2 .R = (encNats L0).reverse := by
    rw [show L0 = [tL as + 1] ++ rowsL (tauL as b) (ddL as b) as from rfl, encNats_append,
      List.reverse_append]
    simp [b2, b1]
  have q1 : v1 .TP = tPL as b := by simp [hv1, eTP]
  have q2 : v1 .TAU = tauL as b := hTau1
  have q3 : v1 .TAU1 = tauL as b + 1 := by simp [hv1, eTAU1]
  have q4 : v1 .DD = ddL as b := hDD1
  have q5 : v1 .Y = yL as b := by simp [hv1, eY]
  obtain ⟨v7, r5⟩ := runs_tail v1 b2 L0 hR2 W2 (by rw [q1, ← eTP]; exact hBd2 .TP)
    (by rw [q2, ← eTAU]; exact hBd2 .TAU) (by rw [q3, ← eTAU1]; exact hBd2 .TAU1)
    (by rw [q4, ← eDD]; exact hBd2 .DD) (by rw [q5, ← eY]; exact hBd2 .Y)
  rw [q1, q2, q3, q4, q5] at r5
  have hLF : L0 ++ [tPL as b, tauL as b, tauL as b + 1, ddL as b, yL as b] = fullL b as := by
    simp [L0, fullL]
  rw [hLF] at r5
  set b15 := Function.update b2 .R (encNats (fullL b as)).reverse
  -- final transfer
  have r4 := runs_move .R .out (by decide) (mk v7 b15)
  have hRout : mk v7 b15 .R = (encNats (fullL b as)).reverse := by simp [mk, isNum, b15]
  have hout' : mk v7 b15 .out = [] := by
    simp [mk, isNum, b15, b2, b1, hout]
  have hlen := fullL_len b as W W2 hWW has (by rw [← eK]; exact hBd2 .K)
    (by rw [← eTP]; exact hBd2 .TP) (by rw [← eTAU]; exact hBd2 .TAU)
    (by rw [← eTAU1]; exact hBd2 .TAU1) (by rw [← eDD]; exact hBd2 .DD)
    (by rw [← eY]; exact hBd2 .Y)
  have big := r1.seq (r2.seq (r3.seq (r5.seq r4)))
  refine ⟨_, big.mono ?_, ?_⟩
  · rw [hRout, List.length_reverse]
    omega
  · simp only [Function.update_self, hout', List.append_nil]
    rw [hRout, List.reverse_reverse, fullL_eq]

end K4d



namespace K4d

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Tardiness

def eqBranch : Prog := .seq (pushProg .out .sep) (pushProg .out .sep)

def phaseB : Prog :=
  .seq (pushProg .ONE .one)
    (.seq (rdProg .inp .Bv) (.seq (copyProg .inp .inp2 .sc) (.seq loop1 (.seq (cmpProg .Bv .A)
      (.branch (fun h => (h .lt).isSome) (.seq (popProg .lt) ltBranch)
        (.branch (fun h => (h .gt).isSome) (popProg .gt) eqBranch))))))

def mainProg : Prog := .seq phaseA (.branch (fun h => (h .bad).isSome) skipP phaseB)

def LTb (W L : ℕ) : ℕ :=
  26 * (60 * (3 * (2 ^ 25 * (W + 1)) + 1) ^ 2 + 1) + 20 * (2 ^ 25 * (W + 1) + 3) +
    (3 * (2 ^ 25 * (W + 1)) + 3) + L * (100 * (2 ^ 25 * (W + 1)) + 200) +
    3 * ((4 * L + 6) * (2 * (2 ^ 25 * (W + 1)) + 4)) + 10

def PBb (L : ℕ) : ℕ := 30 * L + L * (100 * (L + 2) + 100) + 100 + LTb (L + 2) L

lemma s0_mk (x : List BSym) : s0 x = mk (fun _ => 0) (s0 x) := by
  funext k
  by_cases hk : isNum k = true
  · rw [mk_num hk, encN_zero]
    have : k ≠ .inp := by intro h; subst h; exact absurd hk (by decide)
    simp [s0, this]
  · rw [mk_base (by simpa using hk)]

lemma clean_s0 (x : List BSym) : Clean (s0 x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s0]

lemma runs_phaseB (b : ℕ) (as : List ℕ) :
    ∃ s, Runs phaseB (s0 (encNats (b :: as))) s (PBb (encNats (b :: as)).length) ∧
      s .out = Fl b as := by
  set x := encNats (b :: as)
  set L := x.length
  obtain ⟨W, hW⟩ : ∃ W, W = L + 2 := ⟨_, rfl⟩
  have hb0 : sz b ≤ L := sz_le_of_mem (by simp)
  have hasL : ∀ a ∈ as, sz a ≤ L := fun a ha => sz_le_of_mem (by simp [ha])
  have hL : L = sz b + 1 + (encNats as).length := len_encNats_cons b as
  have hsum : sz as.sum ≤ L := by
    have := sum_lt_pow as
    have : sz as.sum ≤ (encNats as).length := sz_le_iff.mpr this
    omega
  have hlen : as.length ≤ L := by have := length_le_encNats as; omega
  set base0 := s0 x
  have hc0 : Clean base0 := clean_s0 x
  -- constants
  have p1 := mk_pushNum .ONE rfl (fun _ => 0) base0 1 (by rw [encN_zero, encN_one])
  set v3 := Function.update (fun _ : Key => (0 : ℕ)) .ONE 1
  -- read b
  have r1 := mk_rd .inp .Bv rfl (by decide) rfl v3 base0 hc0 b (encNats as)
    (by simp [base0, s0, x, encNats_cons])
  set v4 := Function.update v3 .Bv b
  set base1 := Function.update base0 .inp (encNats as)
  have hc1 : Clean base1 := clean_inp hc0 _
  have r2 := mk_copyBase .inp .inp2 rfl rfl (by decide) (by decide) (by decide) v4 base1 hc1
  set base2 := Function.update base1 .inp2 (base1 .inp ++ base1 .inp2)
  have hb2 : base2 .inp2 = encNats as := by simp [base2, base1, base0, s0]
  have hc2 : Clean base2 := clean_inp2 hc1 _
  -- loop 1
  have r3 := runs_loop1 W as v4 base2 hc2 (by simp [base2, base1]) (by simp [v4, v3])
    (by simp [v4, v3]) (by simp [v4, v3]; omega)
    (by simp [v4, v3]; have := sz_le_self as.length; omega)
    (by simp [v4, v3, sz]) (fun a ha => by have := hasL a ha; omega)
  set vL := Function.update (Function.update (Function.update v4 .A (v4 .A + as.sum)) .T
    (v4 .T + as.length)) .M (as.foldl max (v4 .M))
  set base3 := Function.update base2 .inp []
  have hc3 : Clean base3 := clean_inp hc2 _
  have eA : vL .A = as.sum := by simp [vL, v4, v3]
  have eT : vL .T = as.length := by simp [vL, v4, v3]
  have eM : vL .M = aSL as := by simp [vL, v4, v3, aSL]
  have eB : vL .Bv = b := by simp [vL, v4]
  have eO : vL .ONE = 1 := by simp [vL, v4, v3]
  have eX : vL .X = 0 := by simp [vL, v4, v3]
  have eZ : vL .Z = 0 := by simp [vL, v4, v3]
  -- compare
  obtain ⟨h1, h2, -, -, h5, -, -, -, h9, h10⟩ := mk_scratch (v := vL) hc3
  have r4 := runs_cmp .Bv .A (num_free rfl).1.1 (num_free rfl).1.1 (by decide) (by decide)
    (by decide) (by decide) (mk vL base3) h1 h2 h5 h9 h10 b as.sum (by rw [mk_num rfl, eB])
    (by rw [mk_num rfl, eA])
  rw [mk_upd_base (k := .lt) rfl, mk_upd_base (k := .gt) rfl] at r4
  set base4 := Function.update (Function.update base3 .lt (flag (decide (b < as.sum)))) .gt
    (flag (decide (as.sum < b)))
  have hs : base0 = mk (fun _ => 0) base0 := s0_mk x
  have e1 : sz (v3 .Bv) = 0 := by simp [v3, sz]
  have e2 : (base1 .inp).length = (encNats as).length := by simp [base1]
  rw [e1] at r1; rw [e2] at r2
  have hloop : as.length * (100 * W + 100) ≤ L * (100 * (L + 2) + 100) := by
    rw [hW]; exact Nat.mul_le_mul_right _ hlen
  by_cases hlt : b < as.sum
  · -- the main case
    have r5 := mk_pop .lt rfl vL base4
    have e5 : Function.update base4 .lt (base4 .lt).tail = base3 := by
      have hgt : ¬ as.sum < b := by omega
      funext k
      by_cases k1 : k = .lt
      · subst k1; simp [base4, hlt, flag, base3, base2, base1, base0, s0]
      by_cases k2 : k = .gt
      · subst k2; simp [base4, hgt, flag, base3, base2, base1, base0, s0]
      simp [base4, k1, k2]
    rw [e5] at r5
    have hBd : Bd W vL := by
      intro k
      simp only [vL, v4, v3, Function.update_apply]
      have hM : sz (as.foldl max 0) ≤ L := le_trans (sz_mono (aSL_le_sum as)) hsum
      have h1' : sz 1 ≤ 1 := by rw [← length_encN', encN_one]; simp
      have hl' := sz_le_self as.length
      split_ifs <;> simp [sz] at * <;> omega
    obtain ⟨s, r6, hout⟩ := runs_ltBranch b as W vL base3 hc3 eO eT eM eA eB eX eZ hBd
      (fun a ha => by have := hasL a ha; omega) (by simp [base3, hb2])
      (by simp [base3, base2, base1, base0, s0]) (by simp [base3, base2, base1, base0, s0])
    have full := p1.seq (r1.seq (r2.seq (r3.seq (r4.seq
      (Runs.brT (test := fun h => (h .lt).isSome) (q := (.branch (fun h => (h .gt).isSome)
        (popProg .gt) eqBranch)) (by simp [mk, isNum, base4, hlt, flag]) (r5.seq r6))))))
    rw [← hs] at full
    refine ⟨s, full.mono ?_, by rw [hout]; simp [Fl, hlt]⟩
    simp only [compOps_length] at *
    unfold PBb LTb
    subst hW
    obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ 25 * (L + 2 + 1) := ⟨_, rfl⟩
    rw [← hP] at *
    have : as.length * (100 * P + 200) ≤ L * (100 * P + 200) := Nat.mul_le_mul_right _ hlen
    have : (4 * as.length + 6) * (2 * P + 4) ≤ (4 * L + 6) * (2 * P + 4) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have hlt' : decide (b < as.sum) = false := by simpa using hlt
    by_cases hgt : as.sum < b
    · have r5 := mk_pop .gt rfl vL base4
      have full := p1.seq (r1.seq (r2.seq (r3.seq (r4.seq
        (Runs.brF (test := fun h => (h .lt).isSome) (p := (.seq (popProg .lt) ltBranch))
          (by simp [mk, isNum, base4, hlt', flag])
          (Runs.brT (test := fun h => (h .gt).isSome) (q := eqBranch)
            (by simp [mk, isNum, base4, hgt, flag]) r5))))))
      rw [← hs] at full
      refine ⟨_, full.mono ?_, ?_⟩
      · unfold PBb; omega
      · simp [mk, isNum, base4, base3, base2, base1, base0, s0, Fl, hlt]; omega
    · have hgt' : decide (as.sum < b) = false := by simpa using hgt
      have q1 := mk_push .out rfl .sep vL base4
      have q2 := mk_push .out rfl .sep vL (Function.update base4 .out (BSym.sep :: base4 .out))
      have full := p1.seq (r1.seq (r2.seq (r3.seq (r4.seq
        (Runs.brF (test := fun h => (h .lt).isSome) (p := (.seq (popProg .lt) ltBranch))
          (by simp [mk, isNum, base4, hlt', flag])
          (Runs.brF (test := fun h => (h .gt).isSome) (p := popProg .gt)
            (by simp [mk, isNum, base4, hgt', flag]) (q1.seq q2)))))))
      rw [← hs] at full
      refine ⟨_, full.mono ?_, ?_⟩
      · unfold PBb; omega
      · have heq : b = as.sum := by omega
        simp [mk, isNum, base4, base3, base2, base1, base0, s0, Fl, hlt, heq]

end K4d



namespace K4d

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Tardiness

lemma main_runs (x : List BSym) :
    ∃ s, Runs mainProg (s0 x) s (9 * x.length + 12 + PBb x.length + 2) ∧ s .out = F x := by
  obtain ⟨sA, rA, hout, hbad, hval⟩ := runs_phaseA x
  by_cases hv : vOK x
  · have hsA := hval hv
    subst hsA
    obtain ⟨l, hne, hl, hx⟩ := (vOK_iff x).1 hv
    rcases l with _ | ⟨b, as⟩
    · exact absurd rfl hne
    obtain ⟨s, rB, hoB⟩ := runs_phaseB b as
    rw [← hx] at rB
    have htest : (s0 x .bad).head?.isSome = false := by
      by_contra h; exact (hbad.1 (by simpa using h)) hv
    refine ⟨s, (rA.seq (Runs.brF (test := fun h => (h .bad).isSome) (p := skipP) htest rB)).mono
      (by omega), ?_⟩
    rw [hoB, hx, F_code b as hl]
  · have htest : (sA .bad).head?.isSome = true := hbad.2 hv
    have : 1 ≤ PBb x.length := by unfold PBb; omega
    refine ⟨sA, (rA.seq (Runs.brT (test := fun h => (h .bad).isSome) (q := phaseB) htest
      (runs_skip sA))).mono (by omega), ?_⟩
    rw [hout, F_bad]
    intro h; exact hv ((vOK_iff x).2 h)

lemma total_bound (L : ℕ) : 9 * L + 12 + PBb L + 2 ≤ 2 ^ 75 * (L + 1) ^ 2 + 0 := by
  unfold PBb LTb
  nlinarith [sq_nonneg L]

lemma F_poly : PolyTimeComputable F := by
  obtain ⟨k, hk⟩ := polynomial_absorb (2 ^ 75) 2 0
  refine stack_program_polytime mainProg .inp .out F k ?_
  intro w
  obtain ⟨s, ⟨n, hn, he⟩, hout⟩ := main_runs w
  exact ⟨s, n, le_trans hn (le_trans (total_bound _) (hk _)), he, hout⟩

lemma hasSched_empty : HasScheduleLE (expandP []) (expandW []) (expandD []) 0 := by
  refine ⟨fun _ => 0, fun i => absurd i.1.isLt (by simp), ?_⟩
  unfold totalWeightedTardiness
  rw [Finset.sum_eq_zero (fun i _ => absurd i.1.isLt (by simp))]
  simp

lemma multCode_nil : multCode [] 0 = [BSym.sep, BSym.sep] := by
  simp [multCode, encNats, encNat]

lemma F_spec (x : List BSym) :
    ((∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
        (∀ j, 0 < a j) ∧ 0 < b ∧ b < bigA a ∧
        HasScheduleLE (wtP a b (2 * tPrime a b + bigA a + 1))
          (wtW a b (2 * tPrime a b + bigA a + 1))
          (wtD a b (2 * tPrime a b + bigA a + 1))
          (yThr a b (2 * tPrime a b + bigA a + 1)) ∧
        x = encNats (b :: List.ofFn a)) ∨
      (∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
        (∀ j, 0 < a j) ∧ 0 < b ∧ b = bigA a ∧ x = encNats (b :: List.ofFn a))) ↔
      F x ∈ wtLangMult := by
  have hpos : ∀ {t : ℕ} (a : Fin t → ℕ) (b : ℕ), (∀ j, 0 < a j) → 0 < b →
      ∀ v ∈ b :: List.ofFn a, 0 < v := by
    intro t a b ha hb v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hb
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv; exact ha i
  constructor
  · rintro (⟨t, a, b, ha, hb, hlt, hy, rfl⟩ | ⟨t, a, b, ha, hb, heq, rfl⟩)
    · rw [F_code b _ (hpos a b ha hb)]
      have hlt' : b < (List.ofFn a).sum := by rw [sum_ofFn']; exact hlt
      simp only [Fl, hlt', if_true]
      exact ⟨typesL b (List.ofFn a), yL (List.ofFn a) b, rfl, (hasSched_iff a b).2 hy⟩
    · rw [F_code b _ (hpos a b ha hb)]
      have heq' : b = (List.ofFn a).sum := by rw [sum_ofFn']; exact heq
      simp only [Fl, heq', lt_irrefl, if_false, if_true]
      exact ⟨[], 0, multCode_nil.symm, hasSched_empty⟩
  · intro h
    by_cases hd : ∃ l : List ℕ, l ≠ [] ∧ (∀ v ∈ l, 0 < v) ∧ x = encNats l
    · obtain ⟨l, hne, hl, rfl⟩ := hd
      rcases l with _ | ⟨b, as⟩
      · exact absurd rfl hne
      obtain ⟨t, a, rfl⟩ : ∃ (t : ℕ) (a : Fin t → ℕ), List.ofFn a = as :=
        ⟨as.length, as.get, List.ofFn_get as⟩
      rw [F_code b _ hl] at h
      have ha : ∀ j, 0 < a j := fun i => hl (a i) (by simp)
      have hb : 0 < b := hl b (by simp)
      have hsum := sum_ofFn' a
      by_cases hlt : b < (List.ofFn a).sum
      · simp only [Fl, hlt, if_true] at h
        obtain ⟨ts, y, hcode, hy⟩ := h
        obtain ⟨rfl, rfl⟩ := multCode_inj hcode.symm
        left
        exact ⟨t, a, b, ha, hb, by rw [← hsum]; exact hlt, (hasSched_iff a b).1 hy, rfl⟩
      · by_cases heq : b = (List.ofFn a).sum
        · right
          exact ⟨t, a, b, ha, hb, by rw [← hsum]; exact heq, rfl⟩
        · simp only [Fl, hlt, heq, if_false] at h
          obtain ⟨ts, y, hcode, -⟩ := h
          exact absurd hcode.symm (multCode_ne_nil ts y)
    · rw [F_bad x hd] at h
      obtain ⟨ts, y, hcode, -⟩ := h
      exact absurd hcode.symm (multCode_ne_nil ts y)

end K4d

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Tardiness

theorem solution :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
            (∀ j, 0 < a j) ∧ 0 < b ∧ b < bigA a ∧
            HasScheduleLE (wtP a b (2 * tPrime a b + bigA a + 1))
              (wtW a b (2 * tPrime a b + bigA a + 1))
              (wtD a b (2 * tPrime a b + bigA a + 1))
              (yThr a b (2 * tPrime a b + bigA a + 1)) ∧
            x = encNats (b :: List.ofFn a)) ∨
          (∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
            (∀ j, 0 < a j) ∧ 0 < b ∧ b = bigA a ∧ x = encNats (b :: List.ofFn a))) ↔
          f x ∈ wtLangMult :=
  ⟨K4d.F, K4d.F_poly, K4d.F_spec⟩
