-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.totalTotal_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T00:29:50.29861+00:00
-- url     : https://prove2.me/submissions/5800492e-1733-4138-917c-08ec02a17fe8

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_TwoAgentSched_TotalTotal_Construction
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_TwoAgentSched_TotalTotal_theorem_9_2_equivalence

set_option autoImplicit false

namespace TT92

open CookPvsNP ProjSchedTW.Complexity

/-! ## Binary arithmetic model (LSB first) -/

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

def Canon : List Bool → Prop
  | [] => True
  | b :: l => (l = [] → b = true) ∧ Canon l

instance canonDec : (l : List Bool) → Decidable (Canon l)
  | [] => isTrue trivial
  | b :: l => by
    have := canonDec l
    exact (inferInstance : Decidable ((l = [] → b = true) ∧ Canon l))

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

/-- one step of the stack adder: inputs absent read as `false`. -/
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

/-! ## Stacks of the machine -/

inductive Key
  | inp | orig | acc | nu | bad | tmp | car | lz | sc | C | V | Bc | PB | R | Ac | Kb | Q | out
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .orig, .acc, .nu, .bad, .tmp, .car, .lz, .sc, .C, .V, .Bc, .PB, .R, .Ac, .Kb,
    .Q, .out}
  complete := by intro x; cases x <;> simp

abbrev Store := Key → List BSym

def toB (b : Bool) : BSym := if b then .one else .zero
def enc (x : List Bool) : List BSym := x.map toB

def bitOf : Option BSym → Bool
  | some .one => true
  | _ => false

def isDig : Option BSym → Bool
  | some .one => true
  | some .zero => true
  | _ => false

def carS (c : Bool) : List BSym := if c then [.one] else []

def addAct (src dst : Key) (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = dst then .pop
  else if k = src then (if isDig (h src) then .pop else .keep)
  else if k = .tmp then .push (toB (bitOf (h dst) ^^ bitOf (h src) ^^ (h .car).isSome))
  else if k = .car then
    (if (bitOf (h dst) && bitOf (h src)) || ((h .car).isSome && (bitOf (h dst) ^^ bitOf (h src)))
      then (if (h .car).isSome then .keep else .push .one)
      else (if (h .car).isSome then .pop else .keep))
  else if k = .lz then
    (if isDig (h src) then
      (if bitOf (h src) then (if (h .lz).isSome then .pop else .keep)
        else (if (h .lz).isSome then .keep else .push .one))
     else .keep)
  else .keep

def addTest (src dst : Key) (h : Key → Option BSym) : Bool :=
  isDig (h src) || (h dst).isSome || (h .car).isSome

def addLoop (src dst : Key) : StackProg Key BSym :=
  .loop (addTest src dst) (.act (addAct src dst))

/-- the leading-zero flag after reading digits `y` -/
def lzF : List Bool → List BSym → List BSym
  | [], z => z
  | b :: l, _ => lzF l (if b then [] else [.one])

def addPost (src dst : Key) (x y : List Bool) (c : Bool) (r : List BSym) (s : Store) : Store :=
  fun k => if k = dst then [] else if k = src then r
    else if k = .tmp then (enc (addB x y c)).reverse ++ s .tmp
    else if k = .car then [] else if k = .lz then lzF y (s .lz) else s k

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

lemma head_enc_append (x : List Bool) (r : List BSym) (hr : isDig r.head? = false) :
    bitOf (enc x ++ r).head? = x.headD false ∧ isDig (enc x ++ r).head? = !x.isEmpty := by
  cases x with
  | nil =>
    simp only [enc, List.map_nil, List.nil_append, List.headD_nil, List.isEmpty_nil, Bool.not_true]
    refine ⟨?_, hr⟩
    rcases r with _ | ⟨a, r⟩
    · rfl
    · cases a <;> simp_all [bitOf, isDig]
  | cons b x => cases b <;> simp [enc, toB, bitOf, isDig]

lemma car_act (a b c : Bool) :
    StackAct.apply (if (a && b) || (c && (a ^^ b)) then (if c then .keep else .push .one)
      else (if c then .pop else .keep)) (carS c) = carS ((a && b) || (c && (a ^^ b))) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma lz_act (y : List Bool) (r : List BSym) (hr : isDig r.head? = false) (z : List BSym)
    (hz : z = [] ∨ z = [.one]) :
    lzF y z = lzF y.tail (StackAct.apply (if isDig (enc y ++ r).head? then
      (if bitOf (enc y ++ r).head? then (if z.head?.isSome then .pop else .keep)
        else (if z.head?.isSome then .keep else .push .one))
     else .keep) z) ∧
    (StackAct.apply (if isDig (enc y ++ r).head? then
      (if bitOf (enc y ++ r).head? then (if z.head?.isSome then .pop else .keep)
        else (if z.head?.isSome then .keep else .push .one))
     else .keep) z = [] ∨ StackAct.apply (if isDig (enc y ++ r).head? then
      (if bitOf (enc y ++ r).head? then (if z.head?.isSome then .pop else .keep)
        else (if z.head?.isSome then .keep else .push .one))
     else .keep) z = [.one]) := by
  have := head_enc_append y r hr
  rw [this.1, this.2]
  rcases y with _ | ⟨b0, y⟩
  · simp [lzF, StackAct.apply, hz]
  · rcases hz with hz | hz <;> cases b0 <;> subst hz <;> simp [lzF, StackAct.apply]

lemma meas_step (x y : List Bool) (c : Bool) (h0 : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    x.tail.length + y.tail.length +
      ((x.headD false && y.headD false) || (c && (x.headD false ^^ y.headD false))).toNat + 1 ≤
      x.length + y.length + c.toNat := by
  rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;>
    (try cases x0) <;> (try cases y0) <;> simp_all <;> omega

lemma test_step (x y : List Bool) (c : Bool) (h0 : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    ((!y.isEmpty) || (!x.isEmpty) || c) = true := by
  rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;> simp_all

lemma exec_addLoop (src dst : Key) (hsd : src ≠ dst)
    (hs1 : src ≠ .tmp) (hs2 : src ≠ .car) (hs3 : src ≠ .lz)
    (hd1 : dst ≠ .tmp) (hd2 : dst ≠ .car) (hd3 : dst ≠ .lz) (r : List BSym)
    (hr : isDig r.head? = false) :
    ∀ (N : ℕ) (x y : List Bool) (c : Bool) (s : Store),
      x.length + y.length + c.toNat ≤ N →
      s dst = enc x → s src = enc y ++ r → s .car = carS c →
      (s .lz = [] ∨ s .lz = [.one]) →
      ∃ n ≤ 3 * (x.length + y.length + c.toNat) + 1,
        (addLoop src dst).Exec s (addPost src dst x y c r s) n := by
  intro N
  induction N with
  | zero =>
    intro x y c s hN hx hy hc hz
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hc0 : c = false := by cases c <;> simp_all
    subst hx0 hy0 hc0
    refine ⟨1, by simp, ?_⟩
    have hpost : addPost src dst [] [] false r s = s := by
      funext k
      simp only [addPost, addB, enc, List.map_nil, List.reverse_nil, List.nil_append, lzF]
      split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp_all [carS, enc]
    rw [hpost]
    apply StackProg.Exec.loopFalse
    simp [addTest, hx, hy, hc, enc, carS, hr]
  | succ N ih =>
    intro x y c s hN hx hy hc hz
    by_cases h0 : x = [] ∧ y = [] ∧ c = false
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      refine ⟨1, by simp, ?_⟩
      have hpost : addPost src dst [] [] false r s = s := by
        funext k
        simp only [addPost, addB, enc, List.map_nil, List.reverse_nil, List.nil_append, lzF]
        split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp_all [carS, enc]
      rw [hpost]
      apply StackProg.Exec.loopFalse
      simp [addTest, hx, hy, hc, enc, carS, hr]
    · have hA := head_enc_append x [] (by simp [isDig])
      have hB := head_enc_append y r hr
      simp only [List.append_nil] at hA
      have hhx : bitOf (s dst).head? = x.headD false := by rw [hx]; exact hA.1
      have hdx : ((s dst).head?).isSome = !x.isEmpty := by rw [hx]; cases x <;> simp [enc]
      have hhy : bitOf (s src).head? = y.headD false := by rw [hy]; exact hB.1
      have hdy : isDig (s src).head? = !y.isEmpty := by rw [hy]; exact hB.2
      have hcs : ((s .car).head?).isSome = c := by rw [hc]; cases c <;> simp [carS]
      have hmeas := meas_step x y c h0
      have htest := test_step x y c h0
      generalize ha : x.headD false = a at hhx hmeas
      generalize hb : y.headD false = b at hhy hmeas
      have hstep := addB_step x y c h0
      rw [ha, hb] at hstep
      obtain ⟨s1, hs1def⟩ : ∃ s1, s1 = StackProg.applyAct (addAct src dst) s := ⟨_, rfl⟩
      have e_dst : s1 dst = enc x.tail := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_true]
        rw [hx]; simp [StackAct.apply, enc, List.map_tail]
      have e_src : s1 src = enc y.tail ++ r := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hsd, if_true, hdy]
        rw [hy]; rcases y with _ | ⟨b0, y⟩ <;> simp [StackAct.apply, enc]
      have e_tmp : s1 .tmp = toB (a ^^ b ^^ c) :: s .tmp := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hd1.symm, if_neg hs1.symm,
          if_true, hhx, hhy, hcs]; rfl
      have e_car : s1 .car = carS ((a && b) || (c && (a ^^ b))) := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hd2.symm, if_neg hs2.symm,
          show (Key.car = Key.tmp) = False from by simp, if_false, if_true, hhx, hhy, hcs]
        rw [hc]; exact car_act a b c
      have e_lz : lzF y (s .lz) = lzF y.tail (s1 .lz) ∧ (s1 .lz = [] ∨ s1 .lz = [.one]) := by
        rw [hs1def]; simp only [StackProg.applyAct, addAct, if_neg hd3.symm, if_neg hs3.symm,
          show (Key.lz = Key.tmp) = False from by simp, show (Key.lz = Key.car) = False from by simp,
          if_false, if_true]
        rw [hy]; exact lz_act y r hr (s .lz) hz
      have e_oth : ∀ k, k ≠ dst → k ≠ src → k ≠ .tmp → k ≠ .car → k ≠ .lz → s1 k = s k := by
        intro k h1 h2 h3 h4 h5
        rw [hs1def]; simp [StackProg.applyAct, addAct, h1, h2, h3, h4, h5, StackAct.apply]
      obtain ⟨m, hm, hex⟩ := ih x.tail y.tail ((a && b) || (c && (a ^^ b))) s1 (by omega)
        e_dst e_src e_car e_lz.2
      refine ⟨1 + 1 + 1 + m, by omega, ?_⟩
      have hpost : addPost src dst x.tail y.tail ((a && b) || (c && (a ^^ b))) r s1 =
          addPost src dst x y c r s := by
        funext k
        simp only [addPost]
        by_cases k1 : k = dst
        · simp [k1]
        by_cases k2 : k = src
        · simp [k2, hsd]
        by_cases k3 : k = .tmp
        · subst k3
          simp only [k1, k2, if_false, if_true, e_tmp, hstep]
          simp [enc]
        by_cases k4 : k = .car
        · subst k4; simp [k1, k2]
        by_cases k5 : k = .lz
        · subst k5; simp [k1, k2, e_lz.1]
        simp [k1, k2, k3, k4, k5, e_oth k k1 k2 k3 k4 k5]
      rw [← hpost]
      subst hs1def
      refine StackProg.Exec.loopTrue ?_ (StackProg.Exec.act _ _) hex
      simp only [addTest, hdy, hdx, hcs]; exact htest

/-! ## Generic transfer / copy -/

lemma exec_transfer (src : Key) (targets : Key → Bool) :
    ∀ (l : List BSym) (s : Store), s src = l →
      ∃ n ≤ 3 * l.length + 1, (transferProg src targets).Exec s (transferStore src targets s) n := by
  intro l
  induction l with
  | nil =>
    intro s hs
    refine ⟨1, by simp, ?_⟩
    have : transferStore src targets s = s := by
      funext k; simp only [transferStore]
      split_ifs with h1 h2 <;> simp_all
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons a l ih =>
    intro s hs
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = StackProg.applyAct (transferAct src targets) s := ⟨_, rfl⟩
    have e1 : s1 src = l := by
      rw [hs1]; simp [StackProg.applyAct, transferAct, StackAct.apply, hs]
    obtain ⟨m, hm, hex⟩ := ih s1 e1
    refine ⟨1 + 1 + 1 + m, by simp; omega, ?_⟩
    have hpost : transferStore src targets s1 = transferStore src targets s := by
      funext k; simp only [transferStore]
      by_cases k1 : k = src
      · simp [k1]
      by_cases k2 : targets k = true
      · simp [k1, k2, e1, hs, hs1, StackProg.applyAct, transferAct, StackAct.apply]
      · simp [k1, k2, hs1, StackProg.applyAct, transferAct, StackAct.apply]
    rw [← hpost]; subst hs1
    exact StackProg.Exec.loopTrue (by simp [hs]) (StackProg.Exec.act _ _) hex

lemma exec_copy (src dst scr : Key) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (s : Store) (hs : s scr = []) :
    ∃ n ≤ 6 * (s src).length + 3,
      (copyProg src dst scr).Exec s (Function.update s dst (s src ++ s dst)) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_transfer src (fun k => decide (k = scr)) (s src) s rfl
  set s1 := transferStore src (fun k => decide (k = scr)) s with hs1
  have hs1scr : s1 scr = (s src).reverse := by simp [hs1, transferStore, h2.symm, hs]
  obtain ⟨n2, hn2, e2⟩ := exec_transfer scr (fun k => decide (k = src ∨ k = dst)) _ s1 hs1scr
  refine ⟨n1 + 1 + n2, by simp at hn2; omega, ?_⟩
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
  rw [← this]
  exact StackProg.Exec.seq e1 e2

/-! ## Tokens of the input -/

def isDigB : BSym → Bool
  | .one => true
  | .zero => true
  | _ => false

def toBool (a : BSym) : Bool := decide (a = .one)

lemma split_digits (w : List BSym) :
    w = enc ((w.takeWhile isDigB).map toBool) ++ w.dropWhile isDigB ∧
      isDig (w.dropWhile isDigB).head? = false := by
  induction w with
  | nil => simp [enc, isDig]
  | cons a w ih =>
    cases a <;> simp [List.takeWhile, List.dropWhile, isDigB, enc, toB, toBool, isDig] at ih ⊢ <;>
      first | exact ih | exact ih.1 | exact ih.2 | simp_all

lemma enc_append_inj {y y' : List Bool} {r r' : List BSym} (hr : isDig r.head? = false)
    (hr' : isDig r'.head? = false) (h : enc y ++ r = enc y' ++ r') : y = y' ∧ r = r' := by
  induction y generalizing y' with
  | nil =>
    rcases y' with _ | ⟨b, y'⟩
    · simpa using h
    · exfalso; simp [enc] at h; subst h; cases b <;> simp [toB, isDig] at hr
  | cons b y ih =>
    rcases y' with _ | ⟨b', y'⟩
    · exfalso; simp [enc] at h; subst h; cases b <;> simp [toB, isDig] at hr'
    · simp only [enc, List.map_cons, List.cons_append, List.cons.injEq] at h
      have hb : b = b' := by cases b <;> cases b' <;> simp_all [toB]
      obtain ⟨h1, h2⟩ := ih (y' := y') h.2
      exact ⟨by rw [hb, h1], h2⟩

lemma encNat_eq (k : ℕ) : encNat k = enc (Nat.bits k) ++ [BSym.sep] := by
  simp [encNat, enc, toB]

lemma lzF_nil_iff (y : List Bool) : lzF y [] = [] ↔ Canon y := by
  suffices h : ∀ z, (z = [] ∨ z = [.one]) →
      (lzF y z = [] ↔ (y = [] → z = []) ∧ Canon y) by
    simpa using h [] (Or.inl rfl)
  induction y with
  | nil => intro z hz; simp [lzF, Canon]
  | cons b l ih =>
    intro z hz
    rw [lzF, ih _ (by cases b <;> simp)]
    cases b <;> simp [Canon]

lemma lzF_cases (y : List Bool) (z : List BSym) (hz : z = [] ∨ z = [.one]) :
    lzF y z = [] ∨ lzF y z = [.one] := by
  induction y generalizing z with
  | nil => simpa [lzF] using hz
  | cons b l ih => exact ih _ (by cases b <;> simp)

/-! ## The parse loop -/

def termAct (h : Key → Option BSym) (k : Key) : StackAct BSym :=
  if decide (h .inp = some .sep) && (h .lz).isNone then
    (if k = .inp then .pop else if k = .nu then .push .one else .keep)
  else (if k = .bad then .push .one else .keep)

def parseBody : StackProg Key BSym :=
  (addLoop .inp .acc).seq ((transferProg .tmp (fun k => decide (k = .acc))).seq (.act termAct))

def parseTest (h : Key → Option BSym) : Bool := (h .inp).isSome && (h .bad).isNone

def parseLoop : StackProg Key BSym := .loop parseTest parseBody

/-- parse-phase stores: the seven working stacks, everything else from `s0`. -/
def PS (s0 : Store) (i a n b z t : List BSym) : Store := fun k =>
  match k with
  | .inp => i | .acc => a | .nu => n | .bad => b | .lz => z | .tmp => t | .car => []
  | .orig => s0 .orig | .sc => s0 .sc | .C => s0 .C | .V => s0 .V | .Bc => s0 .Bc
  | .PB => s0 .PB | .R => s0 .R | .Ac => s0 .Ac | .Kb => s0 .Kb | .Q => s0 .Q | .out => s0 .out

lemma length_addB_le (x y : List Bool) (c : Bool) :
    (addB x y c).length ≤ x.length + y.length + 1 := by
  induction x, y, c using addB.induct <;> simp_all [addB] <;> omega

lemma parse_iter (s0 : Store) (x y : List Bool) (r nu : List BSym) (hr : isDig r.head? = false) :
    ∃ n ≤ 6 * (x.length + y.length) + 10,
      parseBody.Exec (PS s0 (enc y ++ r) (enc x) nu [] [] [])
        (if r.head? = some .sep ∧ Canon y then PS s0 r.tail (enc (addB x y false)) (.one :: nu) [] [] []
          else PS s0 r (enc (addB x y false)) nu [.one] (lzF y []) []) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_addLoop .inp .acc (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) r hr _ x y false (PS s0 (enc y ++ r) (enc x) nu [] [] [])
    le_rfl rfl rfl rfl (Or.inl rfl)
  have p1 : addPost .inp .acc x y false r (PS s0 (enc y ++ r) (enc x) nu [] [] []) =
      PS s0 r [] nu [] (lzF y []) (enc (addB x y false)).reverse := by
    funext k; cases k <;> simp [addPost, PS]
  rw [p1] at e1
  obtain ⟨n2, hn2, e2⟩ := exec_transfer .tmp (fun k => decide (k = .acc)) _
    (PS s0 r [] nu [] (lzF y []) (enc (addB x y false)).reverse) rfl
  have p2 : transferStore .tmp (fun k => decide (k = .acc))
      (PS s0 r [] nu [] (lzF y []) (enc (addB x y false)).reverse) =
      PS s0 r (enc (addB x y false)) nu [] (lzF y []) [] := by
    funext k; cases k <;> simp [transferStore, PS]
  rw [p2] at e2
  have p3 : StackProg.applyAct termAct (PS s0 r (enc (addB x y false)) nu [] (lzF y []) []) =
      (if r.head? = some .sep ∧ Canon y then PS s0 r.tail (enc (addB x y false)) (.one :: nu) [] [] []
        else PS s0 r (enc (addB x y false)) nu [.one] (lzF y []) []) := by
    have hz := lzF_cases y [] (Or.inl rfl)
    have hiff := lzF_nil_iff y
    by_cases hc : r.head? = some .sep ∧ Canon y
    · rw [if_pos hc]
      have hl : lzF y [] = [] := hiff.2 hc.2
      funext k; cases k <;> simp [StackProg.applyAct, termAct, PS, hc.1, hl, StackAct.apply]
    · rw [if_neg hc]
      have hn : ¬ (decide (r.head? = some BSym.sep) && (lzF y []).head?.isNone) = true := by
        intro h; apply hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
          List.head?_eq_none_iff] at h
        exact ⟨h.1, hiff.1 h.2⟩
      have hcond : (decide (r.head? = some BSym.sep) && (lzF y []).head?.isNone) = false :=
        Bool.eq_false_iff.mpr hn
      have hc' : ¬(decide (r.head? = some BSym.sep) = true ∧ lzF y [] = []) :=
        fun h => hc ⟨by simpa using h.1, hiff.1 h.2⟩
      funext k; cases k <;> simp [StackProg.applyAct, termAct, PS, StackAct.apply] <;>
        split_ifs with h <;> first | rfl | exact absurd h hc'
  have e3 := StackProg.Exec.act termAct (PS s0 r (enc (addB x y false)) nu [] (lzF y []) [])
  rw [p3] at e3
  have hlen := length_addB_le x y false
  simp only [PS, enc, List.length_reverse, List.length_map, Bool.toNat_false] at hn2 hn1
  refine ⟨n1 + 1 + (n2 + 1 + 1), by omega, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)⟩

/-! ## The whole parse loop -/

lemma encNats_cons' (k : ℕ) (sl : List ℕ) :
    encNats (k :: sl) = enc (Nat.bits k) ++ (BSym.sep :: encNats sl) := by
  simp [encNats, encNat_eq]

lemma encNats_eq_nil {sl : List ℕ} (h : encNats sl = []) : sl = [] := by
  cases sl with
  | nil => rfl
  | cons k sl => rw [encNats_cons'] at h; simp at h

def pbound (L A : ℕ) : ℕ := (L + 1) * (12 * (A + L) + 20) + 1

lemma pbound_step (A Y R A' n m : ℕ) (hA : A' ≤ A + Y + 1) (hn : n ≤ 6 * (A + Y) + 10)
    (hm : m ≤ pbound R A') : 1 + n + 1 + m ≤ pbound (Y + 1 + R) A := by
  unfold pbound at *
  have h1 : (R + 1) * (12 * (A' + R) + 20) ≤ (R + 1) * (12 * (A + Y + 1 + R) + 20) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (Y + 1 + R + 1) * (12 * (A + (Y + 1 + R)) + 20) =
      (R + 1) * (12 * (A + Y + 1 + R) + 20) + (Y + 1) * (12 * (A + Y + 1 + R) + 20) := by ring
  have h3 : 12 * (A + Y + 1 + R) + 20 ≤ (Y + 1) * (12 * (A + Y + 1 + R) + 20) :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [h2]; omega

lemma pbound_ge (L A : ℕ) : 12 * (A + L) + 21 ≤ pbound L A := by
  unfold pbound
  have : 12 * (A + L) + 20 ≤ (L + 1) * (12 * (A + L) + 20) := Nat.le_mul_of_pos_left _ (by omega)
  omega

lemma parse_nil (s0 : Store) (a : ℕ) (nu : List BSym) :
    ∃ t n, n ≤ pbound ([] : List BSym).length (Nat.bits a).length ∧
      parseLoop.Exec (PS s0 [] (enc (Nat.bits a)) nu [] [] []) t n ∧
      (∀ sl, ([] : List BSym) = encNats sl →
        t = PS s0 [] (enc (Nat.bits (a + sl.sum))) (List.replicate sl.length .one ++ nu) [] [] []) ∧
      ((∀ sl, ([] : List BSym) ≠ encNats sl) →
        ∃ i' a' nu' z', t = PS s0 i' a' nu' [.one] z' []) := by
  refine ⟨_, 1, by simp [pbound], StackProg.Exec.loopFalse (by simp [parseTest, PS]), ?_, ?_⟩
  · intro sl hsl
    have := encNats_eq_nil hsl.symm; subst this; simp
  · intro h; exact absurd rfl (h [])

lemma parse_all (s0 : Store) : ∀ (L : ℕ) (i : List BSym) (a : ℕ) (nu : List BSym), i.length ≤ L →
    ∃ t n, n ≤ pbound i.length (Nat.bits a).length ∧
      parseLoop.Exec (PS s0 i (enc (Nat.bits a)) nu [] [] []) t n ∧
      (∀ sl, i = encNats sl →
        t = PS s0 [] (enc (Nat.bits (a + sl.sum))) (List.replicate sl.length .one ++ nu) [] [] []) ∧
      ((∀ sl, i ≠ encNats sl) → ∃ i' a' nu' z', t = PS s0 i' a' nu' [.one] z' []) := by
  intro L
  induction L with
  | zero =>
    intro i a nu hi
    have : i = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact parse_nil s0 a nu
  | succ L ih =>
    intro i a nu hi
    by_cases hnil : i = []
    · subst hnil; exact parse_nil s0 a nu
    obtain ⟨y, r, hi_eq, hr⟩ : ∃ y r, i = enc y ++ r ∧ isDig r.head? = false :=
      ⟨_, _, (split_digits i).1, (split_digits i).2⟩
    subst hi_eq
    have htest : parseTest (fun k => (PS s0 (enc y ++ r) (enc (Nat.bits a)) nu [] [] [] k).head?)
        = true := by
      simp only [parseTest, PS, List.head?_nil, Option.isNone_none, Bool.and_true]
      cases h : (enc y ++ r) with
      | nil => exact absurd h hnil
      | cons _ _ => rfl
    obtain ⟨n, hn, eb⟩ := parse_iter s0 (Nat.bits a) y r nu hr
    have hlen : (enc y ++ r).length = y.length + r.length := by simp [enc]
    by_cases hc : r.head? = some .sep ∧ Canon y
    · rw [if_pos hc] at eb
      obtain ⟨r', rfl⟩ : ∃ r', r = .sep :: r' := by
        rcases r with _ | ⟨b, r'⟩
        · simp at hc
        · simp at hc; exact ⟨r', by rw [hc.1]⟩
      set k := bval y with hk
      have hy : Nat.bits k = y := bits_bval hc.2
      have hadd : addB (Nat.bits a) y false = Nat.bits (a + k) := by rw [← hy, bits_add]
      rw [hadd] at eb
      simp only [List.tail_cons] at eb
      obtain ⟨t, m, hm, hex, hval, hinv⟩ := ih r' (a + k) (.one :: nu) (by simp at hlen hi; omega)
      have hA : (Nat.bits (a + k)).length ≤ (Nat.bits a).length + y.length + 1 := by
        rw [← hadd]; exact length_addB_le _ _ _
      refine ⟨t, 1 + n + 1 + m, ?_, StackProg.Exec.loopTrue htest eb hex, ?_, ?_⟩
      · have := pbound_step _ _ _ _ _ _ hA hn hm
        simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · intro sl hsl
        rcases sl with _ | ⟨k', sl'⟩
        · exact absurd hsl (by simp [encNats])
        rw [encNats_cons'] at hsl
        obtain ⟨h1, h2⟩ := enc_append_inj hr (by rfl) hsl
        simp only [List.cons.injEq, true_and] at h2
        have hkk : k = k' := by rw [hk, h1, (canon_bits_bval k').2]
        rw [hval sl' h2, ← hkk]
        simp [List.replicate_succ', Nat.add_assoc]
      · intro hall
        apply hinv
        intro sl' h'
        apply hall (k :: sl')
        rw [encNats_cons', hy, h']
    · rw [if_neg hc] at eb
      refine ⟨_, 1 + n + 1 + 1, ?_,
        StackProg.Exec.loopTrue htest eb (StackProg.Exec.loopFalse (by simp [parseTest, PS])), ?_, ?_⟩
      · have := pbound_ge (enc y ++ r).length (Nat.bits a).length
        rw [hlen] at this ⊢; omega
      · intro sl hsl
        exfalso
        rcases sl with _ | ⟨k', sl'⟩
        · exact hnil hsl
        rw [encNats_cons'] at hsl
        obtain ⟨h1, h2⟩ := enc_append_inj hr (by rfl) hsl
        apply hc; subst h1 h2
        exact ⟨rfl, (canon_bits_bval k').1⟩
      · intro _; exact ⟨_, _, _, _, rfl⟩


end TT92


set_option autoImplicit false

namespace TT92

open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal

/-! ## Subset sums -/

inductive Sums : List ℕ → ℕ → Prop
  | nil : Sums [] 0
  | skip {x : ℕ} {l : List ℕ} {a : ℕ} : Sums l a → Sums (x :: l) a
  | take {x : ℕ} {l : List ℕ} {a : ℕ} : Sums l a → Sums (x :: l) (a + x)

lemma Sums.le_sum {l : List ℕ} {a : ℕ} (h : Sums l a) : a ≤ l.sum := by
  induction h with
  | nil => simp
  | skip _ ih => simp; omega
  | take _ ih => simp; omega

lemma sum_fin_cons (x : ℕ) (xs : List ℕ) (A : Finset (Fin (xs.length + 1))) :
    ∑ i ∈ A, (x :: xs).get i = (if 0 ∈ A then x else 0) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin xs.length => i.succ ∈ A), xs.get i := by
  rw [Finset.sum_filter, ← Finset.univ_inter A, ← Finset.sum_ite_mem, Fin.sum_univ_succ]
  simp

lemma sums_iff (s : List ℕ) (a : ℕ) :
    Sums s a ↔ ∃ A : Finset (Fin s.length), ∑ i ∈ A, s.get i = a := by
  induction s generalizing a with
  | nil =>
    constructor
    · rintro ⟨⟩; exact ⟨∅, by simp⟩
    · rintro ⟨A, hA⟩
      have : A = ∅ := by ext i; exact i.elim0
      subst this; simp at hA; subst hA; exact Sums.nil
  | cons x xs ih =>
    show _ ↔ ∃ A : Finset (Fin (xs.length + 1)), ∑ i ∈ A, (x :: xs).get i = a
    constructor
    · intro h
      cases h with
      | skip h =>
        obtain ⟨A, hA⟩ := (ih a).1 h
        refine ⟨A.map (Fin.succEmb _), ?_⟩
        rw [sum_fin_cons]
        rw [if_neg (by simp [Fin.succ_ne_zero]), ← hA, zero_add]
        congr 1; ext i; simp
      | take h =>
        rename_i a'
        obtain ⟨A, hA⟩ := (ih a').1 h
        refine ⟨insert 0 (A.map (Fin.succEmb _)), ?_⟩
        rw [sum_fin_cons]
        rw [if_pos (by simp), ← hA, add_comm]
        congr 1; apply Finset.sum_congr _ (fun _ _ => rfl); ext i; simp [Fin.succ_ne_zero]
    · rintro ⟨A, hA⟩
      rw [sum_fin_cons] at hA
      split_ifs at hA with h0
      · rw [← hA, add_comm]; exact Sums.take ((ih _).2 ⟨_, rfl⟩)
      · rw [← hA, zero_add]; exact Sums.skip ((ih _).2 ⟨_, rfl⟩)

lemma sum_get_eq (s : List ℕ) : ∑ i : Fin s.length, s.get i = s.sum := by
  simp [List.sum_ofFn]

lemma partitionYes_iff (s : List ℕ) : PartitionYes s ↔ ∃ a, Sums s a ∧ 2 * a = s.sum := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨_, (sums_iff s _).2 ⟨A, rfl⟩, ?_⟩
    have := Finset.sum_add_sum_compl A (fun i => s.get i)
    rw [sum_get_eq] at this; omega
  · rintro ⟨a, ha, h2⟩
    obtain ⟨A, hA⟩ := (sums_iff s a).1 ha
    refine ⟨A, ?_⟩
    have := Finset.sum_add_sum_compl A (fun i => s.get i)
    rw [sum_get_eq] at this; omega

/-! ## The distinct values: for the `j`-th nonzero size `x`, the pair `jZ, jZ + x` -/

def go (Z : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | c, x :: xs => if x = 0 then go Z c xs else c * Z :: (c * Z + x) :: go Z (c + 1) xs

def Bs (Z : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | c, x :: xs => if x = 0 then Bs Z c xs else c * Z + Bs Z (c + 1) xs

lemma go_sum (Z : ℕ) : ∀ (l : List ℕ) (c : ℕ), (go Z c l).sum = 2 * Bs Z c l + l.sum := by
  intro l
  induction l with
  | nil => intro c; simp [go, Bs]
  | cons x xs ih =>
    intro c
    by_cases hx : x = 0
    · simp [go, Bs, hx, ih]
    · simp [go, Bs, hx, ih]; ring

lemma Bs_dvd (Z : ℕ) : ∀ (l : List ℕ) (c : ℕ), Z ∣ Bs Z c l := by
  intro l
  induction l with
  | nil => intro c; simp [Bs]
  | cons x xs ih =>
    intro c
    by_cases hx : x = 0
    · simp [Bs, hx, ih]
    · simp only [Bs, hx, if_false]; exact dvd_add (dvd_mul_left _ _) (ih _)

lemma sums_go_of (Z : ℕ) : ∀ (l : List ℕ) (c e : ℕ), Sums l e → Sums (go Z c l) (Bs Z c l + e) := by
  intro l
  induction l with
  | nil => intro c e h; cases h; simpa [go, Bs] using Sums.nil
  | cons x xs ih =>
    intro c e h
    by_cases hx : x = 0
    · subst hx
      simp only [go, Bs, if_true]
      cases h with
      | skip h => exact ih c e h
      | take h => simpa using ih c _ h
    · simp only [go, Bs, hx, if_false]
      cases h with
      | skip h =>
        have := Sums.take (x := c * Z) (Sums.skip (x := c * Z + x) (ih (c + 1) e h))
        convert this using 1; ring
      | take h =>
        rename_i e'
        have := Sums.skip (x := c * Z) (Sums.take (x := c * Z + x) (ih (c + 1) e' h))
        convert this using 1; ring

lemma sums_go_to (Z : ℕ) : ∀ (l : List ℕ) (c a : ℕ), Sums (go Z c l) a →
    ∃ α e, a = Z * α + e ∧ Sums l e := by
  intro l
  induction l with
  | nil => intro c a h; cases h; exact ⟨0, 0, by simp, Sums.nil⟩
  | cons x xs ih =>
    intro c a h
    by_cases hx : x = 0
    · subst hx
      simp only [go, if_true] at h
      obtain ⟨α, e, rfl, he⟩ := ih c a h
      exact ⟨α, e, rfl, Sums.skip he⟩
    · simp only [go, hx, if_false] at h
      cases h with
      | skip h =>
        cases h with
        | skip h =>
          obtain ⟨α, e, rfl, he⟩ := ih _ _ h
          exact ⟨α, e, rfl, Sums.skip he⟩
        | take h =>
          rename_i a'
          obtain ⟨α, e, rfl, he⟩ := ih _ _ h
          exact ⟨α + c, e + x, by ring, Sums.take he⟩
      | take h =>
        rename_i a'
        cases h with
        | skip h =>
          obtain ⟨α, e, rfl, he⟩ := ih _ _ h
          exact ⟨α + c, e, by ring, Sums.skip he⟩
        | take h =>
          obtain ⟨α, e, rfl, he⟩ := ih _ _ h
          exact ⟨α + 2 * c, e + x, by ring, Sums.take he⟩

theorem partition_go (Z : ℕ) (l : List ℕ) (c : ℕ) (hZ : l.sum < Z) :
    PartitionYes l ↔ PartitionYes (go Z c l) := by
  rw [partitionYes_iff, partitionYes_iff, go_sum]
  constructor
  · rintro ⟨e, he, h2⟩
    exact ⟨_, sums_go_of Z l c e he, by omega⟩
  · rintro ⟨a, ha, h2⟩
    obtain ⟨α, e, rfl, he⟩ := sums_go_to Z l c a ha
    refine ⟨e, he, ?_⟩
    obtain ⟨β, hβ⟩ := Bs_dvd Z l c
    rw [hβ] at h2
    have hle := he.le_sum
    -- 2 Z α + 2 e = 2 Z β + S with 2e < 2Z, S < 2Z
    have h3 : (2 * Z) * α + 2 * e = (2 * Z) * β + l.sum := by linarith
    have m1 := congrArg (· % (2 * Z)) h3
    simp only [Nat.mul_add_mod] at m1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at m1
    exact m1

lemma go_ge (Z : ℕ) : ∀ (l : List ℕ) (c : ℕ), ∀ v ∈ go Z c l, c * Z ≤ v := by
  intro l
  induction l with
  | nil => intro c v hv; simp [go] at hv
  | cons x xs ih =>
    intro c v hv
    by_cases hx : x = 0
    · simp only [go, hx, if_true] at hv; exact ih c v hv
    · simp only [go, hx, if_false, List.mem_cons] at hv
      rcases hv with rfl | rfl | hv
      · exact le_rfl
      · omega
      · have := ih (c + 1) v hv
        have : c * Z ≤ (c + 1) * Z := Nat.mul_le_mul_right _ (by omega)
        omega

lemma go_sorted (Z : ℕ) : ∀ (l : List ℕ) (c : ℕ), (∀ x ∈ l, x < Z) →
    (go Z c l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro c _; simp [go]
  | cons x xs ih =>
    intro c hl
    have hxZ := hl x (by simp)
    have hrest := ih (c + 1) (fun y hy => hl y (by simp [hy]))
    by_cases hx : x = 0
    · simp only [go, hx, if_true]; exact ih c (fun y hy => hl y (by simp [hy]))
    · simp only [go, hx, if_false]
      have hge := go_ge Z xs (c + 1)
      have e1 : (c + 1) * Z = c * Z + Z := by ring
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hrest)
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · omega
        · have := hge v hv; omega
      · intro v hv; have := hge v hv; omega

/-! ## The accumulated weighted sum -/

def stp (p : ℕ × ℕ) (v : ℕ) : ℕ × ℕ := (p.1 + p.2, p.2 + v)

def wa (l : List ℕ) : ℕ × ℕ := l.foldl stp (0, 0)

def wl (l : List ℕ) : ℕ := ∑ i ∈ Finset.range l.length, (l.length - (i + 1)) * l.getD i 0

lemma wa_snoc (l : List ℕ) (v : ℕ) : wa (l ++ [v]) = stp (wa l) v := by
  simp [wa, List.foldl_append]

lemma wa_eq (l : List ℕ) : wa l = (wl l, l.sum) := by
  induction l using List.reverseRec with
  | nil => simp [wa, wl]
  | append_singleton l v ih =>
    rw [wa_snoc, ih]
    simp only [stp, List.sum_append, List.sum_singleton, Prod.mk.injEq, and_true]
    unfold wl
    simp only [List.length_append, List.length_singleton]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, zero_mul, add_zero]
    have hs : l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => l.getD i 0) l.length, ← sum_get_eq]
      simp
    rw [hs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [List.getD_append _ _ _ _ hi]
    have : l.length + 1 - (i + 1) = (l.length - (i + 1)) + 1 := by omega
    rw [this]; ring

lemma weightedSum_eq (l : List ℕ) : weightedSum l.get = wl l := by
  unfold weightedSum wl
  rw [← Fin.sum_univ_eq_sum_range (fun i => (l.length - (i + 1)) * l.getD i 0)]
  apply Finset.sum_congr rfl
  intro i _; simp

lemma bigP_eq (l : List ℕ) : bigP l.get = l.sum := by
  unfold bigP; exact sum_get_eq l

end TT92


set_option autoImplicit false

namespace TT92

open CookPvsNP ProjSchedTW.Complexity

lemma bits_one : Nat.bits 1 = [true] := by
  have := Nat.bits_append_bit 0 true (by simp)
  simpa using this

/-! ## Primitive programs -/

def LzOk (z : List BSym) : Prop := z = [] ∨ z = [.one]

lemma exec_push (c : Key) (a : BSym) (s : Store) :
    (pushProg c a).Exec s (Function.update s c (a :: s c)) 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (k : Key) =>
    if k = c then StackAct.push a else StackAct.keep) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (k : Key) =>
      if k = c then StackAct.push a else StackAct.keep) s = Function.update s c (a :: s c) := by
    funext k; by_cases hk : k = c
    · subst hk; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, hk]
  rw [this] at e; exact e

lemma exec_pop (c : Key) (s : Store) :
    (popProg c).Exec s (Function.update s c (s c).tail) 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (k : Key) =>
    if k = c then StackAct.pop else (StackAct.keep : StackAct BSym)) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (k : Key) =>
      if k = c then StackAct.pop else (StackAct.keep : StackAct BSym)) s =
      Function.update s c (s c).tail := by
    funext k; by_cases hk : k = c
    · subst hk; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, hk]
  rw [this] at e; exact e

def skipP : StackProg Key BSym := .act (fun _ _ => .keep)

lemma exec_skip (s : Store) : skipP.Exec s s 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (_ : Key) =>
    (StackAct.keep : StackAct BSym)) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (_ : Key) =>
      (StackAct.keep : StackAct BSym)) s = s := by
    funext k; simp [StackProg.applyAct, StackAct.apply]
  rw [this] at e; exact e

/-- reverse `src` onto `dst`, keeping `src` (scratch `sc`). -/
def revTo (src dst : Key) : StackProg Key BSym :=
  .seq (transferProg src (fun k => decide (k = dst ∨ k = .sc)))
    (transferProg .sc (fun k => decide (k = src)))

lemma exec_revTo (src dst : Key) (h1 : src ≠ dst) (h2 : src ≠ .sc) (h3 : dst ≠ .sc)
    (s : Store) (hs : s .sc = []) :
    ∃ n ≤ 6 * (s src).length + 3,
      (revTo src dst).Exec s (Function.update s dst ((s src).reverse ++ s dst)) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_transfer src (fun k => decide (k = dst ∨ k = .sc)) (s src) s rfl
  set s1 := transferStore src (fun k => decide (k = dst ∨ k = .sc)) s with hs1
  have hs1sc : s1 .sc = (s src).reverse := by simp [hs1, transferStore, h2.symm, hs]
  obtain ⟨n2, hn2, e2⟩ := exec_transfer .sc (fun k => decide (k = src)) _ s1 hs1sc
  refine ⟨n1 + 1 + n2, by simp at hn2; omega, ?_⟩
  have : transferStore .sc (fun k => decide (k = src)) s1 =
      Function.update s dst ((s src).reverse ++ s dst) := by
    funext k
    by_cases k1 : k = .sc
    · subst k1; simp [transferStore, h3.symm, hs]
    by_cases k2 : k = src
    · subst k2; simp [transferStore, hs1, k1, h1, hs, Ne.symm h2]
    by_cases k3 : k = dst
    · subst k3; simp [transferStore, hs1, k1, k2]
    · simp [transferStore, hs1, k1, k2, k3]
  rw [← this]
  exact StackProg.Exec.seq e1 e2

/-- `dst := dst + src` (both binary, LSB on top); the digits of `src` are consumed. -/
def addTo (src dst : Key) : StackProg Key BSym :=
  .seq (addLoop src dst) (transferProg .tmp (fun k => decide (k = dst)))

lemma exec_addTo (src dst : Key) (hsd : src ≠ dst)
    (hs1 : src ≠ .tmp) (hs2 : src ≠ .car) (hs3 : src ≠ .lz)
    (hd1 : dst ≠ .tmp) (hd2 : dst ≠ .car) (hd3 : dst ≠ .lz) (a b : ℕ) (r : List BSym)
    (hr : isDig r.head? = false) (s : Store)
    (hd : s dst = enc (Nat.bits a)) (hs : s src = enc (Nat.bits b) ++ r)
    (htmp : s .tmp = []) (hcar : s .car = []) (hlz : LzOk (s .lz)) :
    ∃ n ≤ 6 * ((Nat.bits a).length + (Nat.bits b).length) + 10,
      (addTo src dst).Exec s (Function.update (Function.update (Function.update s .lz
        (lzF (Nat.bits b) (s .lz))) src r) dst (enc (Nat.bits (a + b)))) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_addLoop src dst hsd hs1 hs2 hs3 hd1 hd2 hd3 r hr _
    (Nat.bits a) (Nat.bits b) false s le_rfl hd hs (by rw [hcar]; rfl) hlz
  obtain ⟨n2, hn2, e2⟩ := exec_transfer .tmp (fun k => decide (k = dst)) _
    (addPost src dst (Nat.bits a) (Nat.bits b) false r s) rfl
  refine ⟨n1 + 1 + n2, ?_, ?_⟩
  · have hl := length_addB_le (Nat.bits a) (Nat.bits b) false
    simp only [addPost, if_neg hd1.symm, if_neg hs1.symm, if_true, htmp, List.append_nil,
      List.length_reverse, enc, List.length_map] at hn2
    simp only [Bool.toNat_false, add_zero] at hn1
    omega
  · have hadd : addB (Nat.bits a) (Nat.bits b) false = Nat.bits (a + b) := (bits_add a b).symm
    have : transferStore .tmp (fun k => decide (k = dst))
        (addPost src dst (Nat.bits a) (Nat.bits b) false r s) =
        Function.update (Function.update (Function.update s .lz
          (lzF (Nat.bits b) (s .lz))) src r) dst (enc (Nat.bits (a + b))) := by
      funext k
      by_cases k1 : k = dst
      · subst k1; simp [transferStore, addPost, hd1, hadd, hd1.symm, hsd.symm, htmp, hs1.symm]
      by_cases k2 : k = src
      · subst k2; simp [transferStore, addPost, k1, hs1]
      by_cases k3 : k = .tmp
      · subst k3; simp [transferStore, addPost, htmp, Ne.symm hs1, Ne.symm hd1]
      by_cases k4 : k = .car
      · subst k4; simp [transferStore, addPost, hcar, k1, k2]
      by_cases k5 : k = .lz
      · subst k5; simp [transferStore, addPost, k1, k2]
      · simp [transferStore, addPost, k1, k2, k3, k4, k5]
    rw [← this]
    exact StackProg.Exec.seq e1 e2

lemma lzOk_lzF (y : List Bool) {z : List BSym} (hz : LzOk z) : LzOk (lzF y z) :=
  lzF_cases y z hz

/-! ## Emitting one value -/

def emitP : StackProg Key BSym :=
  .seq (revTo .V .PB) (.seq (pushProg .PB .sep) (.seq (copyProg .R .C .sc) (.seq (addTo .C .Ac)
    (.seq (addTo .V .R) (.seq (pushProg .C .one) (addTo .C .Kb))))))

lemma exec_emit (v r a kk : ℕ) (s : Store) (hV : s .V = enc (Nat.bits v))
    (hR : s .R = enc (Nat.bits r)) (hA : s .Ac = enc (Nat.bits a))
    (hK : s .Kb = enc (Nat.bits kk)) (hC : s .C = []) (hsc : s .sc = []) (htmp : s .tmp = [])
    (hcar : s .car = []) (hlz : LzOk (s .lz)) :
    ∃ t n, n ≤ 20 * ((Nat.bits v).length + (Nat.bits r).length + (Nat.bits a).length +
        (Nat.bits kk).length) + 80 ∧ emitP.Exec s t n ∧
      t .PB = (encNat v).reverse ++ s .PB ∧ t .R = enc (Nat.bits (r + v)) ∧
      t .Ac = enc (Nat.bits (a + r)) ∧ t .Kb = enc (Nat.bits (kk + 1)) ∧ t .V = [] ∧
      LzOk (t .lz) ∧
      ∀ k, k ≠ .PB → k ≠ .R → k ≠ .Ac → k ≠ .Kb → k ≠ .V → k ≠ .lz → t k = s k := by
  obtain ⟨n1, hn1, e1⟩ := exec_revTo .V .PB (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .PB ((s .V).reverse ++ s .PB) with hs1
  have e2 := exec_push .PB .sep s1
  set s2 := Function.update s1 .PB (.sep :: s1 .PB) with hs2
  obtain ⟨n3, hn3, e3⟩ := exec_copy .R .C .sc (by decide) (by decide) (by decide) s2
    (by simp [hs2, hs1, hsc])
  set s3 := Function.update s2 .C (s2 .R ++ s2 .C) with hs3
  obtain ⟨n4, hn4, e4⟩ := exec_addTo .C .Ac (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a r [] (by rfl) s3 (by simp [hs3, hs2, hs1, hA])
    (by simp [hs3, hs2, hs1, hR, hC]) (by simp [hs3, hs2, hs1, htmp])
    (by simp [hs3, hs2, hs1, hcar]) (by simpa [hs3, hs2, hs1] using hlz)
  set s4 := Function.update (Function.update (Function.update s3 .lz
    (lzF (Nat.bits r) (s3 .lz))) .C []) .Ac (enc (Nat.bits (a + r))) with hs4
  obtain ⟨n5, hn5, e5⟩ := exec_addTo .V .R (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) r v [] (by rfl) s4 (by simp [hs4, hs3, hs2, hs1, hR])
    (by simp [hs4, hs3, hs2, hs1, hV]) (by simp [hs4, hs3, hs2, hs1, htmp])
    (by simp [hs4, hs3, hs2, hs1, hcar])
    (by simp only [hs4, hs3, hs2, hs1]; simp; exact lzOk_lzF _ (by simpa using hlz))
  set s5 := Function.update (Function.update (Function.update s4 .lz
    (lzF (Nat.bits v) (s4 .lz))) .V []) .R (enc (Nat.bits (r + v))) with hs5
  have e6 := exec_push .C .one s5
  set s6 := Function.update s5 .C (.one :: s5 .C) with hs6
  obtain ⟨n7, hn7, e7⟩ := exec_addTo .C .Kb (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) kk 1 [] (by rfl) s6
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hK])
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, bits_one, enc, toB])
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, htmp])
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hcar])
    (by simp only [hs6, hs5, hs4, hs3, hs2, hs1]; simp
        exact lzOk_lzF _ (lzOk_lzF _ (by simpa using hlz)))
  set s7 := Function.update (Function.update (Function.update s6 .lz
    (lzF (Nat.bits 1) (s6 .lz))) .C []) .Kb (enc (Nat.bits (kk + 1))) with hs7
  refine ⟨s7, n1 + 1 + (1 + 1 + (n3 + 1 + (n4 + 1 + (n5 + 1 + (1 + 1 + n7))))), ?_,
    StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 (StackProg.Exec.seq e4
      (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 e7))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hV, enc, List.length_map] at hn1
    simp only [hs2, hs1, hR, enc, List.length_map, Function.update_apply] at hn3
    simp only [bits_one, List.length_cons, List.length_nil] at hn7
    simp at hn3
    omega
  · simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hV, encNat_eq]
  · simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  · simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  · simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  · simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  · simp only [hs7, hs6, hs5, hs4, hs3, hs2, hs1]; simp
    exact lzOk_lzF _ (lzOk_lzF _ (lzOk_lzF _ (by simpa using hlz)))
  · intro k k1 k2 k3 k4 k5 k6
    by_cases k7 : k = .C
    · subst k7; simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hC]
    · simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, k1, k2, k3, k4, k5, k6, k7]

lemma bits_len_mono {u M : ℕ} (h : u ≤ M) : (Nat.bits u).length ≤ (Nat.bits M).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

lemma encNats_app (a b : List ℕ) : encNats (a ++ b) = encNats a ++ encNats b := by
  simp [encNats]

/-! ## The main loop over the sizes -/

def nzP : StackProg Key BSym :=
  .seq (copyProg .Bc .V .sc) (.seq emitP (.seq (copyProg .Bc .V .sc) (.seq (addTo .orig .V)
    (.seq (popProg .orig) (.seq emitP (.seq (copyProg .acc .C .sc) (addTo .C .Bc)))))))

def loopBody : StackProg Key BSym :=
  .branch (fun h => decide (h .orig = some .sep)) (popProg .orig) nzP

def mainLoop : StackProg Key BSym := .loop (fun h => (h .orig).isSome) loopBody

def LoopInv (Z : ℕ) (s : Store) (r : List ℕ) (c : ℕ) (vs : List ℕ) : Prop :=
  s .orig = encNats r ∧ s .Bc = enc (Nat.bits (c * Z)) ∧ s .acc = enc (Nat.bits Z) ∧
  s .PB = (encNats vs).reverse ∧ s .R = enc (Nat.bits (wa vs).2) ∧
  s .Ac = enc (Nat.bits (wa vs).1) ∧ s .Kb = enc (Nat.bits vs.length) ∧ s .V = [] ∧
  s .C = [] ∧ s .sc = [] ∧ s .tmp = [] ∧ s .car = [] ∧ LzOk (s .lz)

lemma exec_nz (Z G x : ℕ) (xs : List ℕ) (c : ℕ) (vs : List ℕ) (s : Store) (hx : x ≠ 0)
    (hI : LoopInv Z s (x :: xs) c vs)
    (hG1 : (Nat.bits ((c + 1) * Z)).length ≤ G) (hG2 : (Nat.bits (c * Z + x)).length ≤ G)
    (hG3 : (Nat.bits (wa (vs ++ [c * Z, c * Z + x])).1).length ≤ G)
    (hG4 : (Nat.bits (wa (vs ++ [c * Z, c * Z + x])).2).length ≤ G)
    (hG5 : (Nat.bits (vs.length + 2)).length ≤ G) :
    ∃ t n, n ≤ 200 * G + 6 * (Nat.bits x).length + 200 ∧ nzP.Exec s t n ∧
      LoopInv Z t xs (c + 1) (vs ++ [c * Z, c * Z + x]) ∧
      ∀ k, k ≠ .orig → k ≠ .Bc → k ≠ .PB → k ≠ .R → k ≠ .Ac → k ≠ .Kb → k ≠ .lz → t k = s k := by
  obtain ⟨hO, hB, hacc, hPB, hR, hA, hK, hV, hC, hsc, htmp, hcar, hlz⟩ := hI
  -- monotone facts for the bounds
  have hZc : c * Z ≤ (c + 1) * Z := Nat.mul_le_mul_right _ (by omega)
  have hZ1 : Z ≤ (c + 1) * Z := by nlinarith
  have w1 := wa_snoc vs (c * Z)
  have w2 := wa_snoc (vs ++ [c * Z]) (c * Z + x)
  rw [List.append_assoc, List.singleton_append] at w2
  simp only [stp] at w1 w2
  rw [w2, w1] at hG3 hG4
  simp only at hG3 hG4
  -- step 1: V := c Z
  obtain ⟨n1, hn1, e1⟩ := exec_copy .Bc .V .sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .V (s .Bc ++ s .V) with hs1
  obtain ⟨t2, n2, hn2, e2, p2PB, p2R, p2A, p2K, p2V, p2lz, f2⟩ :=
    exec_emit (c * Z) (wa vs).2 (wa vs).1 vs.length s1 (by simp [hs1, hB, hV])
      (by simp [hs1, hR]) (by simp [hs1, hA]) (by simp [hs1, hK]) (by simp [hs1, hC])
      (by simp [hs1, hsc]) (by simp [hs1, htmp]) (by simp [hs1, hcar]) (by simpa [hs1] using hlz)
  have g2 : ∀ k, k ≠ .PB → k ≠ .R → k ≠ .Ac → k ≠ .Kb → k ≠ .V → k ≠ .lz → t2 k = s k := by
    intro k a1 a2 a3 a4 a5 a6; rw [f2 k a1 a2 a3 a4 a5 a6]; simp [hs1, a5]
  obtain ⟨n3, hn3, e3⟩ := exec_copy .Bc .V .sc (by decide) (by decide) (by decide) t2
    (by rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsc])
  set s3 := Function.update t2 .V (t2 .Bc ++ t2 .V) with hs3
  have hO' : s .orig = enc (Nat.bits x) ++ BSym.sep :: encNats xs := by
    rw [hO, encNats_cons']
  obtain ⟨n4, hn4, e4⟩ := exec_addTo .orig .V (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (c * Z) x (BSym.sep :: encNats xs) (by rfl) s3
    (by simp [hs3, p2V]; rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hB])
    (by simp [hs3]; rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hO'])
    (by simp [hs3]; rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), htmp])
    (by simp [hs3]; rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hcar])
    (by simpa [hs3] using p2lz)
  set s4 := Function.update (Function.update (Function.update s3 .lz
    (lzF (Nat.bits x) (s3 .lz))) .orig (BSym.sep :: encNats xs)) .V
      (enc (Nat.bits (c * Z + x))) with hs4
  have e5 := exec_pop .orig s4
  set s5 := Function.update s4 .orig (s4 .orig).tail with hs5
  have q5 : ∀ k, k ≠ .orig → k ≠ .V → k ≠ .lz → s5 k = t2 k := by
    intro k a1 a2 a3; simp [hs5, hs4, hs3, a1, a2, a3]
  obtain ⟨t6, n6, hn6, e6, p6PB, p6R, p6A, p6K, p6V, p6lz, f6⟩ :=
    exec_emit (c * Z + x) ((wa vs).2 + c * Z) ((wa vs).1 + (wa vs).2) (vs.length + 1) s5
      (by simp [hs5, hs4]) (by rw [q5 _ (by decide) (by decide) (by decide), p2R])
      (by rw [q5 _ (by decide) (by decide) (by decide), p2A])
      (by rw [q5 _ (by decide) (by decide) (by decide), p2K])
      (by rw [q5 _ (by decide) (by decide) (by decide),
            g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hC])
      (by rw [q5 _ (by decide) (by decide) (by decide),
            g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsc])
      (by rw [q5 _ (by decide) (by decide) (by decide),
            g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), htmp])
      (by rw [q5 _ (by decide) (by decide) (by decide),
            g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcar])
      (by simp only [hs5, hs4]; simp; exact lzOk_lzF _ (by simpa [hs3] using p2lz))
  have g6 : ∀ k, k ≠ .orig → k ≠ .PB → k ≠ .R → k ≠ .Ac → k ≠ .Kb → k ≠ .V → k ≠ .lz →
      t6 k = s k := by
    intro k a0 a1 a2 a3 a4 a5 a6
    rw [f6 k a1 a2 a3 a4 a5 a6, q5 k a0 a5 a6, g2 k a1 a2 a3 a4 a5 a6]
  obtain ⟨n7, hn7, e7⟩ := exec_copy .acc .C .sc (by decide) (by decide) (by decide) t6
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hsc])
  set s7 := Function.update t6 .C (t6 .acc ++ t6 .C) with hs7
  have q7 : ∀ k, k ≠ .C → s7 k = t6 k := by intro k a; simp [hs7, a]
  obtain ⟨n8, hn8, e8⟩ := exec_addTo .C .Bc (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (c * Z) Z [] (by rfl) s7
    (by rw [q7 _ (by decide), g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hB])
    (by simp only [hs7, Function.update_self]
        rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hacc, hC])
    (by rw [q7 _ (by decide), g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), htmp])
    (by rw [q7 _ (by decide), g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hcar])
    (by rw [q7 _ (by decide)]; exact p6lz)
  set s8 := Function.update (Function.update (Function.update s7 .lz
    (lzF (Nat.bits Z) (s7 .lz))) .C []) .Bc (enc (Nat.bits (c * Z + Z))) with hs8
  refine ⟨s8, n1 + 1 + (n2 + 1 + (n3 + 1 + (n4 + 1 + (1 + 1 + (n6 + 1 + (n7 + 1 + n8)))))), ?_,
    StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 (StackProg.Exec.seq e4
      (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7 e8)))))), ?_, ?_⟩
  · -- the bound
    have b1 : (Nat.bits (c * Z)).length ≤ G := le_trans (bits_len_mono hZc) hG1
    have b2 : (Nat.bits Z).length ≤ G := le_trans (bits_len_mono hZ1) hG1
    have b3 : (Nat.bits (wa vs).2).length ≤ G := le_trans (bits_len_mono (by omega)) hG4
    have b4 : (Nat.bits (wa vs).1).length ≤ G := le_trans (bits_len_mono (by omega)) hG3
    have b5 : (Nat.bits vs.length).length ≤ G := le_trans (bits_len_mono (by omega)) hG5
    have b6 : (Nat.bits ((wa vs).2 + c * Z)).length ≤ G := le_trans (bits_len_mono (by omega)) hG4
    have b7 : (Nat.bits ((wa vs).1 + (wa vs).2)).length ≤ G :=
      le_trans (bits_len_mono (by omega)) hG3
    have b8 : (Nat.bits (vs.length + 1)).length ≤ G := le_trans (bits_len_mono (by omega)) hG5
    have l3 : (t2 .Bc).length ≤ G := by
      rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hB]
      simpa [enc] using b1
    have l7 : (t6 .acc).length ≤ G := by
      rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hacc]
      simpa [enc] using b2
    simp only [hB, enc, List.length_map] at hn1
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hs8, hs7, hs5, hs4, hs3]; rw [f6 _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; simp [hs5, hs4]
    · simp [hs8]; congr 2; ring
    · simp [hs8, hs7]; rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hacc]
    · simp [hs8, hs7, p6PB]; rw [q5 _ (by decide) (by decide) (by decide), p2PB]
      simp [hs1, hPB, encNats_app, encNats]
    · simp [hs8, hs7, p6R, w2, w1]
    · simp [hs8, hs7, p6A, w2, w1]
    · simp [hs8, hs7, p6K]
    · simp [hs8, hs7, p6V]
    · simp [hs8]
    · simp [hs8, hs7]; rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hsc]
    · simp [hs8, hs7]; rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), htmp]
    · simp [hs8, hs7]; rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hcar]
    · simp [hs8, hs7]; exact lzOk_lzF _ p6lz
  · intro k a1 a2 a3 a4 a5 a6 a7
    by_cases a8 : k = .C
    · subst a8; simp [hs8, hC]
    by_cases a9 : k = .V
    · subst a9; simp [hs8, hs7, p6V, hV]
    · simp [hs8, hs7, a1, a2, a3, a4, a5, a6, a7, a8, a9]
      exact g6 k a1 a3 a4 a5 a6 a9 a7

lemma foldl_stp_mono : ∀ (m : List ℕ) (p : ℕ × ℕ), p.1 ≤ (m.foldl stp p).1 ∧ p.2 ≤ (m.foldl stp p).2 := by
  intro m
  induction m with
  | nil => intro p; simp
  | cons v m ih =>
    intro p
    have := ih (stp p v)
    simp only [List.foldl_cons]
    exact ⟨le_trans (by simp [stp]) this.1, le_trans (by simp [stp]) this.2⟩

lemma wa_mono (l m : List ℕ) : (wa l).1 ≤ (wa (l ++ m)).1 ∧ (wa l).2 ≤ (wa (l ++ m)).2 := by
  unfold wa; rw [List.foldl_append]; exact foldl_stp_mono m _

lemma le_wa2 {v : ℕ} {l : List ℕ} (h : v ∈ l) : v ≤ (wa l).2 := by
  rw [wa_eq]; exact List.le_sum_of_mem h

lemma len_encNats_cons (x : ℕ) (xs : List ℕ) :
    (encNats (x :: xs)).length = (Nat.bits x).length + 1 + (encNats xs).length := by
  rw [encNats_cons']; simp [enc]; omega

lemma exec_loop (Z G M : ℕ) (hM : (Nat.bits M).length ≤ G) :
    ∀ (r : List ℕ) (c : ℕ) (vs : List ℕ) (s : Store), LoopInv Z s r c vs →
      (c + r.length + 1) * Z ≤ M → (wa (vs ++ go Z c r)).1 ≤ M →
      (wa (vs ++ go Z c r)).2 ≤ M → (vs ++ go Z c r).length + 2 ≤ M →
      ∃ t n c', n ≤ (encNats r).length * (200 * G + 400) + 1 ∧ mainLoop.Exec s t n ∧
        LoopInv Z t [] c' (vs ++ go Z c r) ∧
        ∀ k, k ≠ .orig → k ≠ .Bc → k ≠ .PB → k ≠ .R → k ≠ .Ac → k ≠ .Kb → k ≠ .lz →
          t k = s k := by
  intro r
  induction r with
  | nil =>
    intro c vs s hI _ _ _ _
    refine ⟨s, 1, c, by simp, StackProg.Exec.loopFalse ?_, by simpa [go] using hI,
      fun _ _ _ _ _ _ _ _ => rfl⟩
    simp [hI.1, encNats]
  | cons x xs ih =>
    intro c vs s hI h1 h2 h3 h4
    have hlen := len_encNats_cons x xs
    have htest : (fun h : Key → Option BSym => (h .orig).isSome) (fun k => (s k).head?) = true := by
      simp [hI.1, encNats_cons']
    by_cases hx : x = 0
    · subst hx
      have hO : s .orig = BSym.sep :: encNats xs := by rw [hI.1, encNats_cons']; simp [enc]
      have e1 := exec_pop .orig s
      set s1 := Function.update s .orig (s .orig).tail with hs1
      have hI1 : LoopInv Z s1 xs c vs := by
        obtain ⟨_, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hI
        refine ⟨by simp [hs1, hO], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simpa [hs1] using by assumption
      have hgo : go Z c (0 :: xs) = go Z c xs := by simp [go]
      rw [hgo] at h2 h3 h4
      obtain ⟨t, m, c', hm, em, hIt, ft⟩ := ih c vs s1 hI1 (by
        have : (c + xs.length + 1) * Z ≤ (c + (0 :: xs).length + 1) * Z :=
          Nat.mul_le_mul_right _ (by simp)
        omega) h2 h3 h4
      refine ⟨t, 1 + (1 + 1) + 1 + m, c', ?_, StackProg.Exec.loopTrue htest
        (StackProg.Exec.branchTrue (by simp [hO]) e1) em, by rw [hgo]; exact hIt, ?_⟩
      · rw [hlen]
        have : (encNats xs).length * (200 * G + 400) + 200 * G + 400 =
          ((encNats xs).length + 1) * (200 * G + 400) := by ring
        have : ((Nat.bits 0).length + 1 + (encNats xs).length) * (200 * G + 400) =
          ((encNats xs).length + 1) * (200 * G + 400) := by simp <;> ring
        omega
      · intro k a1 a2 a3 a4 a5 a6 a7
        rw [ft k a1 a2 a3 a4 a5 a6 a7]; simp [hs1, a1]
    · have hgo : vs ++ go Z c (x :: xs) = (vs ++ [c * Z, c * Z + x]) ++ go Z (c + 1) xs := by
        simp [go, hx]
      rw [hgo] at h2 h3 h4
      have mono := wa_mono (vs ++ [c * Z, c * Z + x]) (go Z (c + 1) xs)
      have hmem : c * Z + x ∈ (vs ++ [c * Z, c * Z + x]) ++ go Z (c + 1) xs := by simp
      have hv := le_wa2 hmem
      have hc1 : (c + 1) * Z ≤ M := by
        have : (c + 1) * Z ≤ (c + (x :: xs).length + 1) * Z := Nat.mul_le_mul_right _ (by simp)
        omega
      obtain ⟨t1, n1, hn1, e1, hI1, f1⟩ := exec_nz Z G x xs c vs s hx hI
        (le_trans (bits_len_mono hc1) hM) (le_trans (bits_len_mono (by omega)) hM)
        (le_trans (bits_len_mono (by omega)) hM) (le_trans (bits_len_mono (by omega)) hM)
        (le_trans (bits_len_mono (by simp at h4 ⊢; omega)) hM)
      obtain ⟨t, m, c', hm, em, hIt, ft⟩ := ih (c + 1) (vs ++ [c * Z, c * Z + x]) t1 hI1 (by
        have : (c + 1 + xs.length + 1) * Z = (c + (x :: xs).length + 1) * Z := by
          simp only [List.length_cons]; ring
        omega) h2 h3 h4
      have hbr : (fun h : Key → Option BSym => decide (h .orig = some .sep))
          (fun k => (s k).head?) = false := by
        simp only [hI.1, encNats_cons', decide_eq_false_iff_not]
        cases h : Nat.bits x with
        | nil => exact absurd (by have := (canon_bits_bval x).2; rw [h] at this; simpa [bval] using this.symm) hx
        | cons b l => cases b <;> simp [enc, toB]
      refine ⟨t, 1 + (1 + n1) + 1 + m, c', ?_, StackProg.Exec.loopTrue htest
        (StackProg.Exec.branchFalse hbr e1) em, by rw [hgo]; exact hIt, ?_⟩
      · rw [hlen]
        have : ((Nat.bits x).length + 1 + (encNats xs).length) * (200 * G + 400) =
          (Nat.bits x).length * (200 * G + 400) + 200 * G + 400 +
            (encNats xs).length * (200 * G + 400) := by ring
        have : 6 * (Nat.bits x).length ≤ (Nat.bits x).length * (200 * G + 400) := by
          calc 6 * (Nat.bits x).length = (Nat.bits x).length * 6 := by ring
            _ ≤ (Nat.bits x).length * (200 * G + 400) := Nat.mul_le_mul_left _ (by omega)
        omega
      · intro k a1 a2 a3 a4 a5 a6 a7
        rw [ft k a1 a2 a3 a4 a5 a6 a7, f1 k a1 a2 a3 a4 a5 a6 a7]

end TT92


set_option autoImplicit false

namespace TT92

open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal

/-! ## Injectivity of the codes -/

lemma sep_split_inj : ∀ {u u' R R' : List BSym}, BSym.sep ∉ u → BSym.sep ∉ u' →
    u ++ BSym.sep :: R = u' ++ BSym.sep :: R' → u = u' ∧ R = R' := by
  intro u
  induction u with
  | nil =>
    intro u' R R' _ h2 h
    rcases u' with _ | ⟨b, u'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h2
  | cons a u ih =>
    intro u' R R' h1 h2 h
    rcases u' with _ | ⟨b, u'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h1
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨e1, e2⟩ := ih (fun hh => h1 (List.mem_cons_of_mem _ hh))
        (fun hh => h2 (List.mem_cons_of_mem _ hh)) h.2
      exact ⟨by rw [h.1, e1], e2⟩

lemma sep_not_mem_enc (x : List Bool) : BSym.sep ∉ enc x := by
  simp only [enc, List.mem_map, not_exists, not_and]
  intro b _ h; cases b <;> simp [toB] at h

lemma enc_inj {x y : List Bool} (h : enc x = enc y) : x = y := by
  apply List.map_injective_iff.2 _ h
  intro a b hab; cases a <;> cases b <;> simp_all [toB]

lemma encNats_cons (k : ℕ) (l : List ℕ) :
    encNats (k :: l) = enc (Nat.bits k) ++ BSym.sep :: encNats l := by
  simp [encNats, encNat_eq]

lemma encNats_append (a b : List ℕ) : encNats (a ++ b) = encNats a ++ encNats b := by
  simp [encNats]

lemma encNats_inj : ∀ {a b : List ℕ}, encNats a = encNats b → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    rcases b with _ | ⟨k, b⟩
    · rfl
    · rw [encNats_cons] at h; simp [encNats] at h
  | cons k a ih =>
    intro b h
    rcases b with _ | ⟨k', b⟩
    · rw [encNats_cons] at h; simp [encNats] at h
    · rw [encNats_cons, encNats_cons] at h
      obtain ⟨e1, e2⟩ := sep_split_inj (sep_not_mem_enc _) (sep_not_mem_enc _) h
      have hk : k = k' := by
        have := congrArg bval (enc_inj e1)
        rwa [(canon_bits_bval k).2, (canon_bits_bval k').2] at this
      rw [hk, ih e2]

lemma codeList_inj {I J : Instance} {a b c d : ℕ} (h : I.codeList a b = J.codeList c d) :
    I = J ∧ a = c ∧ b = d := by
  obtain ⟨nA, nB, pA, pB⟩ := I
  obtain ⟨nA', nB', pA', pB'⟩ := J
  simp only [Instance.codeList, List.cons_append, List.nil_append, List.append_assoc,
    List.cons.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h3, h4⟩ := List.append_inj h2 (by simp)
  have e1 := List.ofFn_injective h1
  have e2 := List.ofFn_injective h3
  subst e1 e2
  simp only [List.cons.injEq, and_true] at h4
  exact ⟨rfl, h4.1, h4.2⟩

/-! ## The reduction function -/

/-- the constructed distinct sizes -/
def vals (sl : List ℕ) : List ℕ := go (sl.sum + 1) 1 sl

def Qv (l : List ℕ) : ℕ := l.sum + l.sum / 2 + (wa l).1 + (wa l).1

def codeOf (sl : List ℕ) : List ℕ :=
  [(vals sl).length, (vals sl).length] ++ vals sl ++ vals sl ++ [Qv (vals sl), Qv (vals sl)]

open Classical in
noncomputable def F (w : List BSym) : List BSym :=
  if h : ∃ sl, w = encNats sl then encNats (codeOf h.choose) else []

lemma F_valid (sl : List ℕ) : F (encNats sl) = encNats (codeOf sl) := by
  have h : ∃ s, encNats sl = encNats s := ⟨sl, rfl⟩
  rw [F, dif_pos h, show h.choose = sl from (encNats_inj h.choose_spec).symm]

lemma F_invalid {w : List BSym} (hw : ¬ ∃ sl, w = encNats sl) : F w = [] := by
  rw [F, dif_neg hw]

lemma codeOf_eq (sl : List ℕ) :
    codeOf sl = (construction (vals sl).get).codeList (Qv (vals sl)) (Qv (vals sl)) := by
  simp [codeOf, Instance.codeList, construction]

lemma meets_mono (I : Instance) {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') {l : List _}
    (h : I.Meets a b l) : I.Meets a' b' l :=
  ⟨h.1, le_trans h.2.1 ha, le_trans h.2.2 hb⟩

lemma thresholdQ_eq {k : ℕ} (p : Fin k → ℕ) : thresholdQ p = (bigT p : ℝ) / 2 := by
  unfold thresholdQ bigT; push_cast; ring

lemma even_of_partitionYes {s : List ℕ} (h : PartitionYes s) : Even s.sum := by
  obtain ⟨a, -, h2⟩ := (partitionYes_iff s).1 h
  exact ⟨a, by omega⟩

lemma vals_sorted (sl : List ℕ) : StrictMono (vals sl).get := by
  rw [← List.sortedLT_iff_strictMono_get]
  apply List.Pairwise.sortedLT
  apply go_sorted
  intro x hx
  have := List.le_sum_of_mem hx
  omega

lemma partition_vals (sl : List ℕ) : PartitionYes sl ↔ PartitionYes (vals sl) :=
  partition_go _ sl 1 (by omega)

theorem recYes_iff (l : List ℕ) (hl : StrictMono l.get) :
    (construction l.get).RecYes (thresholdQ l.get) (thresholdQ l.get) ↔
      (construction l.get).RecYes (Qv l : ℝ) (Qv l : ℝ) := by
  have hq : thresholdQ l.get = (3 / 2 : ℝ) * (l.sum : ℝ) + 2 * ((wa l).1 : ℝ) := by
    unfold thresholdQ; rw [bigP_eq, weightedSum_eq, wa_eq]
  rcases Nat.even_or_odd l.sum with he | ho
  · have : (Qv l : ℝ) = thresholdQ l.get := by
      rw [hq]; unfold Qv
      obtain ⟨r, hr⟩ := he
      rw [hr, show (r + r) / 2 = r by omega]; push_cast; ring
    rw [this]
  · have hlt : (Qv l : ℝ) ≤ thresholdQ l.get := by
      rw [hq]; unfold Qv
      obtain ⟨r, hr⟩ := ho
      rw [hr, show (2 * r + 1) / 2 = r by omega]; push_cast; linarith
    have hno : ¬ (construction l.get).RecYes (thresholdQ l.get) (thresholdQ l.get) := by
      intro h
      rw [thresholdQ_eq, ← theorem_9_2_equivalence _ hl, List.ofFn_get] at h
      have := even_of_partitionYes h
      exact (Nat.not_even_iff_odd.2 ho) this
    constructor
    · intro h; exact absurd h hno
    · rintro ⟨l', hl'⟩; exact absurd ⟨l', meets_mono _ hlt hlt hl'⟩ hno

theorem F_correct (x : List BSym) :
    ∃ (k : ℕ) (p : Fin k → ℕ), StrictMono p ∧
      (x ∈ partitionLang ↔ PartitionYes (List.ofFn p)) ∧
      ((construction p).RecYes (thresholdQ p) (thresholdQ p) ↔ F x ∈ targetLang) := by
  by_cases hw : ∃ sl, x = encNats sl
  · obtain ⟨sl, rfl⟩ := hw
    refine ⟨_, (vals sl).get, vals_sorted sl, ?_, ?_⟩
    · rw [List.ofFn_get, ← partition_vals]
      constructor
      · rintro ⟨s, hs, he⟩; rwa [encNats_inj he]
      · intro h; exact ⟨sl, h, rfl⟩
    · rw [recYes_iff _ (vals_sorted sl), F_valid]
      constructor
      · intro h; exact ⟨_, _, _, h, by rw [codeOf_eq]⟩
      · rintro ⟨I, QA, QB, hI, he⟩
        rw [codeOf_eq] at he
        obtain ⟨rfl, rfl, rfl⟩ := codeList_inj (encNats_inj he)
        exact hI
  · refine ⟨1, fun _ => 1, fun a b h => absurd h (by omega), ?_, ?_⟩
    · have hno : ¬ PartitionYes (List.ofFn (fun _ : Fin 1 => 1)) := by
        intro h; have := even_of_partitionYes h; simp at this
      constructor
      · rintro ⟨s, -, hs⟩; exact absurd ⟨s, hs⟩ hw
      · intro h; exact absurd h hno
    · rw [F_invalid hw]
      have hsm : StrictMono (fun _ : Fin 1 => (1 : ℕ)) := fun a b h => absurd h (by omega)
      constructor
      · intro h
        rw [thresholdQ_eq, ← theorem_9_2_equivalence _ hsm] at h
        have := even_of_partitionYes h; simp at this
      · rintro ⟨I, QA, QB, -, he⟩
        have : encNats (I.codeList QA QB) ≠ [] := by
          simp [Instance.codeList, encNats_append, encNats_cons]
        exact absurd he.symm this

end TT92


set_option autoImplicit false

namespace TT92

open CookPvsNP ProjSchedTW.Complexity

/-! ## Computing `Q` and writing the output -/

def qP : StackProg Key BSym :=
  .seq (copyProg .R .Q .sc) (.seq (copyProg .R .C .sc) (.seq (popProg .C) (.seq (addTo .C .Q)
    (.seq (copyProg .Ac .C .sc) (.seq (addTo .C .Q) (.seq (copyProg .Ac .C .sc) (addTo .C .Q)))))))

def outP : StackProg Key BSym :=
  .seq (pushProg .out .sep) (.seq (copyProg .Q .out .sc) (.seq (pushProg .out .sep)
    (.seq (copyProg .Q .out .sc)
    (.seq (transferProg .PB (fun k => decide (k = .out ∨ k = .sc)))
    (.seq (transferProg .sc (fun k => decide (k = .PB)))
    (.seq (transferProg .PB (fun k => decide (k = .out)))
    (.seq (pushProg .out .sep) (.seq (copyProg .Kb .out .sc) (.seq (pushProg .out .sep)
      (copyProg .Kb .out .sc))))))))))

lemma exec_qP (P W G : ℕ) (s : Store) (hR : s .R = enc (Nat.bits P))
    (hA : s .Ac = enc (Nat.bits W)) (hQ : s .Q = []) (hC : s .C = []) (hsc : s .sc = [])
    (htmp : s .tmp = []) (hcar : s .car = []) (hlz : LzOk (s .lz))
    (hG : (Nat.bits (P + P / 2 + W + W)).length ≤ G) :
    ∃ t n, n ≤ 100 * G + 100 ∧ qP.Exec s t n ∧ t .Q = enc (Nat.bits (P + P / 2 + W + W)) ∧
      t .C = [] ∧ t .sc = [] ∧ t .tmp = [] ∧ t .car = [] ∧
      ∀ k, k ≠ .Q → k ≠ .C → k ≠ .lz → t k = s k := by
  have bP : (Nat.bits P).length ≤ G := le_trans (bits_len_mono (by omega)) hG
  have bP2 : (Nat.bits (P / 2)).length ≤ G := le_trans (bits_len_mono (by omega)) hG
  have bW : (Nat.bits W).length ≤ G := le_trans (bits_len_mono (by omega)) hG
  have b1 : (Nat.bits (P + P / 2)).length ≤ G := le_trans (bits_len_mono (by omega)) hG
  have b2 : (Nat.bits (P + P / 2 + W)).length ≤ G := le_trans (bits_len_mono (by omega)) hG
  obtain ⟨n1, hn1, e1⟩ := exec_copy .R .Q .sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .Q (s .R ++ s .Q) with hs1
  obtain ⟨n2, hn2, e2⟩ := exec_copy .R .C .sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 .C (s1 .R ++ s1 .C) with hs2
  have e3 := exec_pop .C s2
  set s3 := Function.update s2 .C (s2 .C).tail with hs3
  have hdiv : (enc (Nat.bits P)).tail = enc (Nat.bits (P / 2)) := by
    rw [bits_div_two]; simp [enc, List.map_tail]
  obtain ⟨n4, hn4, e4⟩ := exec_addTo .C .Q (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) P (P / 2) [] (by rfl) s3 (by simp [hs3, hs2, hs1, hR, hQ])
    (by simp [hs3, hs2, hs1, hR, hC, hdiv]) (by simp [hs3, hs2, hs1, htmp])
    (by simp [hs3, hs2, hs1, hcar]) (by simpa [hs3, hs2, hs1] using hlz)
  set s4 := Function.update (Function.update (Function.update s3 .lz
    (lzF (Nat.bits (P / 2)) (s3 .lz))) .C []) .Q (enc (Nat.bits (P + P / 2))) with hs4
  obtain ⟨n5, hn5, e5⟩ := exec_copy .Ac .C .sc (by decide) (by decide) (by decide) s4
    (by simp [hs4, hs3, hs2, hs1, hsc])
  set s5 := Function.update s4 .C (s4 .Ac ++ s4 .C) with hs5
  obtain ⟨n6, hn6, e6⟩ := exec_addTo .C .Q (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (P + P / 2) W [] (by rfl) s5 (by simp [hs5, hs4])
    (by simp [hs5, hs4, hs3, hs2, hs1, hA]) (by simp [hs5, hs4, hs3, hs2, hs1, htmp])
    (by simp [hs5, hs4, hs3, hs2, hs1, hcar])
    (by simp only [hs5, hs4]; simp; exact lzOk_lzF _ (by simpa [hs3, hs2, hs1] using hlz))
  set s6 := Function.update (Function.update (Function.update s5 .lz
    (lzF (Nat.bits W) (s5 .lz))) .C []) .Q (enc (Nat.bits (P + P / 2 + W))) with hs6
  obtain ⟨n7, hn7, e7⟩ := exec_copy .Ac .C .sc (by decide) (by decide) (by decide) s6
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hsc])
  set s7 := Function.update s6 .C (s6 .Ac ++ s6 .C) with hs7
  obtain ⟨n8, hn8, e8⟩ := exec_addTo .C .Q (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (P + P / 2 + W) W [] (by rfl) s7 (by simp [hs7, hs6])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hA]) (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, htmp])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hcar])
    (by simp only [hs7, hs6, hs5, hs4]; simp
        exact lzOk_lzF _ (lzOk_lzF _ (by simpa [hs3, hs2, hs1] using hlz)))
  set s8 := Function.update (Function.update (Function.update s7 .lz
    (lzF (Nat.bits W) (s7 .lz))) .C []) .Q (enc (Nat.bits (P + P / 2 + W + W))) with hs8
  refine ⟨s8, n1 + 1 + (n2 + 1 + (1 + 1 + (n4 + 1 + (n5 + 1 + (n6 + 1 + (n7 + 1 + n8)))))), ?_,
    StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 (StackProg.Exec.seq e4
      (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7 e8)))))),
    by simp [hs8], by simp [hs8], ?_, ?_, ?_, ?_⟩
  · simp only [hs1, hs2, hs3, hs4, hs5, hs6, hR, hA, enc, List.length_map, Function.update_apply]
      at hn1 hn2 hn5 hn7
    simp [hA, enc] at hn1 hn2 hn5 hn7
    omega
  · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hsc]
  · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, htmp]
  · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hcar]
  · intro k a1 a2 a3
    simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, a1, a2, a3]

lemma exec_outP (q kk G : ℕ) (U : List ℕ) (s : Store) (hout : s .out = []) (hsc : s .sc = [])
    (hQ : s .Q = enc (Nat.bits q)) (hPB : s .PB = (encNats U).reverse)
    (hK : s .Kb = enc (Nat.bits kk)) (hGq : (Nat.bits q).length ≤ G)
    (hGk : (Nat.bits kk).length ≤ G) :
    ∃ t n, n ≤ 30 * G + 12 * (encNats U).length + 60 ∧ outP.Exec s t n ∧
      t .out = encNats ([kk, kk] ++ U ++ U ++ [q, q]) := by
  have o1 := exec_push .out .sep s
  set s1 := Function.update s .out (.sep :: s .out) with hs1
  obtain ⟨n2, hn2, o2⟩ := exec_copy .Q .out .sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 .out (s1 .Q ++ s1 .out) with hs2
  have o3 := exec_push .out .sep s2
  set s3 := Function.update s2 .out (.sep :: s2 .out) with hs3
  obtain ⟨n4, hn4, o4⟩ := exec_copy .Q .out .sc (by decide) (by decide) (by decide) s3
    (by simp [hs3, hs2, hs1, hsc])
  set s4 := Function.update s3 .out (s3 .Q ++ s3 .out) with hs4
  obtain ⟨n5, hn5, o5⟩ := exec_transfer .PB (fun k => decide (k = .out ∨ k = .sc)) _ s4 rfl
  set s5 := transferStore .PB (fun k => decide (k = .out ∨ k = .sc)) s4 with hs5
  obtain ⟨n6, hn6, o6⟩ := exec_transfer .sc (fun k => decide (k = .PB)) _ s5 rfl
  set s6 := transferStore .sc (fun k => decide (k = .PB)) s5 with hs6
  obtain ⟨n7, hn7, o7⟩ := exec_transfer .PB (fun k => decide (k = .out)) _ s6 rfl
  set s7 := transferStore .PB (fun k => decide (k = .out)) s6 with hs7
  have o8 := exec_push .out .sep s7
  set s8 := Function.update s7 .out (.sep :: s7 .out) with hs8
  have v8sc : s8 .sc = [] := by
    simp [hs8, hs7, hs6, transferStore]
  obtain ⟨n9, hn9, o9⟩ := exec_copy .Kb .out .sc (by decide) (by decide) (by decide) s8 v8sc
  set s9 := Function.update s8 .out (s8 .Kb ++ s8 .out) with hs9
  have o10 := exec_push .out .sep s9
  set s10 := Function.update s9 .out (.sep :: s9 .out) with hs10
  obtain ⟨n11, hn11, o11⟩ := exec_copy .Kb .out .sc (by decide) (by decide) (by decide) s10
    (by simp [hs10, hs9, v8sc])
  set s11 := Function.update s10 .out (s10 .Kb ++ s10 .out) with hs11
  have vK : s10 .Kb = enc (Nat.bits kk) := by
    simp [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, transferStore, hK]
  have v8K : s8 .Kb = enc (Nat.bits kk) := by
    simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, transferStore, hK]
  refine ⟨s11, 1 + 1 + (n2 + 1 + (1 + 1 + (n4 + 1 + (n5 + 1 + (n6 + 1 + (n7 + 1 + (1 + 1 +
    (n9 + 1 + (1 + 1 + n11))))))))), ?_, StackProg.Exec.seq o1 (StackProg.Exec.seq o2
    (StackProg.Exec.seq o3 (StackProg.Exec.seq o4 (StackProg.Exec.seq o5 (StackProg.Exec.seq o6
    (StackProg.Exec.seq o7 (StackProg.Exec.seq o8 (StackProg.Exec.seq o9
    (StackProg.Exec.seq o10 o11))))))))), ?_⟩
  · have l5 : (s4 .PB).length = (encNats U).length := by
      simp [hs4, hs3, hs2, hs1, hPB]
    have l6 : (s5 .sc).length = (encNats U).length := by
      simp [hs5, transferStore, hs4, hs3, hs2, hs1, hPB, hsc]
    have l7 : (s6 .PB).length = (encNats U).length := by
      simp [hs6, hs5, transferStore, hs4, hs3, hs2, hs1, hPB, hsc]
    rw [l5] at hn5; rw [l6] at hn6; rw [l7] at hn7
    simp only [hs1, hs2, hs3, Function.update_apply, hQ, enc, List.length_map] at hn2 hn4
    simp at hn2 hn4
    rw [v8K] at hn9; rw [vK] at hn11
    simp only [enc, List.length_map] at hn9 hn11
    omega
  · simp only [hs11, Function.update_self, vK]
    simp [hs10, hs9, v8K, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, transferStore, hQ, hPB,
      hout, hsc, encNats_app, encNats_cons, hK, encNats, encNat_eq]

/-! ## Size bounds -/

lemma go_length_le (Z : ℕ) : ∀ (l : List ℕ) (c : ℕ), (go Z c l).length ≤ 2 * l.length := by
  intro l
  induction l with
  | nil => intro c; simp [go]
  | cons x xs ih =>
    intro c
    by_cases hx : x = 0
    · simp only [go, hx, if_true]; have := ih c; simp; omega
    · simp only [go, hx, if_false]; have := ih (c + 1); simp; omega

lemma go_val_le (Z : ℕ) : ∀ (l : List ℕ) (c : ℕ), (∀ x ∈ l, x ≤ Z) →
    ∀ v ∈ go Z c l, v ≤ (c + l.length) * Z + Z := by
  intro l
  induction l with
  | nil => intro c _ v hv; simp [go] at hv
  | cons x xs ih =>
    intro c hl v hv
    have hxZ := hl x (by simp)
    have hrest : ∀ y ∈ xs, y ≤ Z := fun y hy => hl y (by simp [hy])
    have e1 : (c + (x :: xs).length) * Z + Z = (c + xs.length) * Z + Z + Z := by
      simp only [List.length_cons]; ring
    by_cases hx : x = 0
    · simp only [go, hx, if_true] at hv
      have := ih c hrest v hv; omega
    · simp only [go, hx, if_false, List.mem_cons] at hv
      have h2 : c * Z ≤ (c + xs.length) * Z := Nat.mul_le_mul_right _ (by omega)
      rcases hv with rfl | rfl | hv
      · omega
      · omega
      · have := ih (c + 1) hrest v hv
        have e2 : (c + 1 + xs.length) * Z + Z = (c + xs.length) * Z + Z + Z := by ring
        omega

lemma wa1_le (l : List ℕ) : (wa l).1 ≤ l.length * (wa l).2 := by
  induction l using List.reverseRec with
  | nil => simp [wa]
  | append_singleton l v ih =>
    rw [wa_snoc]; simp only [stp, List.length_append, List.length_singleton]
    nlinarith

lemma len_encNats_le (G : ℕ) : ∀ (l : List ℕ), (∀ v ∈ l, (Nat.bits v).length ≤ G) →
    (encNats l).length ≤ l.length * (G + 1) := by
  intro l
  induction l with
  | nil => intro _; simp [encNats]
  | cons x xs ih =>
    intro h
    rw [len_encNats_cons]
    have := ih (fun v hv => h v (by simp [hv]))
    have := h x (by simp)
    simp only [List.length_cons]; nlinarith

lemma len_bits_sum (sl : List ℕ) : ∀ a : ℕ,
    (Nat.bits (a + sl.sum)).length ≤ (Nat.bits a).length + (encNats sl).length := by
  induction sl with
  | nil => intro a; simp [encNats]
  | cons k sl ih =>
    intro a
    have h1 := ih (a + k)
    have h2 : (Nat.bits (a + k)).length ≤ (Nat.bits a).length + (Nat.bits k).length + 1 := by
      rw [bits_add]; exact length_addB_le _ _ _
    rw [encNats_cons']
    simp only [List.sum_cons, List.length_append, List.length_cons, enc, List.length_map] at h1 ⊢
    rw [← Nat.add_assoc]
    omega

lemma len_sl (sl : List ℕ) : sl.length ≤ (encNats sl).length := by
  induction sl with
  | nil => simp
  | cons k sl ih => rw [encNats_cons']; simp; omega

lemma lt_pow_of_bits {u t : ℕ} (h : (Nat.bits u).length ≤ t) : u < 2 ^ t := by
  rw [Nat.size_eq_bits_len] at h
  exact lt_of_lt_of_le (Nat.lt_size_self u) (Nat.pow_le_pow_right (by norm_num) h)

lemma bits_le_of_le_pow {u t : ℕ} (h : u ≤ 2 ^ t) : (Nat.bits u).length ≤ t + 1 := by
  have := bits_len_mono h
  rw [Nat.size_eq_bits_len (2 ^ t), Nat.size_pow] at this; exact this

/-- All numbers the machine handles on a valid input of length `L` are at most `32 * (2^L)^4`. -/
theorem numbers_le (sl : List ℕ) :
    let A := 2 ^ (encNats sl).length
    let U := vals sl
    (sl.length + 2) * (sl.sum + 1) ≤ 32 * A ^ 4 ∧ (wa U).1 ≤ 32 * A ^ 4 ∧
      (wa U).2 ≤ 32 * A ^ 4 ∧ U.length + 2 ≤ 32 * A ^ 4 ∧ Qv U ≤ 32 * A ^ 4 ∧
      sl.sum + 1 ≤ A ∧ (∀ v ∈ U, v ≤ 32 * A ^ 4) := by
  intro A U
  set L := (encNats sl).length with hL
  set N := sl.length with hN
  set Z := sl.sum + 1 with hZ
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  have hNL : N ≤ L := len_sl sl
  have hLA : L < A := Nat.lt_two_pow_self
  have hSb : (Nat.bits sl.sum).length ≤ L := by
    have := len_bits_sum sl 0; simpa using this
  have hZA : Z ≤ A := lt_pow_of_bits hSb
  have hN2 : N + 2 ≤ 2 * A := by omega
  have hNZ : (N + 2) * Z ≤ 2 * A * A := Nat.mul_le_mul hN2 hZA
  have hlen : U.length ≤ 2 * A := by
    have := go_length_le (sl.sum + 1) sl 1; exact le_trans this (by omega)
  have hval : ∀ v ∈ U, v ≤ 2 * A * A := by
    intro v hv
    have := go_val_le Z sl 1 (fun x hx => by have := List.le_sum_of_mem hx; omega) v hv
    have e : (1 + sl.length) * Z + Z = (N + 2) * Z := by simp only [hN]; ring
    omega
  have hP : (wa U).2 ≤ 2 * A * (2 * A * A) := by
    rw [wa_eq]
    have := List.sum_le_card_nsmul U (2 * A * A) hval
    simp only [smul_eq_mul] at this
    exact le_trans this (Nat.mul_le_mul_right _ hlen)
  have hW : (wa U).1 ≤ 2 * A * (2 * A * (2 * A * A)) :=
    le_trans (wa1_le U) (Nat.mul_le_mul hlen hP)
  have hA4 : 2 * A * (2 * A * (2 * A * A)) = 8 * A ^ 4 := by ring
  have hA3 : 2 * A * (2 * A * A) ≤ 8 * A ^ 4 := by
    have : A ^ 3 ≤ A ^ 4 := Nat.pow_le_pow_right hA1 (by norm_num)
    nlinarith
  have hA2 : 2 * A * A ≤ 8 * A ^ 4 := by
    have : A ^ 2 ≤ A ^ 4 := Nat.pow_le_pow_right hA1 (by norm_num)
    nlinarith
  have hA1' : A ≤ A ^ 4 := by
    calc A = A ^ 1 := by ring
      _ ≤ A ^ 4 := Nat.pow_le_pow_right hA1 (by norm_num)
  refine ⟨by omega, by omega, by omega, by omega, ?_, hZA, fun v hv => ?_⟩
  · unfold Qv
    have : U.sum = (wa U).2 := by rw [wa_eq]
    rw [this]; omega
  · have := hval v hv; omega

end TT92


set_option autoImplicit false

namespace TT92

open CookPvsNP ProjSchedTW.Complexity

/-! ## The whole machine -/

def initP : StackProg Key BSym :=
  .seq (pushProg .C .one) (.seq (addTo .C .acc) (copyProg .acc .Bc .sc))

def mainProg : StackProg Key BSym :=
  .seq (copyProg .inp .orig .sc)
    (.seq parseLoop
      (.branch (fun h => (h .bad).isSome) skipP
        (.seq initP (.seq mainLoop (.seq qP outP)))))

lemma exec_valid (w : List BSym) (sl : List ℕ) (hsl : w = encNats sl) (sa : Store)
    (hsa : ∀ k, k ≠ .orig → k ≠ .inp → sa k = []) (hsao : sa .orig = w) :
    ∃ t n, n ≤ 4000 * (w.length + 1) ^ 2 ∧
      (StackProg.seq initP (StackProg.seq mainLoop (StackProg.seq qP outP))).Exec
        (PS sa [] (enc (Nat.bits (0 + sl.sum))) (List.replicate sl.length .one ++ []) [] [] [])
        t n ∧ t .out = F w := by
  set L := w.length with hL
  set S := sl.sum with hS
  set Z := S + 1 with hZ
  set U := vals sl with hU
  set A := 2 ^ L with hA
  set M := 32 * A ^ 4 with hM
  set G := (Nat.bits M).length with hG
  have hLL : (encNats sl).length = L := by rw [hL, hsl]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := numbers_le sl
  rw [hLL] at n1 n2 n3 n4 n5 n6 n7
  have hM' : M = 32 * (2 ^ L) ^ 4 := by rw [hM, hA]
  rw [← hM'] at n1 n2 n3 n4 n5 n7
  have hMpow : M = 2 ^ (4 * L + 5) := by
    have e1 : (2 : ℕ) ^ (4 * L + 5) = 2 ^ (4 * L) * 32 := by rw [pow_add]; norm_num
    have e2 : ((2 : ℕ) ^ L) ^ 4 = 2 ^ (4 * L) := by rw [← pow_mul, mul_comm]
    rw [hM', e1, e2, mul_comm]
  have hGle : G ≤ 4 * L + 6 := by
    have := bits_le_of_le_pow (u := M) (t := 4 * L + 5) (by rw [hMpow]); omega
  have hbM : ∀ u, u ≤ M → (Nat.bits u).length ≤ G := fun u hu => bits_len_mono hu
  set s := PS sa [] (enc (Nat.bits (0 + S))) (List.replicate sl.length .one ++ []) [] [] []
    with hs
  -- init
  have i1 := exec_push .C .one s
  set u1 := Function.update s .C (.one :: s .C) with hu1
  obtain ⟨na, hna, i2⟩ := exec_addTo .C .acc (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) S 1 [] (by rfl) u1 (by simp [hu1, hs, PS])
    (by simp [hu1, hs, PS, hsa, bits_one, enc, toB]) (by simp [hu1, hs, PS])
    (by simp [hu1, hs, PS]) (by simp [hu1, hs, PS, LzOk])
  set u2 := Function.update (Function.update (Function.update u1 .lz
    (lzF (Nat.bits 1) (u1 .lz))) .C []) .acc (enc (Nat.bits (S + 1))) with hu2
  obtain ⟨nc, hnc, i3⟩ := exec_copy .acc .Bc .sc (by decide) (by decide) (by decide) u2
    (by simp [hu2, hu1, hs, PS, hsa])
  set u3 := Function.update u2 .Bc (u2 .acc ++ u2 .Bc) with hu3
  have hI : LoopInv Z u3 sl 1 [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hu3, hu2, hu1, hs, PS, hsa, hsao, hsl, wa, encNats, LzOk, lzF, bits_one, hZ, enc]
  -- loop
  obtain ⟨t2, nl, c', hnl, el, hI2, f2⟩ := exec_loop Z G M le_rfl sl 1 [] u3 hI
    (by rw [show 1 + sl.length + 1 = sl.length + 2 by omega]; exact n1)
    (by simpa [vals] using n2) (by simpa [vals] using n3) (by simpa [vals] using n4)
  simp only [List.nil_append] at hI2
  obtain ⟨_, _, _, hPB, hR, hAc, hK, _, hC, hsc, htmp, hcar, hlz⟩ := hI2
  have hU' : go Z 1 sl = U := rfl
  rw [hU'] at hPB hR hAc hK
  have v2 : ∀ k, k = .Q ∨ k = .out → t2 k = [] := by
    intro k hk
    rcases hk with rfl | rfl
    · rw [f2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; simp [hu3, hu2, hu1, hs, PS, hsa]
    · rw [f2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; simp [hu3, hu2, hu1, hs, PS, hsa]
  have hQv : (wa U).2 + (wa U).2 / 2 + (wa U).1 + (wa U).1 = Qv U := by
    simp [Qv, wa_eq]
  obtain ⟨t3, nq, hnq, eq, hQ3, _, _, _, _, f3⟩ := exec_qP (wa U).2 (wa U).1 G t2 hR hAc
    (v2 _ (Or.inl rfl)) hC hsc htmp hcar hlz (by rw [hQv]; exact hbM _ n5)
  rw [hQv] at hQ3
  obtain ⟨t4, no, hno, eo, hout⟩ := exec_outP (Qv U) U.length G U t3
    (by rw [f3 _ (by decide) (by decide) (by decide)]; exact v2 _ (Or.inr rfl))
    (by rw [f3 _ (by decide) (by decide) (by decide)]; exact hsc) hQ3
    (by rw [f3 _ (by decide) (by decide) (by decide)]; exact hPB)
    (by rw [f3 _ (by decide) (by decide) (by decide)]; exact hK) (hbM _ n5)
    (hbM _ (by show (vals sl).length ≤ M; omega))
  refine ⟨t4, 1 + 1 + (na + 1 + nc) + 1 + (nl + 1 + (nq + 1 + no)), ?_,
    StackProg.Exec.seq (StackProg.Exec.seq i1 (StackProg.Exec.seq i2 i3))
      (StackProg.Exec.seq el (StackProg.Exec.seq eq eo)), ?_⟩
  · -- time
    have hSb : (Nat.bits S).length ≤ L + 1 := bits_le_of_le_pow (by omega)
    have hZb : (Nat.bits (S + 1)).length ≤ L + 1 := bits_le_of_le_pow n6
    have hnc' : nc ≤ 6 * (L + 1) + 3 := by
      have : (u2 .acc).length = (Nat.bits (S + 1)).length := by simp [hu2, enc]
      omega
    simp only [bits_one, List.length_cons, List.length_nil] at hna
    have hUl : U.length ≤ 2 * L := by
      have h1 := go_length_le (sl.sum + 1) sl 1
      have h2 := len_sl sl
      rw [hLL] at h2
      show (go (sl.sum + 1) 1 sl).length ≤ 2 * L
      omega
    have hEU : (encNats U).length ≤ U.length * (G + 1) :=
      len_encNats_le G U (fun v hv => hbM v (n7 v hv))
    rw [hLL] at hnl
    have p1 : L * (200 * G + 400) ≤ L * (800 * L + 1600) := Nat.mul_le_mul_left _ (by omega)
    have p2 : U.length * (G + 1) ≤ (2 * L) * (4 * L + 7) := Nat.mul_le_mul hUl (by omega)
    nlinarith
  · rw [hout, hsl, F_valid]; rfl

lemma exec_main (w : List BSym) : ∃ t n, n ≤ 5000 * (w.length + 1) ^ 2 ∧
    mainProg.Exec (fun j => if j = .inp then w else []) t n ∧ t .out = F w := by
  set s0 : Store := fun j => if j = .inp then w else [] with hs0
  obtain ⟨n1, hn1, e1⟩ := exec_copy .inp .orig .sc (by decide) (by decide) (by decide) s0
    (by simp [hs0])
  set sa := Function.update s0 .orig (s0 .inp ++ s0 .orig) with hsa
  have hsaPS : sa = PS sa w (enc (Nat.bits 0)) [] [] [] [] := by
    funext k; cases k <;> simp [PS, hsa, hs0, enc]
  have hn1' : n1 ≤ 6 * w.length + 3 := by simpa [hs0] using hn1
  obtain ⟨t, n2, hn2, e2, hval, hinv⟩ := parse_all sa w.length w 0 [] le_rfl
  rw [← hsaPS] at e2
  have hpb : pbound w.length (Nat.bits 0).length = (w.length + 1) * (12 * w.length + 20) + 1 := by
    simp [pbound]
  rw [hpb] at hn2
  by_cases hw : ∃ sl, w = encNats sl
  · obtain ⟨sl, hsl⟩ := hw
    have ht := hval sl hsl
    subst ht
    have hbr : (fun h : Key → Option BSym => (h .bad).isSome)
        (fun k => (PS sa [] (enc (Nat.bits (0 + sl.sum))) (List.replicate sl.length .one ++ [])
          [] [] [] k).head?) = false := by
      simp [PS]
    obtain ⟨t3, n3, hn3, e3, hout⟩ := exec_valid w sl hsl sa
      (by intro k k1 k2; simp [hsa, hs0, k1, k2]) (by simp [hsa, hs0])
    refine ⟨t3, n1 + 1 + (n2 + 1 + (1 + n3)), ?_,
      StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.branchFalse hbr e3)), hout⟩
    nlinarith
  · obtain ⟨i', a', nu', z', rfl⟩ := hinv (fun sl h => hw ⟨sl, h⟩)
    refine ⟨_, n1 + 1 + (n2 + 1 + (1 + 1)), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.branchTrue (by simp [PS]) (exec_skip _))), ?_⟩
    · nlinarith
    · rw [F_invalid hw]; simp [PS, hsa, hs0]

lemma absorb (L : ℕ) : 5000 * (L + 1) ^ 2 ≤ L ^ 30000 + 30000 := by
  rcases L with _ | _ | L
  · norm_num
  · norm_num
  · have key : 5000 * (L + 1 + 1 + 1) ^ 2 ≤ (L + 2) ^ 17 := by
      have h1 : 2 ^ 15 ≤ (L + 2) ^ 15 := Nat.pow_le_pow_left (by omega) 15
      have h2 : (L + 2) ^ 17 = (L + 2) ^ 2 * (L + 2) ^ 15 := by ring
      have h4 : (L + 1 + 1 + 1) ^ 2 ≤ 4 * (L + 2) ^ 2 := by
        have h : L + 1 + 1 + 1 ≤ 2 * (L + 2) := by omega
        calc (L + 1 + 1 + 1) ^ 2 ≤ (2 * (L + 2)) ^ 2 := Nat.pow_le_pow_left h 2
          _ = 4 * (L + 2) ^ 2 := by ring
      rw [h2]
      generalize (L + 2) ^ 15 = X at h1
      generalize (L + 1 + 1 + 1) ^ 2 = Z at h4 ⊢
      generalize (L + 2) ^ 2 = Y at h4 ⊢
      have hYX : Y * 32768 ≤ Y * X := Nat.mul_le_mul_left _ (by simpa using h1)
      omega
    have h3 : (L + 2) ^ 17 ≤ (L + 2) ^ 30000 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc 5000 * (L + 1 + 1 + 1) ^ 2 ≤ (L + 2) ^ 17 := key
      _ ≤ (L + 2) ^ 30000 := h3
      _ ≤ (L + 1 + 1) ^ 30000 + 30000 := Nat.le_add_right _ _

theorem F_exec (w : List BSym) : ∃ s n, n ≤ w.length ^ 30000 + 30000 ∧
    mainProg.Exec (fun j => if j = .inp then w else []) s n ∧ s .out = F w := by
  obtain ⟨t, n, hn, e, ho⟩ := exec_main w
  exact ⟨t, n, le_trans hn (absorb _), e, ho⟩

theorem F_poly : PolyTimeComputable F :=
  stack_program_polytime mainProg .inp .out F 30000 F_exec

end TT92


theorem solution :
    ∃ f : List ProjSchedTW.Complexity.BSym → List ProjSchedTW.Complexity.BSym,
      CookPvsNP.PolyTimeComputable f ∧
      ∀ x : List ProjSchedTW.Complexity.BSym,
        ∃ (k : ℕ) (p : Fin k → ℕ), StrictMono p ∧
          (x ∈ ProjSchedTW.Complexity.partitionLang ↔
            ProjSchedTW.Complexity.PartitionYes (List.ofFn p)) ∧
          ((TwoAgentSched.TotalTotal.construction p).RecYes (TwoAgentSched.TotalTotal.thresholdQ p)
              (TwoAgentSched.TotalTotal.thresholdQ p) ↔
            f x ∈ TwoAgentSched.TotalTotal.targetLang) :=
  ⟨TT92.F, TT92.F_poly, TT92.F_correct⟩
