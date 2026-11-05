-- Prove2me | solution 1 for TwoAgentSched.Shops.shops_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:39:56.385305+00:00
-- url     : https://prove2.me/submissions/01094001-f399-497b-ba14-148a30a972f7

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_TwoAgentSched_Shops_Construction
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_TwoAgentSched_Shops_theorem_10_1_equivalence
import Theorems.Thm_TwoAgentSched_Shops_theorem_10_2_equivalence

set_option autoImplicit false

namespace ShopsEnc

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
  | inp | orig | acc | tmp | car | lz | bad | nu | bc | e0 | c1 | c2 | sc | R | out
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .orig, .acc, .tmp, .car, .lz, .bad, .nu, .bc, .e0, .c1, .c2, .sc, .R, .out}
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
  | .orig => s0 .orig | .bc => s0 .bc | .e0 => s0 .e0 | .c1 => s0 .c1 | .c2 => s0 .c2
  | .sc => s0 .sc | .R => s0 .R | .out => s0 .out

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

/-! ## The binary counter -/

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

lemma bits_one : Nat.bits 1 = [true] := by
  have := Nat.bits_append_bit 0 true (by simp)
  simpa using this

def incAct (_ : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .c1 then .pop else if k = .e0 then .push .one else .keep

def countBody : StackProg Key BSym :=
  .seq (.act incAct) (.seq (addLoop .e0 .bc) (transferProg .tmp (fun k => decide (k = .bc))))

def countLoop : StackProg Key BSym := .loop (fun h => (h .c1).isSome) countBody

lemma exec_count : ∀ (N b : ℕ) (s : Store), s .c1 = List.replicate N .one →
    s .bc = enc (Nat.bits b) → s .e0 = [] → s .tmp = [] → s .car = [] → s .lz = [] →
    ∃ n ≤ N * (6 * (b + N) + 30) + 1, countLoop.Exec s
      (Function.update (Function.update s .c1 []) .bc (enc (Nat.bits (b + N)))) n := by
  intro N
  induction N with
  | zero =>
    intro b s hc1 hbc _ _ _ _
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update s .c1 []) .bc (enc (Nat.bits (b + 0))) = s := by
      funext k
      by_cases h1 : k = .bc
      · subst h1; simp [hbc]
      by_cases h2 : k = .c1
      · subst h2; simp [hc1]
      · simp [h1, h2]
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hc1])
  | succ N ih =>
    intro b s hc1 hbc he0 htmp hcar hlz
    set s1 := StackProg.applyAct incAct s with hs1
    have h1c1 : s1 .c1 = List.replicate N .one := by
      simp [hs1, StackProg.applyAct, incAct, StackAct.apply, hc1, List.replicate_succ]
    have h1e0 : s1 .e0 = enc [true] ++ [] := by
      simp [hs1, StackProg.applyAct, incAct, StackAct.apply, he0, enc, toB]
    have h1oth : ∀ k, k ≠ .c1 → k ≠ .e0 → s1 k = s k := by
      intro k k1 k2; simp [hs1, StackProg.applyAct, incAct, StackAct.apply, k1, k2]
    obtain ⟨n1, hn1, e1⟩ := exec_addLoop .e0 .bc (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) [] (by rfl) _ (Nat.bits b) [true] false s1 le_rfl
      (by rw [h1oth _ (by decide) (by decide), hbc]) h1e0
      (by rw [h1oth _ (by decide) (by decide), hcar]; rfl)
      (Or.inl (by rw [h1oth _ (by decide) (by decide), hlz]))
    set s2 := addPost .e0 .bc (Nat.bits b) [true] false [] s1 with hs2
    have hadd : addB (Nat.bits b) [true] false = Nat.bits (b + 1) := by
      rw [bits_add, bits_one]
    obtain ⟨n2, hn2, e2⟩ := exec_transfer .tmp (fun k => decide (k = .bc)) _ s2 rfl
    set s3 := transferStore .tmp (fun k => decide (k = .bc)) s2 with hs3
    have h3 : ∀ k, s3 k = if k = .c1 then List.replicate N .one
        else if k = .bc then enc (Nat.bits (b + 1)) else s k := by
      intro k
      by_cases k1 : k = .c1
      · subst k1; simp [hs3, hs2, transferStore, addPost, h1c1]
      by_cases k2 : k = .bc
      · subst k2; simp [hs3, hs2, transferStore, addPost, hadd, htmp, h1oth]
      by_cases k3 : k = .e0
      · subst k3; simp [hs3, hs2, transferStore, addPost, he0]
      by_cases k4 : k = .tmp
      · subst k4; simp [hs3, hs2, transferStore, addPost, htmp]
      by_cases k5 : k = .car
      · subst k5; simp [hs3, hs2, transferStore, addPost, hcar]
      by_cases k6 : k = .lz
      · subst k6; simp [hs3, hs2, transferStore, addPost, hlz, lzF, h1oth]
      · simp [hs3, hs2, transferStore, addPost, k1, k2, k3, k4, k5, k6, h1oth]
    obtain ⟨m, hm, ex⟩ := ih (b + 1) s3 (by rw [h3]; simp) (by rw [h3]; simp)
      (by rw [h3]; simp [he0]) (by rw [h3]; simp [htmp]) (by rw [h3]; simp [hcar])
      (by rw [h3]; simp [hlz])
    have hfin : Function.update (Function.update s3 .c1 []) .bc (enc (Nat.bits (b + 1 + N))) =
        Function.update (Function.update s .c1 []) .bc (enc (Nat.bits (b + (N + 1)))) := by
      funext k
      by_cases k1 : k = .bc
      · subst k1; simp [Nat.add_assoc, Nat.add_comm 1 N]
      by_cases k2 : k = .c1
      · subst k2; simp
      · simp [k1, k2, h3]
    rw [hfin] at ex
    have eb : countBody.Exec s s3 (1 + 1 + (n1 + 1 + n2)) :=
      StackProg.Exec.seq (StackProg.Exec.act incAct s) (StackProg.Exec.seq e1 e2)
    refine ⟨1 + (1 + 1 + (n1 + 1 + n2)) + 1 + m, ?_,
      StackProg.Exec.loopTrue (by simp [hc1, List.replicate_succ]) eb ex⟩
    have lb := len_bits_le b
    have lb1 := len_bits_le (b + 1)
    have : s2 .tmp = (enc (Nat.bits (b + 1))).reverse := by simp [hs2, addPost, hadd, h1oth, htmp]
    rw [this] at hn2
    simp only [enc, List.length_reverse, List.length_map, List.length_cons, List.length_nil,
      Bool.toNat_false] at hn1 hn2
    have hNb : N * (6 * (b + 1 + N) + 30) ≤ N * (6 * (b + (N + 1)) + 30) :=
      Nat.mul_le_mul_left _ (by omega)
    have : (N + 1) * (6 * (b + (N + 1)) + 30) = N * (6 * (b + (N + 1)) + 30) + (6 * (b + (N + 1)) + 30) := by ring
    omega


/-! ## Output-phase building blocks (the output `O` is kept reversed on `R`) -/

def skipP : StackProg Key BSym := .act (fun _ _ => .keep)

def pushR (a : BSym) : StackProg Key BSym := .act (fun _ k => if k = .R then .push a else .keep)

def pushL : List BSym → StackProg Key BSym
  | [] => skipP
  | a :: P => .seq (pushR a) (pushL P)

def popAct (c : Key) : StackProg Key BSym := .act (fun _ k => if k = c then .pop else .keep)

def emitL (c : Key) (P : List BSym) : StackProg Key BSym :=
  .loop (fun h => (h c).isSome) (.seq (popAct c) (pushL P))

lemma exec_skip (s : Store) : skipP.Exec s s 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (_ : Key) => (StackAct.keep : StackAct BSym)) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (_ : Key) => (StackAct.keep : StackAct BSym)) s = s := by
    funext k; simp [StackProg.applyAct, StackAct.apply]
  rw [this] at e; exact e

lemma exec_pushR (a : BSym) (s : Store) :
    (pushR a).Exec s (Function.update s .R (a :: s .R)) 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (k : Key) =>
    if k = .R then StackAct.push a else StackAct.keep) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (k : Key) =>
      if k = .R then StackAct.push a else StackAct.keep) s = Function.update s .R (a :: s .R) := by
    funext k; by_cases hk : k = .R
    · subst hk; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, hk]
  rw [this] at e; exact e

lemma exec_pushL : ∀ (P : List BSym) (s : Store),
    (pushL P).Exec s (Function.update s .R (P.reverse ++ s .R)) (2 * P.length + 1) := by
  intro P
  induction P with
  | nil => intro s; simpa [pushL] using exec_skip s
  | cons a P ih =>
    intro s
    have e := StackProg.Exec.seq (exec_pushR a s) (ih _)
    have hst : Function.update (Function.update s .R (a :: s .R)) .R
        (P.reverse ++ (Function.update s .R (a :: s .R)) .R) =
        Function.update s .R ((a :: P).reverse ++ s .R) := by
      simp
    rw [hst] at e
    simpa [pushL, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using e

lemma exec_popAct (c : Key) (s : Store) :
    (popAct c).Exec s (Function.update s c (s c).tail) 1 := by
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (k : Key) =>
    if k = c then StackAct.pop else (StackAct.keep : StackAct BSym)) s
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (k : Key) =>
      if k = c then StackAct.pop else (StackAct.keep : StackAct BSym)) s =
      Function.update s c (s c).tail := by
    funext k; by_cases hk : k = c
    · subst hk; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, hk]
  rw [this] at e; exact e

lemma exec_emitL (c : Key) (hc : c ≠ .R) (P : List BSym) : ∀ (N : ℕ) (s : Store),
    s c = List.replicate N .one →
    ∃ n ≤ N * (2 * P.length + 5) + 1, (emitL c P).Exec s
      (Function.update (Function.update s c []) .R ((List.replicate N P).flatten.reverse ++ s .R)) n := by
  intro N
  induction N with
  | zero =>
    intro s hs
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update s c []) .R
        ((List.replicate 0 P).flatten.reverse ++ s .R) = s := by
      funext k
      by_cases h1 : k = .R
      · subst h1; simp
      by_cases h2 : k = c
      · subst h2; simp [h1, hs]
      · simp [h1, h2]
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | succ N ih =>
    intro s hs
    set s1 := Function.update s c (s c).tail with hs1
    set s2 := Function.update s1 .R (P.reverse ++ s1 .R) with hs2
    have eb : (StackProg.seq (popAct c) (pushL P)).Exec s s2 (1 + 1 + (2 * P.length + 1)) :=
      StackProg.Exec.seq (exec_popAct c s) (exec_pushL P s1)
    have h2c : s2 c = List.replicate N .one := by
      simp [hs2, hs1, hc, hs, List.replicate_succ]
    obtain ⟨m, hm, ex⟩ := ih s2 h2c
    have hfin : Function.update (Function.update s2 c []) .R
        ((List.replicate N P).flatten.reverse ++ s2 .R) =
        Function.update (Function.update s c []) .R
          ((List.replicate (N + 1) P).flatten.reverse ++ s .R) := by
      funext k
      by_cases h1 : k = .R
      · subst h1; simp [hs2, hs1, hc, Ne.symm hc, List.replicate_succ]
      by_cases h2 : k = c
      · subst h2; simp [h1]
      · simp [h1, h2, hs2, hs1]
    rw [hfin] at ex
    refine ⟨1 + (1 + 1 + (2 * P.length + 1)) + 1 + m, ?_,
      StackProg.Exec.loopTrue (by simp [hs, List.replicate_succ]) eb ex⟩
    have : (N + 1) * (2 * P.length + 5) = N * (2 * P.length + 5) + (2 * P.length + 5) := by ring
    omega

/-- copy the unary counter `nu` into `c1` and emit `P` that many times. -/
def emitNu (P : List BSym) : StackProg Key BSym := .seq (copyProg .nu .c1 .sc) (emitL .c1 P)

lemma exec_emitNu (P : List BSym) (V : ℕ) (s : Store) (hnu : s .nu = List.replicate V .one)
    (hc1 : s .c1 = []) (hsc : s .sc = []) :
    ∃ n ≤ 6 * V + 3 + 1 + (V * (2 * P.length + 5) + 1), (emitNu P).Exec s
      (Function.update s .R ((List.replicate V P).flatten.reverse ++ s .R)) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy .nu .c1 .sc (by decide) (by decide) (by decide) s hsc
  rw [hnu, hc1, List.append_nil] at e1
  obtain ⟨n2, hn2, e2⟩ := exec_emitL .c1 (by decide) P V (Function.update s .c1 (List.replicate V .one)) (by simp)
  have hfin : Function.update (Function.update (Function.update s .c1 (List.replicate V .one)) .c1 [])
      .R ((List.replicate V P).flatten.reverse ++
        (Function.update s .c1 (List.replicate V .one)) .R) =
      Function.update s .R ((List.replicate V P).flatten.reverse ++ s .R) := by
    funext k
    by_cases h1 : k = .R
    · subst h1; simp
    by_cases h2 : k = .c1
    · subst h2; simp [hc1]
    · simp [h1, h2]
  rw [hfin] at e2
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  simp only [hnu, List.length_replicate] at hn1
  omega


lemma exec_transferR (c : Key) (hc : c ≠ .R) (s : Store) :
    ∃ n ≤ 3 * (s c).length + 1, (transferProg c (fun k => decide (k = .R))).Exec s
      (Function.update (Function.update s c []) .R ((s c).reverse ++ s .R)) n := by
  obtain ⟨n, hn, e⟩ := exec_transfer c (fun k => decide (k = .R)) (s c) s rfl
  have : transferStore c (fun k => decide (k = .R)) s =
      Function.update (Function.update s c []) .R ((s c).reverse ++ s .R) := by
    funext k
    by_cases h1 : k = .R
    · subst h1; simp [transferStore, Ne.symm hc]
    by_cases h2 : k = c
    · subst h2; simp [transferStore, h1]
    · simp [transferStore, h1, h2]
  rw [this] at e; exact ⟨n, hn, e⟩


end ShopsEnc

set_option autoImplicit false

namespace ShopsEnc

open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.Shops

/-! ## Scheduling part: the shop instances written by the machine -/

lemma nonoverlap_sum_le {α : Type*} [DecidableEq α] (a L : α → ℝ)
    (hL : ∀ i, 0 ≤ L i)
    (hdisj : ∀ i j, i ≠ j → a i + L i ≤ a j ∨ a j + L j ≤ a i) :
    ∀ (n : ℕ) (T : Finset α), T.card = n → ∀ (lo hi : ℝ), lo ≤ hi →
      (∀ i ∈ T, lo ≤ a i ∧ a i + L i ≤ hi) → ∑ i ∈ T, L i ≤ hi - lo := by
  intro n
  induction n with
  | zero =>
    intro T hcard lo hi hle _
    rw [Finset.card_eq_zero.mp hcard, Finset.sum_empty]
    linarith
  | succ n ih =>
    intro T hcard lo hi hle hT
    by_cases hzero : ∃ i₀ ∈ T, L i₀ = 0
    · obtain ⟨i₀, hi₀, hLi₀⟩ := hzero
      rw [← Finset.add_sum_erase _ _ hi₀, hLi₀, zero_add]
      exact ih (T.erase i₀) (by rw [Finset.card_erase_of_mem hi₀, hcard]; rfl) lo hi hle
        (fun i hi => hT i (Finset.mem_of_mem_erase hi))
    · push_neg at hzero
      have hpos : ∀ i ∈ T, 0 < L i := fun i hi => lt_of_le_of_ne (hL i) (Ne.symm (hzero i hi))
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image T a hne
      rw [← Finset.add_sum_erase _ _ hi₀]
      have hi₀_bounds := hT i₀ hi₀
      have hsub : ∑ i ∈ T.erase i₀, L i ≤ hi - (a i₀ + L i₀) := by
        refine ih (T.erase i₀) (by rw [Finset.card_erase_of_mem hi₀, hcard]; rfl)
          (a i₀ + L i₀) hi hi₀_bounds.2 (fun j hj => ?_)
        have hjT : j ∈ T := Finset.mem_of_mem_erase hj
        have hne_ji : i₀ ≠ j := (Finset.ne_of_mem_erase hj).symm
        have haj : a i₀ ≤ a j := hmin j hjT
        have hLj : 0 < L j := hpos j hjT
        rcases hdisj i₀ j hne_ji with h1 | h2
        · exact ⟨h1, (hT j hjT).2⟩
        · linarith
      linarith

lemma sum_get_eq_sum (p : List ℕ) : ∑ i : Fin p.length, p.get i = p.sum := by
  induction p with
  | nil => simp
  | cons a l ih =>
    change ∑ i : Fin (l.length + 1), (a :: l).get i = (a :: l).sum
    rw [Fin.sum_univ_succ]
    simp [ih]

lemma sum_get_real_eq_partSum (p : List ℕ) :
    ∑ i : Fin p.length, (p.get i : ℝ) = partSum p := by
  unfold partSum
  rw [← sum_get_eq_sum p]
  push_cast
  rfl

def cum {k : ℕ} (w : Fin k → ℝ) (S : Finset (Fin k)) (i : Fin k) : ℝ :=
  ∑ j ∈ S.filter (· < i), w j

lemma cum_nonneg {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset (Fin k)) (i : Fin k) :
    0 ≤ cum w S i :=
  Finset.sum_nonneg (fun j _ => hw j)

lemma cum_add_le_sum {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i)
    {S : Finset (Fin k)} {i : Fin k} (hi : i ∈ S) :
    cum w S i + w i ≤ ∑ j ∈ S, w j := by
  unfold cum
  have hnot : i ∉ S.filter (· < i) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hw j)
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact hi
  · exact (Finset.mem_filter.mp hj).1

lemma cum_add_le_cum_of_lt {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i)
    {S : Finset (Fin k)} {i j : Fin k} (hi : i ∈ S) (hij : i < j) :
    cum w S i + w i ≤ cum w S j := by
  unfold cum
  have hnot : i ∉ S.filter (· < i) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hw x)
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_filter.mpr ⟨hi, hij⟩
  · obtain ⟨hxS, hxi⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxS, lt_trans hxi hij⟩

lemma cum_disj {k : ℕ} {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i)
    {S : Finset (Fin k)} {i j : Fin k} (hi : i ∈ S) (hj : j ∈ S) (hne : i ≠ j) (t₀ : ℝ) :
    (t₀ + cum w S i) + w i ≤ t₀ + cum w S j ∨ (t₀ + cum w S j) + w j ≤ t₀ + cum w S i := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · left; linarith [cum_add_le_cum_of_lt hw hi hij]
  · right; linarith [cum_add_le_cum_of_lt hw hj hji]

/-- The flow shop instance of the proof of Theorem 10.1 with `ε = 0`, for `P = 2H`. -/
def zNat (p : List ℕ) (H : ℕ) : NatInstance := ⟨p.length, 1, fun _ => 0, p.get, fun _ => H, fun _ => H⟩

/-- The open shop instance of the proof of Theorem 10.2, for `P = 2H`. -/
def oNat (p : List ℕ) (H : ℕ) : NatInstance := ⟨p.length, 1, p.get, p.get, fun _ => H, fun _ => H⟩

lemma oNat_eq (p : List ℕ) (H : ℕ) (hP : p.sum = 2 * H) : (oNat p H).toInstance = openInst p := by
  have hH : ((H : ℕ) : ℝ) = partSum p / 2 := by
    unfold partSum; rw [hP]; push_cast; ring
  simp only [NatInstance.toInstance, oNat, openInst, hH]

lemma zflow_iff (p : List ℕ) (H : ℕ) (hP : p.sum = 2 * H) :
    (zNat p H).toInstance.FlowYes ((3 * H : ℕ) : ℝ) ((2 * H : ℕ) : ℝ) ↔ PartitionYes p := by
  classical
  set I := (zNat p H).toInstance with hI
  have htotR : ∑ i : Fin p.length, (p.get i : ℝ) = 2 * (H : ℝ) := by
    rw [sum_get_real_eq_partSum]; unfold partSum; rw [hP]; push_cast; ring
  have hHnn : (0 : ℝ) ≤ H := by positivity
  have hp1_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → I.p1 j = 0 := by
    intro j i h; unfold Instance.p1; rw [h]; exact Nat.cast_zero
  have hp1_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → I.p1 j = H := by
    intro j k h; unfold Instance.p1; rw [h]; rfl
  have hp2_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → I.p2 j = (p.get i : ℝ) := by
    intro j i h; unfold Instance.p2; rw [h]; rfl
  have hp2_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → I.p2 j = H := by
    intro j k h; unfold Instance.p2; rw [h]; rfl
  have ha : ∀ i : Fin I.nA, finSumFinEquiv.symm (I.aJob i) = Sum.inl i :=
    fun i => finSumFinEquiv_symm_apply_castAdd i
  have hb : ∀ k : Fin I.nB, finSumFinEquiv.symm (I.bJob k) = Sum.inr k :=
    fun k => finSumFinEquiv_symm_apply_natAdd k
  constructor
  · rintro ⟨s₁, s₂, ⟨h0, _, hd2, hfl⟩, hA, hB⟩
    set B := I.bJob ⟨0, Nat.one_pos⟩ with hBdef
    have hB1 := h0 B
    have hB2 := hfl B
    rw [hp1_inr B _ (hb _)] at hB2
    have hBQ := (hB ⟨0, Nat.one_pos⟩).2
    have hpB2 : I.pB2 ⟨0, Nat.one_pos⟩ = H := rfl
    rw [hpB2] at hBQ
    push_cast at hBQ
    have hsB : s₂ B = H := by linarith
    have ha_inj : Function.Injective I.aJob := by
      intro i j hij
      have := congrArg finSumFinEquiv.symm hij
      rw [ha i, ha j] at this
      exact Sum.inl_injective this
    have ha_ne_B : ∀ i : Fin p.length, I.aJob i ≠ B := by
      intro i h
      have := congrArg finSumFinEquiv.symm h
      rw [ha i, hBdef, hb] at this
      nomatch this
    have hpA : ∀ i : Fin p.length, I.p2 (I.aJob i) = (p.get i : ℝ) := fun i => hp2_inl _ i (ha i)
    have hs2nn : ∀ i : Fin p.length, 0 ≤ s₂ (I.aJob i) := by
      intro i
      have := hfl (I.aJob i); have := h0 (I.aJob i)
      rw [hp1_inl _ i (ha i)] at *; linarith
    set A := Finset.univ.filter
      (fun i : Fin p.length => s₂ (I.aJob i) + (p.get i : ℝ) ≤ H)
    have hdisjA : ∀ i j : Fin p.length, i ≠ j →
        s₂ (I.aJob i) + (p.get i : ℝ) ≤ s₂ (I.aJob j) ∨
          s₂ (I.aJob j) + (p.get j : ℝ) ≤ s₂ (I.aJob i) := by
      intro i j hij
      have := hd2 (I.aJob i) (I.aJob j) (fun e => hij (ha_inj e))
      rwa [hpA i, hpA j] at this
    have hsumA : ∑ i ∈ A, (p.get i : ℝ) ≤ H := by
      have := nonoverlap_sum_le (fun i : Fin p.length => s₂ (I.aJob i))
        (fun i : Fin p.length => (p.get i : ℝ)) (fun i => by positivity) hdisjA
        A.card A rfl 0 H hHnn (fun i hi => ⟨hs2nn i, (Finset.mem_filter.mp hi).2⟩)
      linarith
    have hsumAc : ∑ i ∈ Aᶜ, (p.get i : ℝ) ≤ H := by
      have := nonoverlap_sum_le (fun i : Fin p.length => s₂ (I.aJob i))
        (fun i : Fin p.length => (p.get i : ℝ)) (fun i => by positivity) hdisjA
        Aᶜ.card Aᶜ rfl (2 * H) (3 * H) (by linarith)
        (fun i hi => by
          have hnotA : ¬ (s₂ (I.aJob i) + (p.get i : ℝ) ≤ H) := by simpa [A] using hi
          have hdisjB := hd2 (I.aJob i) B (ha_ne_B i)
          rw [hpA i, hp2_inr B _ (hb _), hsB] at hdisjB
          have hAe := (hA i).2
          have hpa2 : I.pA2 i = (p.get i : ℝ) := rfl
          rw [hpa2] at hAe
          push_cast at hAe
          rcases hdisjB with h1 | h2
          · exact absurd h1 hnotA
          · exact ⟨by linarith, by linarith⟩)
      linarith
    have htot : ∑ i ∈ A, (p.get i : ℝ) + ∑ i ∈ Aᶜ, (p.get i : ℝ) = 2 * H := by
      rw [Finset.sum_add_sum_compl, htotR]
    have heq_real : ∑ i ∈ A, (p.get i : ℝ) = ∑ i ∈ Aᶜ, (p.get i : ℝ) := by linarith
    exact ⟨A, by exact_mod_cast heq_real⟩
  · rintro ⟨A, hA⟩
    have hA_real : ∑ i ∈ A, (p.get i : ℝ) = ∑ i ∈ Aᶜ, (p.get i : ℝ) := by exact_mod_cast hA
    have htot : ∑ i ∈ A, (p.get i : ℝ) + ∑ i ∈ Aᶜ, (p.get i : ℝ) = 2 * H := by
      rw [Finset.sum_add_sum_compl, htotR]
    have hsumA : ∑ i ∈ A, (p.get i : ℝ) = H := by linarith
    have hsumAc : ∑ i ∈ Aᶜ, (p.get i : ℝ) = H := by linarith
    set w : Fin p.length → ℝ := fun i => (p.get i : ℝ)
    have hw : ∀ i, 0 ≤ w i := fun i => by positivity
    let s2A : Fin I.nA → ℝ := fun i =>
      if i ∈ A then 0 + cum w A i else 2 * (H : ℝ) + cum w Aᶜ i
    let s₁ : Fin (I.nA + I.nB) → ℝ := fun _ => 0
    let s₂ : Fin (I.nA + I.nB) → ℝ :=
      fun j => Sum.elim s2A (fun _ : Fin I.nB => (H : ℝ)) (finSumFinEquiv.symm j)
    have hs2_inl : ∀ j i, finSumFinEquiv.symm j = Sum.inl i → s₂ j = s2A i := by
      intro j i h; dsimp only [s₂]; rw [h]; rfl
    have hs2_inr : ∀ j k, finSumFinEquiv.symm j = Sum.inr k → s₂ j = H := by
      intro j k h; dsimp only [s₂]; rw [h]; rfl
    have hbd : ∀ i : Fin I.nA,
        (i ∈ A → 0 ≤ s2A i ∧ s2A i + w i ≤ H) ∧
        (i ∉ A → 2 * (H : ℝ) ≤ s2A i ∧ s2A i + w i ≤ 3 * H) := by
      intro i
      constructor
      · intro hi
        have h1 := cum_nonneg hw A i
        have h2 := cum_add_le_sum hw hi
        have e : s2A i = 0 + cum w A i := if_pos hi
        rw [e]; exact ⟨by linarith, by linarith⟩
      · intro hni
        have hi : i ∈ Aᶜ := Finset.mem_compl.mpr hni
        have h1 := cum_nonneg hw Aᶜ i
        have h2 := cum_add_le_sum hw hi
        have e : s2A i = 2 * (H : ℝ) + cum w Aᶜ i := if_neg hni
        rw [e]; exact ⟨by linarith, by linarith⟩
    refine ⟨s₁, s₂, ⟨fun _ => le_rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro j₁ j₂ _
      rcases h1 : finSumFinEquiv.symm j₁ with i₁ | k₁
      · left; rw [hp1_inl j₁ i₁ h1]; simp [s₁]
      · right; rcases h2 : finSumFinEquiv.symm j₂ with i₂ | k₂
        · rw [hp1_inl j₂ i₂ h2]; simp [s₁]
        · exfalso; rename_i hne; apply hne; apply finSumFinEquiv.symm.injective
          have hk : k₁ = k₂ := Fin.ext (by
            have hlt1 : k₁.val < 1 := k₁.isLt
            have hlt2 : k₂.val < 1 := k₂.isLt
            omega)
          rw [h1, h2, hk]
    · intro j₁ j₂ hne
      rcases h1 : finSumFinEquiv.symm j₁ with i₁ | k₁ <;>
        rcases h2 : finSumFinEquiv.symm j₂ with i₂ | k₂
      · rw [hs2_inl j₁ i₁ h1, hs2_inl j₂ i₂ h2, hp2_inl j₁ i₁ h1, hp2_inl j₂ i₂ h2]
        have hij : i₁ ≠ i₂ := by
          intro e; apply hne; apply finSumFinEquiv.symm.injective; rw [h1, h2, e]
        by_cases hi1 : i₁ ∈ A <;> by_cases hi2 : i₂ ∈ A
        · have e1 : s2A i₁ = 0 + cum w A i₁ := if_pos hi1
          have e2 : s2A i₂ = 0 + cum w A i₂ := if_pos hi2
          rw [e1, e2]; exact cum_disj hw hi1 hi2 hij 0
        · left; linarith [(hbd i₁).1 hi1 |>.2, (hbd i₂).2 hi2 |>.1]
        · right; linarith [(hbd i₂).1 hi2 |>.2, (hbd i₁).2 hi1 |>.1]
        · have e1 : s2A i₁ = 2 * (H : ℝ) + cum w Aᶜ i₁ := if_neg hi1
          have e2 : s2A i₂ = 2 * (H : ℝ) + cum w Aᶜ i₂ := if_neg hi2
          rw [e1, e2]
          exact cum_disj hw (Finset.mem_compl.mpr hi1) (Finset.mem_compl.mpr hi2) hij _
      · rw [hs2_inl j₁ i₁ h1, hs2_inr j₂ k₂ h2, hp2_inl j₁ i₁ h1, hp2_inr j₂ k₂ h2]
        by_cases hi1 : i₁ ∈ A
        · left; linarith [(hbd i₁).1 hi1 |>.2]
        · right; linarith [(hbd i₁).2 hi1 |>.1]
      · rw [hs2_inr j₁ k₁ h1, hs2_inl j₂ i₂ h2, hp2_inr j₁ k₁ h1, hp2_inl j₂ i₂ h2]
        by_cases hi2 : i₂ ∈ A
        · right; linarith [(hbd i₂).1 hi2 |>.2]
        · left; linarith [(hbd i₂).2 hi2 |>.1]
      · exfalso; apply hne; apply finSumFinEquiv.symm.injective
        have hk : k₁ = k₂ := Fin.ext (by
          have hlt1 : k₁.val < 1 := k₁.isLt
          have hlt2 : k₂.val < 1 := k₂.isLt
          omega)
        rw [h1, h2, hk]
    · intro j
      rcases h : finSumFinEquiv.symm j with i | k
      · rw [hs2_inl j i h, hp1_inl j i h]
        simp only [s₁, zero_add]
        by_cases hi : i ∈ A
        · exact (hbd i).1 hi |>.1
        · linarith [(hbd i).2 hi |>.1]
      · rw [hs2_inr j k h, hp1_inr j k h]; simp [s₁]
    · intro i
      rw [hs2_inl _ i (ha i)]
      have e1 : I.pA1 i = 0 := Nat.cast_zero
      have e2 : I.pA2 i = w i := rfl
      rw [e1, e2]
      push_cast
      by_cases hi : i ∈ A
      · exact ⟨by simp [s₁]; try linarith, by linarith [(hbd i).1 hi |>.2]⟩
      · exact ⟨by simp [s₁]; try linarith, by linarith [(hbd i).2 hi |>.2]⟩
    · intro k
      rw [hs2_inr _ k (hb k)]
      have e1 : I.pB1 k = H := rfl
      have e2 : I.pB2 k = H := rfl
      rw [e1, e2]
      push_cast
      exact ⟨by simp [s₁]; try linarith, by linarith⟩

end ShopsEnc

set_option autoImplicit false

namespace ShopsEnc

open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.Shops

/-! ## Codes -/

lemma bits_inj {a b : ℕ} (h : Nat.bits a = Nat.bits b) : a = b := by
  rw [← (canon_bits_bval a).2, ← (canon_bits_bval b).2, h]

lemma encNats_inj : ∀ {a b : List ℕ}, encNats a = encNats b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by rw [encNats_cons'] at h; simp [encNats] at h
  | _ :: _, [], h => by rw [encNats_cons'] at h; simp [encNats] at h
  | x :: a, y :: b, h => by
    rw [encNats_cons', encNats_cons'] at h
    obtain ⟨h1, h2⟩ := enc_append_inj (by rfl) (by rfl) h
    simp only [List.cons.injEq, true_and] at h2
    rw [bits_inj h1, encNats_inj h2]

lemma encNats_append (a b : List ℕ) : encNats (a ++ b) = encNats a ++ encNats b := by
  simp [encNats]

lemma codeList_inj {I J : NatInstance} {a b c d : ℕ} (h : I.codeList a b = J.codeList c d) :
    I = J ∧ a = c ∧ b = d := by
  obtain ⟨nA, nB, f1, f2, g1, g2⟩ := I
  obtain ⟨nA', nB', f1', f2', g1', g2'⟩ := J
  simp only [NatInstance.codeList, List.cons_append, List.nil_append, List.append_assoc,
    List.cons.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  have e1 := List.append_inj h (by simp)
  have e2 := List.append_inj e1.2 (by simp)
  have e3 := List.append_inj e2.2 (by simp)
  have e4 := List.append_inj e3.2 (by simp)
  have q1 := List.ofFn_injective e1.1
  have q2 := List.ofFn_injective e2.1
  have q3 := List.ofFn_injective e3.1
  have q4 := List.ofFn_injective e4.1
  simp only [List.cons.injEq, and_true] at e4
  subst q1 q2 q3 q4
  exact ⟨rfl, e4.2.1, e4.2.2⟩

lemma encNats_codeList_ne_nil (I : NatInstance) (a b : ℕ) : encNats (I.codeList a b) ≠ [] := by
  simp [NatInstance.codeList, encNats, encNat]

lemma mem_flowLang (I : NatInstance) (a b : ℕ) :
    encNats (I.codeList a b) ∈ flowLang ↔ I.toInstance.FlowYes a b := by
  constructor
  · rintro ⟨J, c, d, hJ, hx⟩
    obtain ⟨rfl, rfl, rfl⟩ := codeList_inj (encNats_inj hx)
    exact hJ
  · intro h; exact ⟨I, a, b, h, rfl⟩

lemma mem_openLang (I : NatInstance) (a b : ℕ) :
    encNats (I.codeList a b) ∈ openLang ↔ I.toInstance.OpenYes a b := by
  constructor
  · rintro ⟨J, c, d, hJ, hx⟩
    obtain ⟨rfl, rfl, rfl⟩ := codeList_inj (encNats_inj hx)
    exact hJ
  · intro h; exact ⟨I, a, b, h, rfl⟩

lemma nil_not_flow : ([] : List BSym) ∉ flowLang := by
  rintro ⟨J, c, d, -, hx⟩; exact encNats_codeList_ne_nil J c d hx.symm

lemma nil_not_open : ([] : List BSym) ∉ openLang := by
  rintro ⟨J, c, d, -, hx⟩; exact encNats_codeList_ne_nil J c d hx.symm

/-- The instance written by the machine: the flow shop one (`fl = true`) or the open shop one. -/
def outI (fl : Bool) (p : List ℕ) : NatInstance :=
  if fl then zNat p (p.sum / 2) else oNat p (p.sum / 2)

def outF (fl : Bool) (p : List ℕ) : List BSym :=
  encNats ((outI fl p).codeList (3 * (p.sum / 2)) p.sum)

open Classical in
noncomputable def Fr (fl : Bool) (w : List BSym) : List BSym :=
  if h : ∃ p, w = encNats p then
    (if h.choose.sum % 2 = 0 then outF fl h.choose else []) else []

lemma Fr_valid (fl : Bool) (p : List ℕ) :
    Fr fl (encNats p) = if p.sum % 2 = 0 then outF fl p else [] := by
  have h : ∃ s, encNats p = encNats s := ⟨p, rfl⟩
  rw [Fr, dif_pos h, show h.choose = p from (encNats_inj h.choose_spec).symm]

lemma Fr_invalid (fl : Bool) {w : List BSym} (hw : ¬ ∃ p, w = encNats p) : Fr fl w = [] := by
  rw [Fr, dif_neg hw]

lemma sum_get' (s : List ℕ) : ∑ i : Fin s.length, s.get i = s.sum := by
  have := sum_get_real_eq_partSum s
  unfold partSum at this
  exact_mod_cast this

lemma even_of_partitionYes' {s : List ℕ} (h : PartitionYes s) : s.sum % 2 = 0 := by
  obtain ⟨A, hA⟩ := h
  have htot : (∑ i ∈ A, s.get i) + (∑ i ∈ Aᶜ, s.get i) = s.sum := by
    rw [Finset.sum_add_sum_compl, sum_get']
  omega

lemma partitionYes_of_sum_zero' (s : List ℕ) (h : s.sum = 0) : PartitionYes s := by
  refine ⟨∅, ?_⟩
  have htot : (∑ i : Fin s.length, s.get i) = 0 := by rw [sum_get', h]
  simp [h]

lemma flow_out_iff (p : List ℕ) (he : p.sum % 2 = 0) :
    outF true p ∈ flowLang ↔ PartitionYes p := by
  rw [outF, mem_flowLang, outI, if_pos rfl]
  have hP : p.sum = 2 * (p.sum / 2) := by omega
  have := zflow_iff p (p.sum / 2) hP
  rw [← hP] at this
  exact this

lemma open_out_iff (p : List ℕ) (he : p.sum % 2 = 0) :
    outF false p ∈ openLang ↔ (openInst p).OpenYes (openQA p) (openQB p) := by
  rw [outF, mem_openLang, outI, if_neg (by simp)]
  have hP : p.sum = 2 * (p.sum / 2) := by omega
  rw [oNat_eq p _ hP]
  have h1 : (((3 * (p.sum / 2) : ℕ)) : ℝ) = openQA p := by
    obtain ⟨H, hH⟩ : ∃ H, p.sum = 2 * H := ⟨p.sum / 2, by omega⟩
    unfold openQA partSum; rw [hH, show 2 * H / 2 = H by omega]; push_cast; ring
  have h2 : ((p.sum : ℕ) : ℝ) = openQB p := rfl
  rw [h1, h2]

theorem flow_correct (x : List BSym) :
    ((∃ p : List ℕ, Even p.sum ∧ (2 ≤ p.sum ∨ p.length ≤ 1) ∧
        (flowInst p).FlowYes (flowQA p) (flowQB p) ∧ x = encNats p) ∨
      (∃ p : List ℕ, p.sum = 0 ∧ x = encNats p)) ↔ Fr true x ∈ flowLang := by
  by_cases hx : ∃ p, x = encNats p
  · obtain ⟨p, rfl⟩ := hx
    rw [Fr_valid]
    by_cases he : p.sum % 2 = 0
    · rw [if_pos he, flow_out_iff p he]
      constructor
      · rintro (⟨q, hq, hr, hf, hpq⟩ | ⟨q, hq, hpq⟩)
        · obtain rfl := encNats_inj hpq
          exact (theorem_10_1_equivalence _ hq hr).2 hf
        · obtain rfl := encNats_inj hpq
          exact partitionYes_of_sum_zero' _ hq
      · intro hyes
        by_cases h0 : p.sum = 0
        · exact Or.inr ⟨p, h0, rfl⟩
        · have hev : Even p.sum := Nat.even_iff.2 he
          have h2 : 2 ≤ p.sum := by omega
          exact Or.inl ⟨p, hev, Or.inl h2, (theorem_10_1_equivalence p hev (Or.inl h2)).1 hyes, rfl⟩
    · rw [if_neg he]
      simp only [nil_not_flow, iff_false]
      rintro (⟨q, hq, -, -, hpq⟩ | ⟨q, hq, hpq⟩)
      · obtain rfl := encNats_inj hpq
        exact he (Nat.even_iff.1 hq)
      · obtain rfl := encNats_inj hpq
        omega
  · rw [Fr_invalid true hx]
    simp only [nil_not_flow, iff_false]
    rintro (⟨q, -, -, -, hpq⟩ | ⟨q, -, hpq⟩) <;> exact hx ⟨q, hpq⟩

theorem open_correct (x : List BSym) :
    (∃ p : List ℕ, (openInst p).OpenYes (openQA p) (openQB p) ∧ x = encNats p) ↔
      Fr false x ∈ openLang := by
  by_cases hx : ∃ p, x = encNats p
  · obtain ⟨p, rfl⟩ := hx
    rw [Fr_valid]
    by_cases he : p.sum % 2 = 0
    · rw [if_pos he, open_out_iff p he]
      constructor
      · rintro ⟨q, hq, hpq⟩
        obtain rfl := encNats_inj hpq
        exact hq
      · intro h; exact ⟨p, h, rfl⟩
    · rw [if_neg he]
      simp only [nil_not_open, iff_false]
      rintro ⟨q, hq, hpq⟩
      obtain rfl := encNats_inj hpq
      exact he (even_of_partitionYes' ((theorem_10_2_equivalence _).2 hq))
  · rw [Fr_invalid false hx]
    simp only [nil_not_open, iff_false]
    rintro ⟨q, -, hpq⟩; exact hx ⟨q, hpq⟩

/-! ## The output as the machine writes it -/

lemma encNats_ofFn_get (p : List ℕ) : encNats (List.ofFn p.get) = encNats p := by
  rw [List.ofFn_get]

lemma encNats_replicate_zero (k : ℕ) :
    encNats (List.replicate k 0) = (List.replicate k [BSym.sep]).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, encNats, encNat] at ih ⊢; exact ih

lemma encNat_eq' (k : ℕ) : encNat k = enc (Nat.bits k) ++ [BSym.sep] := encNat_eq k

def midOut (fl : Bool) (p : List ℕ) : List BSym :=
  if fl then (List.replicate p.length [BSym.sep]).flatten ++ encNats p else encNats p ++ encNats p

theorem outF_spec (fl : Bool) (p : List ℕ) :
    outF fl p = enc (Nat.bits p.length) ++ [BSym.sep, .one, .sep] ++ midOut fl p ++
      enc (Nat.bits (p.sum / 2)) ++ [BSym.sep] ++ enc (Nat.bits (p.sum / 2)) ++ [BSym.sep] ++
      enc (Nat.bits (3 * (p.sum / 2))) ++ [BSym.sep] ++ enc (Nat.bits p.sum) ++ [BSym.sep] := by
  have h1 : encNat 1 = [BSym.one, BSym.sep] := by
    rw [encNat_eq', bits_one]; rfl
  cases fl
  · rw [outF, show outI false p = oNat p (p.sum / 2) from rfl]
    simp only [midOut, NatInstance.codeList, oNat, Bool.false_eq_true, if_false,
      encNats_append, encNats_ofFn_get]
    simp [encNats, encNat_eq', h1, List.ofFn_const, enc, toB]
  · rw [outF, show outI true p = zNat p (p.sum / 2) from rfl]
    simp only [midOut, NatInstance.codeList, zNat, if_true, encNats_append, encNats_ofFn_get]
    have : List.ofFn (fun _ : Fin p.length => (0 : ℕ)) = List.replicate p.length 0 := List.ofFn_const _ _
    rw [this, encNats_replicate_zero]
    simp [encNats, encNat_eq', h1, List.ofFn_const, enc, toB]

end ShopsEnc

set_option autoImplicit false

namespace ShopsEnc

open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.Shops

/-! ## The machine -/

def St (o a nu bc e0 c1 c2 R : List BSym) : Store := fun k =>
  match k with
  | .orig => o | .acc => a | .nu => nu | .bc => bc | .e0 => e0 | .c1 => c1 | .c2 => c2
  | .R => R | .inp => [] | .tmp => [] | .car => [] | .lz => [] | .bad => [] | .sc => []
  | .out => []

def tR (c : Key) : StackProg Key BSym := transferProg c (fun k => decide (k = .R))

def preP : StackProg Key BSym := .seq (copyProg .nu .c1 .sc) countLoop

lemma exec_pre (o a : List BSym) (N : ℕ) :
    ∃ n ≤ 6 * N + 3 + 1 + (N * (6 * (0 + N) + 30) + 1),
      preP.Exec (St o a (List.replicate N .one) [] [] [] [] [])
        (St o a (List.replicate N .one) (enc (Nat.bits N)) [] [] [] []) n := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy .nu .c1 .sc (by decide) (by decide) (by decide)
    (St o a (List.replicate N .one) [] [] [] [] []) rfl
  have h1 : Function.update (St o a (List.replicate N .one) [] [] [] [] []) .c1
      ((St o a (List.replicate N .one) [] [] [] [] []) .nu ++
        (St o a (List.replicate N .one) [] [] [] [] []) .c1) =
      St o a (List.replicate N .one) [] [] (List.replicate N .one) [] [] := by
    funext k; cases k <;> simp [St]
  rw [h1] at e1
  obtain ⟨n2, hn2, e2⟩ := exec_count N 0 (St o a (List.replicate N .one) [] [] (List.replicate N .one) [] [])
    rfl (by simp [St, enc]) rfl rfl rfl rfl
  have h2 : Function.update (Function.update
      (St o a (List.replicate N .one) [] [] (List.replicate N .one) [] []) .c1 []) .bc
      (enc (Nat.bits (0 + N))) = St o a (List.replicate N .one) (enc (Nat.bits N)) [] [] [] [] := by
    funext k; cases k <;> simp [St]
  rw [h2] at e2
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  simp [St] at hn1
  omega

def arith : StackProg Key BSym :=
  .seq (copyProg .acc .c2 .sc) (.seq (copyProg .acc .c1 .sc) (.seq (popAct .acc)
    (.seq (copyProg .acc .e0 .sc) (.seq (addLoop .c1 .e0)
      (transferProg .tmp (fun k => decide (k = .e0)))))))

lemma enc_bits_tail (T : ℕ) : (enc (Nat.bits T)).tail = enc (Nat.bits (T / 2)) := by
  rw [bits_div_two]; simp [enc, List.map_tail]

lemma exec_arith (o nu bc : List BSym) (H : ℕ) :
    ∃ n ≤ 40 * (Nat.bits (2 * H)).length + 40,
      arith.Exec (St o (enc (Nat.bits (2 * H))) nu bc [] [] [] [])
        (St o (enc (Nat.bits H)) nu bc (enc (Nat.bits (3 * H))) [] (enc (Nat.bits (2 * H))) []) n := by
  set A := enc (Nat.bits (2 * H)) with hA
  set Hh := enc (Nat.bits H) with hHh
  have hAt : A.tail = Hh := by rw [hA, enc_bits_tail]; congr 2; omega
  have hHl : Hh.length ≤ A.length := by rw [← hAt]; simp
  obtain ⟨n1, hn1, e1⟩ := exec_copy .acc .c2 .sc (by decide) (by decide) (by decide)
    (St o A nu bc [] [] [] []) rfl
  have h1 : Function.update (St o A nu bc [] [] [] []) .c2
      ((St o A nu bc [] [] [] []) .acc ++ (St o A nu bc [] [] [] []) .c2) = St o A nu bc [] [] A [] := by
    funext k; cases k <;> simp [St]
  rw [h1] at e1
  obtain ⟨n2, hn2, e2⟩ := exec_copy .acc .c1 .sc (by decide) (by decide) (by decide)
    (St o A nu bc [] [] A []) rfl
  have h2 : Function.update (St o A nu bc [] [] A []) .c1
      ((St o A nu bc [] [] A []) .acc ++ (St o A nu bc [] [] A []) .c1) = St o A nu bc [] A A [] := by
    funext k; cases k <;> simp [St]
  rw [h2] at e2
  have e3 := exec_popAct .acc (St o A nu bc [] A A [])
  have h3 : Function.update (St o A nu bc [] A A []) .acc ((St o A nu bc [] A A []) .acc).tail =
      St o Hh nu bc [] A A [] := by
    funext k; cases k <;> simp [St, hAt]
  rw [h3] at e3
  obtain ⟨n4, hn4, e4⟩ := exec_copy .acc .e0 .sc (by decide) (by decide) (by decide)
    (St o Hh nu bc [] A A []) rfl
  have h4 : Function.update (St o Hh nu bc [] A A []) .e0
      ((St o Hh nu bc [] A A []) .acc ++ (St o Hh nu bc [] A A []) .e0) = St o Hh nu bc Hh A A [] := by
    funext k; cases k <;> simp [St]
  rw [h4] at e4
  obtain ⟨n5, hn5, e5⟩ := exec_addLoop .c1 .e0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) [] (by rfl) _ (Nat.bits H) (Nat.bits (2 * H)) false
    (St o Hh nu bc Hh A A []) le_rfl rfl (by simp [St, hA]) rfl (Or.inl rfl)
  have hadd : addB (Nat.bits H) (Nat.bits (2 * H)) false = Nat.bits (3 * H) := by
    rw [← bits_add]; congr 1; omega
  have hlz : lzF (Nat.bits (2 * H)) [] = [] := (lzF_nil_iff _).2 (canon_bits_bval _).1
  have h5 : addPost .c1 .e0 (Nat.bits H) (Nat.bits (2 * H)) false [] (St o Hh nu bc Hh A A []) =
      Function.update (St o Hh nu bc [] [] A []) .tmp (enc (Nat.bits (3 * H))).reverse := by
    funext k; cases k <;> simp [addPost, St, hadd, hlz]
  rw [h5] at e5
  obtain ⟨n6, hn6, e6⟩ := exec_transfer .tmp (fun k => decide (k = .e0)) _
    (Function.update (St o Hh nu bc [] [] A []) .tmp (enc (Nat.bits (3 * H))).reverse) rfl
  have h6 : transferStore .tmp (fun k => decide (k = .e0))
      (Function.update (St o Hh nu bc [] [] A []) .tmp (enc (Nat.bits (3 * H))).reverse) =
      St o Hh nu bc (enc (Nat.bits (3 * H))) [] A [] := by
    funext k; cases k <;> simp [transferStore, St]
  rw [h6] at e6
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 e6))))⟩
  have l3 : (Nat.bits (3 * H)).length ≤ (Nat.bits H).length + (Nat.bits (2 * H)).length + 1 := by
    rw [← hadd]; exact length_addB_le _ _ _
  have hHl' : (Nat.bits H).length ≤ (Nat.bits (2 * H)).length := by
    simpa [hHh, hA, enc] using hHl
  simp only [St, hA, hHh, enc, List.length_map, List.length_append, List.length_nil,
    Function.update_self, List.length_reverse, Bool.toNat_false] at hn1 hn2 hn4 hn5 hn6
  omega

def midP (fl : Bool) : StackProg Key BSym :=
  if fl then .seq (emitNu [.sep]) (tR .orig)
  else .seq (copyProg .orig .c1 .sc) (.seq (tR .orig) (tR .c1))

def midL (fl : Bool) (o : List BSym) (N : ℕ) : List BSym :=
  if fl then (List.replicate N [BSym.sep]).flatten ++ o else o ++ o

lemma exec_tR (c : Key) (hc : c ≠ .R) (s : Store) :
    ∃ n ≤ 3 * (s c).length + 1, (tR c).Exec s
      (Function.update (Function.update s c []) .R ((s c).reverse ++ s .R)) n :=
  exec_transferR c hc s

lemma exec_mid (fl : Bool) (o h bc e c2 R : List BSym) (N : ℕ) :
    ∃ n ≤ 20 * o.length + 20 * N + 20,
      (midP fl).Exec (St o h (List.replicate N .one) bc e [] c2 R)
        (St [] h (List.replicate N .one) bc e [] c2 ((midL fl o N).reverse ++ R)) n := by
  cases fl
  · obtain ⟨n1, hn1, e1⟩ := exec_copy .orig .c1 .sc (by decide) (by decide) (by decide)
      (St o h (List.replicate N .one) bc e [] c2 R) rfl
    have h1 : Function.update (St o h (List.replicate N .one) bc e [] c2 R) .c1
        ((St o h (List.replicate N .one) bc e [] c2 R) .orig ++
          (St o h (List.replicate N .one) bc e [] c2 R) .c1) =
        St o h (List.replicate N .one) bc e o c2 R := by
      funext k; cases k <;> simp [St]
    rw [h1] at e1
    obtain ⟨n2, hn2, e2⟩ := exec_tR .orig (by decide) (St o h (List.replicate N .one) bc e o c2 R)
    have h2 : Function.update (Function.update (St o h (List.replicate N .one) bc e o c2 R) .orig [])
        .R (((St o h (List.replicate N .one) bc e o c2 R) .orig).reverse ++
          (St o h (List.replicate N .one) bc e o c2 R) .R) =
        St [] h (List.replicate N .one) bc e o c2 (o.reverse ++ R) := by
      funext k; cases k <;> simp [St]
    rw [h2] at e2
    obtain ⟨n3, hn3, e3⟩ := exec_tR .c1 (by decide) (St [] h (List.replicate N .one) bc e o c2 (o.reverse ++ R))
    have h3 : Function.update (Function.update
        (St [] h (List.replicate N .one) bc e o c2 (o.reverse ++ R)) .c1 [])
        .R (((St [] h (List.replicate N .one) bc e o c2 (o.reverse ++ R)) .c1).reverse ++
          (St [] h (List.replicate N .one) bc e o c2 (o.reverse ++ R)) .R) =
        St [] h (List.replicate N .one) bc e [] c2 ((midL false o N).reverse ++ R) := by
      funext k; cases k <;> simp [St, midL]
    rw [h3] at e3
    refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)⟩
    simp only [St] at hn1 hn2 hn3
    omega
  · obtain ⟨n1, hn1, e1⟩ := exec_emitNu [BSym.sep] N (St o h (List.replicate N .one) bc e [] c2 R)
      rfl rfl rfl
    have h1 : Function.update (St o h (List.replicate N .one) bc e [] c2 R) .R
        ((List.replicate N [BSym.sep]).flatten.reverse ++ (St o h (List.replicate N .one) bc e [] c2 R) .R) =
        St o h (List.replicate N .one) bc e [] c2 ((List.replicate N [BSym.sep]).flatten.reverse ++ R) := by
      funext k; cases k <;> simp [St]
    rw [h1] at e1
    obtain ⟨n2, hn2, e2⟩ := exec_tR .orig (by decide)
      (St o h (List.replicate N .one) bc e [] c2 ((List.replicate N [BSym.sep]).flatten.reverse ++ R))
    have h2 : Function.update (Function.update
        (St o h (List.replicate N .one) bc e [] c2 ((List.replicate N [BSym.sep]).flatten.reverse ++ R))
        .orig []) .R
        (((St o h (List.replicate N .one) bc e [] c2
          ((List.replicate N [BSym.sep]).flatten.reverse ++ R)) .orig).reverse ++
          (St o h (List.replicate N .one) bc e [] c2
            ((List.replicate N [BSym.sep]).flatten.reverse ++ R)) .R) =
        St [] h (List.replicate N .one) bc e [] c2 ((midL true o N).reverse ++ R) := by
      funext k; cases k <;> simp [St, midL]
    rw [h2] at e2
    refine ⟨_, ?_, StackProg.Exec.seq e1 e2⟩
    simp only [St] at hn2
    simp only [midP, if_true, List.length_cons, List.length_nil] at hn1 ⊢
    omega

end ShopsEnc

set_option autoImplicit false

namespace ShopsEnc

open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.Shops

def outP (fl : Bool) : StackProg Key BSym :=
  .seq (tR .bc) (.seq (pushL [BSym.sep, .one, .sep]) (.seq (midP fl) (.seq (copyProg .acc .c1 .sc)
    (.seq (tR .acc) (.seq (pushL [BSym.sep]) (.seq (tR .c1) (.seq (pushL [BSym.sep])
    (.seq (tR .e0) (.seq (pushL [BSym.sep]) (.seq (tR .c2) (.seq (pushL [BSym.sep])
    (transferProg .R (fun k => decide (k = .out))))))))))))))

lemma len_rep_flat {β : Type} (V : ℕ) (l : List β) :
    (List.replicate V l).flatten.length = V * l.length := by
  induction V with
  | zero => simp
  | succ V ih => simp [List.replicate_succ, ih, Nat.succ_mul]; omega

lemma midL_len (fl : Bool) (o : List BSym) (N : ℕ) : (midL fl o N).length ≤ N + 2 * o.length := by
  cases fl <;> simp [midL, len_rep_flat] <;> omega

lemma exec_outP (fl : Bool) (o h bc e c2 : List BSym) (N : ℕ) :
    ∃ t n, n ≤ 50 * (o.length + h.length + bc.length + e.length + c2.length + N) + 100 ∧
      (outP fl).Exec (St o h (List.replicate N .one) bc e [] c2 []) t n ∧
      t .out = bc ++ [BSym.sep, .one, .sep] ++ midL fl o N ++ h ++ [BSym.sep] ++ h ++ [BSym.sep] ++
        e ++ [BSym.sep] ++ c2 ++ [BSym.sep] := by
  set nu := List.replicate N BSym.one with hnu
  -- 1
  obtain ⟨n1, hn1, e1⟩ := exec_tR .bc (by decide) (St o h nu bc e [] c2 [])
  rw [show Function.update (Function.update (St o h nu bc e [] c2 []) .bc []) .R
      (((St o h nu bc e [] c2 []) .bc).reverse ++ (St o h nu bc e [] c2 []) .R) =
      St o h nu [] e [] c2 bc.reverse from by funext k; cases k <;> simp [St]] at e1
  -- 2
  have e2 := exec_pushL [BSym.sep, .one, .sep] (St o h nu [] e [] c2 bc.reverse)
  rw [show Function.update (St o h nu [] e [] c2 bc.reverse) .R
      ([BSym.sep, .one, .sep].reverse ++ (St o h nu [] e [] c2 bc.reverse) .R) =
      St o h nu [] e [] c2 (bc ++ [BSym.sep, .one, .sep]).reverse from by
        funext k; cases k <;> simp [St]] at e2
  -- 3
  obtain ⟨n3, hn3, e3⟩ := exec_mid fl o h [] e c2 (bc ++ [BSym.sep, .one, .sep]).reverse N
  set X3 := bc ++ [BSym.sep, .one, .sep] ++ midL fl o N with hX3
  rw [show (midL fl o N).reverse ++ (bc ++ [BSym.sep, .one, .sep]).reverse = X3.reverse from by
    simp [hX3]] at e3
  -- 4
  obtain ⟨n4, hn4, e4⟩ := exec_copy .acc .c1 .sc (by decide) (by decide) (by decide)
    (St [] h nu [] e [] c2 X3.reverse) rfl
  rw [show Function.update (St [] h nu [] e [] c2 X3.reverse) .c1
      ((St [] h nu [] e [] c2 X3.reverse) .acc ++ (St [] h nu [] e [] c2 X3.reverse) .c1) =
      St [] h nu [] e h c2 X3.reverse from by funext k; cases k <;> simp [St]] at e4
  -- 5
  obtain ⟨n5, hn5, e5⟩ := exec_tR .acc (by decide) (St [] h nu [] e h c2 X3.reverse)
  rw [show Function.update (Function.update (St [] h nu [] e h c2 X3.reverse) .acc []) .R
      (((St [] h nu [] e h c2 X3.reverse) .acc).reverse ++ (St [] h nu [] e h c2 X3.reverse) .R) =
      St [] [] nu [] e h c2 (X3 ++ h).reverse from by funext k; cases k <;> simp [St]] at e5
  -- 6
  have e6 := exec_pushL [BSym.sep] (St [] [] nu [] e h c2 (X3 ++ h).reverse)
  rw [show Function.update (St [] [] nu [] e h c2 (X3 ++ h).reverse) .R
      ([BSym.sep].reverse ++ (St [] [] nu [] e h c2 (X3 ++ h).reverse) .R) =
      St [] [] nu [] e h c2 (X3 ++ h ++ [BSym.sep]).reverse from by
        funext k; cases k <;> simp [St]] at e6
  -- 7
  obtain ⟨n7, hn7, e7⟩ := exec_tR .c1 (by decide) (St [] [] nu [] e h c2 (X3 ++ h ++ [BSym.sep]).reverse)
  rw [show Function.update (Function.update (St [] [] nu [] e h c2 (X3 ++ h ++ [BSym.sep]).reverse)
      .c1 []) .R (((St [] [] nu [] e h c2 (X3 ++ h ++ [BSym.sep]).reverse) .c1).reverse ++
        (St [] [] nu [] e h c2 (X3 ++ h ++ [BSym.sep]).reverse) .R) =
      St [] [] nu [] e [] c2 (X3 ++ h ++ [BSym.sep] ++ h).reverse from by
        funext k; cases k <;> simp [St]] at e7
  -- 8
  have e8 := exec_pushL [BSym.sep] (St [] [] nu [] e [] c2 (X3 ++ h ++ [BSym.sep] ++ h).reverse)
  rw [show Function.update (St [] [] nu [] e [] c2 (X3 ++ h ++ [BSym.sep] ++ h).reverse) .R
      ([BSym.sep].reverse ++ (St [] [] nu [] e [] c2 (X3 ++ h ++ [BSym.sep] ++ h).reverse) .R) =
      St [] [] nu [] e [] c2 (X3 ++ h ++ [BSym.sep] ++ h ++ [BSym.sep]).reverse from by
        funext k; cases k <;> simp [St]] at e8
  set X8 := X3 ++ h ++ [BSym.sep] ++ h ++ [BSym.sep] with hX8
  -- 9
  obtain ⟨n9, hn9, e9⟩ := exec_tR .e0 (by decide) (St [] [] nu [] e [] c2 X8.reverse)
  rw [show Function.update (Function.update (St [] [] nu [] e [] c2 X8.reverse) .e0 []) .R
      (((St [] [] nu [] e [] c2 X8.reverse) .e0).reverse ++ (St [] [] nu [] e [] c2 X8.reverse) .R) =
      St [] [] nu [] [] [] c2 (X8 ++ e).reverse from by funext k; cases k <;> simp [St]] at e9
  -- 10
  have e10 := exec_pushL [BSym.sep] (St [] [] nu [] [] [] c2 (X8 ++ e).reverse)
  rw [show Function.update (St [] [] nu [] [] [] c2 (X8 ++ e).reverse) .R
      ([BSym.sep].reverse ++ (St [] [] nu [] [] [] c2 (X8 ++ e).reverse) .R) =
      St [] [] nu [] [] [] c2 (X8 ++ e ++ [BSym.sep]).reverse from by
        funext k; cases k <;> simp [St]] at e10
  -- 11
  obtain ⟨n11, hn11, e11⟩ := exec_tR .c2 (by decide) (St [] [] nu [] [] [] c2 (X8 ++ e ++ [BSym.sep]).reverse)
  rw [show Function.update (Function.update (St [] [] nu [] [] [] c2 (X8 ++ e ++ [BSym.sep]).reverse)
      .c2 []) .R (((St [] [] nu [] [] [] c2 (X8 ++ e ++ [BSym.sep]).reverse) .c2).reverse ++
        (St [] [] nu [] [] [] c2 (X8 ++ e ++ [BSym.sep]).reverse) .R) =
      St [] [] nu [] [] [] [] (X8 ++ e ++ [BSym.sep] ++ c2).reverse from by
        funext k; cases k <;> simp [St]] at e11
  -- 12
  have e12 := exec_pushL [BSym.sep] (St [] [] nu [] [] [] [] (X8 ++ e ++ [BSym.sep] ++ c2).reverse)
  rw [show Function.update (St [] [] nu [] [] [] [] (X8 ++ e ++ [BSym.sep] ++ c2).reverse) .R
      ([BSym.sep].reverse ++ (St [] [] nu [] [] [] [] (X8 ++ e ++ [BSym.sep] ++ c2).reverse) .R) =
      St [] [] nu [] [] [] [] (X8 ++ e ++ [BSym.sep] ++ c2 ++ [BSym.sep]).reverse from by
        funext k; cases k <;> simp [St]] at e12
  set X := X8 ++ e ++ [BSym.sep] ++ c2 ++ [BSym.sep] with hX
  -- 13
  obtain ⟨n13, hn13, e13⟩ := exec_transfer .R (fun k => decide (k = .out)) _
    (St [] [] nu [] [] [] [] X.reverse) rfl
  refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10 (StackProg.Exec.seq e11
    (StackProg.Exec.seq e12 e13))))))))))), ?_⟩
  · have hm := midL_len fl o N
    simp only [St, List.length_reverse, List.length_append, List.length_cons, List.length_nil,
      hX, hX8, hX3] at hn1 hn3 hn4 hn5 hn7 hn9 hn11 hn13 ⊢
    omega
  · simp [transferStore, St, hX, hX8, hX3]

def mainProg (fl : Bool) : StackProg Key BSym :=
  .seq (copyProg .inp .orig .sc)
    (.seq parseLoop
      (.branch (fun h => (h .bad).isSome) skipP
        (.branch (fun h => decide (h .acc = some .one)) skipP
          (.seq preP (.seq arith (outP fl))))))

lemma enc_bits_head (T : ℕ) : (enc (Nat.bits T)).head? = some BSym.one ↔ T % 2 = 1 := by
  rcases Nat.even_or_odd' T with ⟨H, rfl | rfl⟩
  · by_cases hH : H = 0
    · subst hH; simp [enc]
    · have hb := Nat.bits_append_bit H false (fun h => absurd h hH)
      rw [Nat.bit_val] at hb
      simp only [Bool.toNat_false, add_zero] at hb
      rw [hb]; simp [enc, toB]
  · have hb := Nat.bits_append_bit H true (fun _ => rfl)
    rw [Nat.bit_val] at hb
    simp only [Bool.toNat_true] at hb
    rw [hb]; simp [enc, toB] <;> omega

end ShopsEnc

set_option autoImplicit false

namespace ShopsEnc

open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.Shops

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

lemma absorb2000 (L : ℕ) : 400 * (L + 1) ^ 2 + 400 ≤ L ^ 2000 + 2000 := by
  rcases L with _ | _ | L
  · norm_num
  · norm_num
  · have key : 400 * (L + 1 + 1 + 1) ^ 2 + 400 ≤ (L + 2) ^ 14 := by
      have h1 : 2 ^ 12 ≤ (L + 2) ^ 12 := Nat.pow_le_pow_left (by omega) 12
      have h2 : (L + 2) ^ 14 = (L + 2) ^ 2 * (L + 2) ^ 12 := by ring
      have h4 : (L + 1 + 1 + 1) ^ 2 ≤ 4 * (L + 2) ^ 2 := by
        have h : L + 1 + 1 + 1 ≤ 2 * (L + 2) := by omega
        calc (L + 1 + 1 + 1) ^ 2 ≤ (2 * (L + 2)) ^ 2 := Nat.pow_le_pow_left h 2
          _ = 4 * (L + 2) ^ 2 := by ring
      have h5 : 1 ≤ (L + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [h2]
      generalize (L + 2) ^ 12 = X at h1
      generalize (L + 1 + 1 + 1) ^ 2 = Z at h4 ⊢
      generalize (L + 2) ^ 2 = Y at h4 h5 ⊢
      have hYX : Y * 4096 ≤ Y * X := Nat.mul_le_mul_left _ (by simpa using h1)
      omega
    have h3 : (L + 2) ^ 14 ≤ (L + 2) ^ 2000 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc 400 * (L + 1 + 1 + 1) ^ 2 + 400 ≤ (L + 2) ^ 14 := key
      _ ≤ (L + 2) ^ 2000 := h3
      _ ≤ (L + 1 + 1) ^ 2000 + 2000 := Nat.le_add_right _ _

lemma bound_small (L n1 n2 : ℕ) (h1 : n1 ≤ 6 * L + 3) (h2 : n2 ≤ (L + 1) * (12 * L + 20) + 1) :
    n1 + 1 + (n2 + 1 + (1 + (1 + 1))) ≤ 400 * (L + 1) ^ 2 + 400 := by nlinarith

lemma bound_main (L N n1 n2 n3 n4 n5 bT bH b3 bN : ℕ) (hN : N ≤ L) (hT : bT ≤ L) (hH : bH ≤ bT)
    (h3 : b3 ≤ bH + bT + 1) (hbN : bN ≤ N) (h1 : n1 ≤ 6 * L + 3)
    (h2 : n2 ≤ (L + 1) * (12 * L + 20) + 1)
    (h3' : n3 ≤ 6 * N + 3 + 1 + (N * (6 * (0 + N) + 30) + 1)) (h4 : n4 ≤ 40 * bT + 40)
    (h5 : n5 ≤ 50 * (L + bH + bN + b3 + bT + N) + 100) :
    n1 + 1 + (n2 + 1 + (1 + (1 + (n3 + 1 + (n4 + 1 + n5))))) ≤ 400 * (L + 1) ^ 2 + 400 := by
  nlinarith [Nat.mul_le_mul hN hN]

lemma exec_main (fl : Bool) (w : List BSym) : ∃ t n, n ≤ 400 * (w.length + 1) ^ 2 + 400 ∧
    (mainProg fl).Exec (fun j => if j = .inp then w else []) t n ∧ t .out = Fr fl w := by
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
    set N := sl.length with hN
    set T := sl.sum with hT
    have htSt : PS sa [] (enc (Nat.bits (0 + T))) (List.replicate N .one ++ []) [] [] [] =
        St w (enc (Nat.bits T)) (List.replicate N .one) [] [] [] [] [] := by
      funext k; cases k <;> simp [PS, St, hsa, hs0]
    rw [htSt] at e2
    have hbr : (fun h : Key → Option BSym => (h .bad).isSome)
        (fun k => (St w (enc (Nat.bits T)) (List.replicate N .one) [] [] [] [] [] k).head?) = false := by
      simp [St]
    have hNL : N ≤ w.length := by rw [hsl]; exact len_sl sl
    have hTL : (Nat.bits T).length ≤ w.length := by
      have := len_bits_sum sl 0; simp at this; rw [hsl]; simpa [hT] using this
    by_cases hodd : T % 2 = 1
    · have hpar : (fun h : Key → Option BSym => decide (h .acc = some .one))
          (fun k => (St w (enc (Nat.bits T)) (List.replicate N .one) [] [] [] [] [] k).head?) = true := by
        simp only [St]; exact decide_eq_true ((enc_bits_head T).2 hodd)
      refine ⟨_, n1 + 1 + (n2 + 1 + (1 + (1 + 1))), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
        (StackProg.Exec.branchFalse hbr (StackProg.Exec.branchTrue hpar (exec_skip _)))), ?_⟩
      · exact bound_small _ _ _ hn1' hn2
      · rw [hsl, Fr_valid, if_neg (by omega)]; rfl
    · have hpar : (fun h : Key → Option BSym => decide (h .acc = some .one))
          (fun k => (St w (enc (Nat.bits T)) (List.replicate N .one) [] [] [] [] [] k).head?) = false := by
        simp only [St]; exact decide_eq_false (fun h => hodd ((enc_bits_head T).1 h))
      set H := T / 2 with hH
      have hT2 : T = 2 * H := by omega
      obtain ⟨n3, hn3, e3⟩ := exec_pre w (enc (Nat.bits T)) N
      obtain ⟨n4, hn4, e4⟩ := exec_arith w (List.replicate N .one) (enc (Nat.bits N)) H
      rw [← hT2] at e4 hn4
      obtain ⟨t5, n5, hn5, e5, hout⟩ := exec_outP fl w (enc (Nat.bits H)) (enc (Nat.bits N))
        (enc (Nat.bits (3 * H))) (enc (Nat.bits T)) N
      refine ⟨t5, n1 + 1 + (n2 + 1 + (1 + (1 + (n3 + 1 + (n4 + 1 + n5))))), ?_,
        StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.branchFalse hbr
          (StackProg.Exec.branchFalse hpar (StackProg.Exec.seq e3 (StackProg.Exec.seq e4 e5))))), ?_⟩
      · have hHl : (Nat.bits H).length ≤ (Nat.bits T).length := by
          rw [hH, bits_div_two]; simp
        have h3l : (Nat.bits (3 * H)).length ≤ (Nat.bits H).length + (Nat.bits (2 * H)).length + 1 := by
          rw [show 3 * H = H + 2 * H by omega, bits_add]; exact length_addB_le _ _ _
        have hbN : (Nat.bits N).length ≤ N := len_bits_le N
        rw [← hT2] at h3l
        simp only [enc, List.length_map] at hn5
        exact bound_main _ _ _ _ _ _ _ _ _ _ _ hNL hTL hHl h3l hbN hn1' hn2 hn3 hn4 hn5
      · rw [hout, hsl, Fr_valid, if_pos (by omega), outF_spec]
        have hm : midL fl (encNats sl) N = midOut fl sl := by cases fl <;> rfl
        rw [hm, ← hT, ← hH, ← hN]
  · obtain ⟨i', a', nu', z', rfl⟩ := hinv (fun sl h => hw ⟨sl, h⟩)
    refine ⟨_, n1 + 1 + (n2 + 1 + (1 + 1)), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.branchTrue (by simp [PS]) (exec_skip _))), ?_⟩
    · have := bound_small _ _ _ hn1' hn2; omega
    · rw [Fr_invalid fl hw]; simp [PS, hsa, hs0]

theorem Fr_exec (fl : Bool) (w : List BSym) : ∃ s n, n ≤ w.length ^ 2000 + 2000 ∧
    (mainProg fl).Exec (fun j => if j = .inp then w else []) s n ∧ s .out = Fr fl w := by
  obtain ⟨t, n, hn, e, ho⟩ := exec_main fl w
  exact ⟨t, n, le_trans hn (absorb2000 _), e, ho⟩

end ShopsEnc

open TwoAgentSched.Shops CookPvsNP ProjSchedTW.Complexity in
theorem solution :
    (∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ p : List ℕ, Even p.sum ∧ (2 ≤ p.sum ∨ p.length ≤ 1) ∧
            (flowInst p).FlowYes (flowQA p) (flowQB p) ∧ x = encNats p) ∨
          (∃ p : List ℕ, p.sum = 0 ∧ x = encNats p)) ↔ f x ∈ flowLang) ∧
    (∃ g : List BSym → List BSym, PolyTimeComputable g ∧
      ∀ x : List BSym,
        (∃ p : List ℕ, (openInst p).OpenYes (openQA p) (openQB p) ∧ x = encNats p) ↔
          g x ∈ openLang) :=
  ⟨⟨ShopsEnc.Fr true, stack_program_polytime (ShopsEnc.mainProg true) .inp .out
      (ShopsEnc.Fr true) 2000 (ShopsEnc.Fr_exec true), ShopsEnc.flow_correct⟩,
   ⟨ShopsEnc.Fr false, stack_program_polytime (ShopsEnc.mainProg false) .inp .out
      (ShopsEnc.Fr false) 2000 (ShopsEnc.Fr_exec false), ShopsEnc.open_correct⟩⟩

