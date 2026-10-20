-- Prove2me | solution 1 for ProjSchedTW.Complexity.partition_polyReducible_cumFeas
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T17:06:49.099155+00:00
-- url     : https://prove2.me/submissions/3bfa2ccd-8c09-48d8-9782-e58a4ffcce15

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_Cumulative
import Theorems.Thm_CookPvsNP_stack_program_polytime

set_option autoImplicit false

namespace P5c6

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

/-- the middle rows of the arc matrix. -/
def midRow (V : ℕ) : List BSym :=
  [BSym.sep, .sep] ++ (List.replicate V [BSym.sep, .sep]).flatten ++ [BSym.one, .sep, .sep]

def midBody : StackProg Key BSym :=
  .seq (popAct .c2) (.seq (pushL [BSym.sep, .sep]) (.seq (emitNu [BSym.sep, .sep]) (pushL [BSym.one, .sep, .sep])))

def midLoop : StackProg Key BSym := .loop (fun h => (h .c2).isSome) midBody

lemma exec_midLoop (V : ℕ) : ∀ (M : ℕ) (s : Store), s .c2 = List.replicate M .one →
    s .nu = List.replicate V .one → s .c1 = [] → s .sc = [] →
    ∃ n ≤ M * (16 * V + 30) + 1, midLoop.Exec s
      (Function.update (Function.update s .c2 []) .R
        ((List.replicate M (midRow V)).flatten.reverse ++ s .R)) n := by
  intro M
  induction M with
  | zero =>
    intro s hs _ _ _
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update s .c2 []) .R
        ((List.replicate 0 (midRow V)).flatten.reverse ++ s .R) = s := by
      funext k
      by_cases h1 : k = .R
      · subst h1; simp
      by_cases h2 : k = .c2
      · subst h2; simp [h1, hs]
      · simp [h1, h2]
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | succ M ih =>
    intro s hs hnu hc1 hsc
    set s1 := Function.update s .c2 (s .c2).tail with hs1
    set s2 := Function.update s1 .R ([BSym.sep, .sep].reverse ++ s1 .R) with hs2
    obtain ⟨n3, hn3, e3⟩ := exec_emitNu [BSym.sep, .sep] V s2 (by simp [hs2, hs1, hnu])
      (by simp [hs2, hs1, hc1]) (by simp [hs2, hs1, hsc])
    set s3 := Function.update s2 .R ((List.replicate V [BSym.sep, .sep]).flatten.reverse ++ s2 .R)
      with hs3
    set s4 := Function.update s3 .R ([BSym.one, .sep, .sep].reverse ++ s3 .R) with hs4
    have eb : midBody.Exec s s4 (1 + 1 + ((2 * 2 + 1) + 1 + (n3 + 1 + (2 * 3 + 1)))) :=
      StackProg.Exec.seq (exec_popAct .c2 s) (StackProg.Exec.seq (exec_pushL _ s1)
        (StackProg.Exec.seq e3 (exec_pushL _ s3)))
    obtain ⟨m, hm, ex⟩ := ih s4 (by simp [hs4, hs3, hs2, hs1, hs, List.replicate_succ])
      (by simp [hs4, hs3, hs2, hs1, hnu]) (by simp [hs4, hs3, hs2, hs1, hc1])
      (by simp [hs4, hs3, hs2, hs1, hsc])
    have hfin : Function.update (Function.update s4 .c2 []) .R
        ((List.replicate M (midRow V)).flatten.reverse ++ s4 .R) =
        Function.update (Function.update s .c2 []) .R
          ((List.replicate (M + 1) (midRow V)).flatten.reverse ++ s .R) := by
      funext k
      by_cases h1 : k = .R
      · subst h1; simp [hs4, hs3, hs2, hs1, List.replicate_succ, midRow]
      by_cases h2 : k = .c2
      · subst h2; simp [h1]
      · simp [h1, h2, hs4, hs3, hs2, hs1]
    rw [hfin] at ex
    refine ⟨1 + (1 + 1 + ((2 * 2 + 1) + 1 + (n3 + 1 + (2 * 3 + 1)))) + 1 + m, ?_,
      StackProg.Exec.loopTrue (by simp [hs, List.replicate_succ]) eb ex⟩
    have : (M + 1) * (16 * V + 30) =
        M * (16 * V + 30) + (16 * V + 30) := by ring
    simp only [List.length_cons, List.length_nil] at hn3
    omega

/-! ## R-only phases -/

def mn (l : List BSym) : List BSym := if l = [] then [] else [.minus]

lemma len_rep_flat {β : Type} (V : ℕ) (l : List β) :
    (List.replicate V l).flatten.length = V * l.length := by
  induction V with
  | zero => simp
  | succ V ih => simp [List.replicate_succ, ih, Nat.succ_mul]; omega

lemma len_mn (l : List BSym) : (mn l).length ≤ 1 := by
  unfold mn; split_ifs <;> simp

def ROnly (P : StackProg Key BSym) (X : List BSym) (B : ℕ) (s : Store) : Prop :=
  ∃ n ≤ B, P.Exec s (Function.update s .R (X.reverse ++ s .R)) n

lemma ro_seq {P Q : StackProg Key BSym} {X Y : List BSym} {B B' : ℕ} {s : Store}
    (h1 : ROnly P X B s) (h2 : ROnly Q Y B' (Function.update s .R (X.reverse ++ s .R))) :
    ROnly (.seq P Q) (X ++ Y) (B + 1 + B') s := by
  obtain ⟨n, hn, e1⟩ := h1
  obtain ⟨m, hm, e2⟩ := h2
  have : Function.update (Function.update s .R (X.reverse ++ s .R)) .R
      (Y.reverse ++ (Function.update s .R (X.reverse ++ s .R)) .R) =
      Function.update s .R ((X ++ Y).reverse ++ s .R) := by simp
  rw [this] at e2
  exact ⟨n + 1 + m, by omega, StackProg.Exec.seq e1 e2⟩

lemma ro_pushL (P : List BSym) (s : Store) : ROnly (pushL P) P (2 * P.length + 1) s :=
  ⟨_, le_rfl, exec_pushL P s⟩

lemma ro_emitNu (P : List BSym) (V : ℕ) (s : Store) (hnu : s .nu = List.replicate V .one)
    (hc1 : s .c1 = []) (hsc : s .sc = []) :
    ROnly (emitNu P) (List.replicate V P).flatten (6 * V + 3 + 1 + (V * (2 * P.length + 5) + 1)) s :=
  exec_emitNu P V s hnu hc1 hsc

def midPhase : StackProg Key BSym := .seq (copyProg .nu .c2 .sc) midLoop

lemma ro_midPhase (V : ℕ) (s : Store) (hnu : s .nu = List.replicate V .one)
    (hc1 : s .c1 = []) (hc2 : s .c2 = []) (hsc : s .sc = []) :
    ROnly midPhase (List.replicate V (midRow V)).flatten
      (6 * V + 3 + 1 + (V * (16 * V + 30) + 1)) s := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy .nu .c2 .sc (by decide) (by decide) (by decide) s hsc
  rw [hnu, hc2, List.append_nil] at e1
  obtain ⟨n2, hn2, e2⟩ := exec_midLoop V V (Function.update s .c2 (List.replicate V .one))
    (by simp) (by simp [hnu]) (by simp [hc1]) (by simp [hsc])
  have hfin : Function.update (Function.update (Function.update s .c2 (List.replicate V .one)) .c2 [])
      .R ((List.replicate V (midRow V)).flatten.reverse ++
        (Function.update s .c2 (List.replicate V .one)) .R) =
      Function.update s .R ((List.replicate V (midRow V)).flatten.reverse ++ s .R) := by
    funext k
    by_cases h1 : k = .R
    · subst h1; simp
    by_cases h2 : k = .c2
    · subst h2; simp [hc2]
    · simp [h1, h2]
  rw [hfin] at e2
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  simp only [hnu, List.length_replicate] at hn1
  omega

def minusIf (c : Key) : StackProg Key BSym := .branch (fun h => (h c).isSome) (pushR .minus) skipP

lemma ro_minusIf (c : Key) (s : Store) : ROnly (minusIf c) (mn (s c)) 2 s := by
  by_cases h : s c = []
  · refine ⟨1 + 1, le_rfl, ?_⟩
    have : Function.update s .R ((mn (s c)).reverse ++ s .R) = s := by simp [mn, h]
    rw [this]
    exact StackProg.Exec.branchFalse (by simp [h]) (exec_skip s)
  · refine ⟨1 + 1, le_rfl, ?_⟩
    have : Function.update s .R ((mn (s c)).reverse ++ s .R) =
        Function.update s .R (.minus :: s .R) := by simp [mn, h]
    rw [this]
    refine StackProg.Exec.branchTrue ?_ (exec_pushR .minus s)
    cases hc : s c with
    | nil => exact absurd hc h
    | cons _ _ => simp [hc]

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

/-! ## the output program -/

def rPart : StackProg Key BSym :=
  .seq (popAct .acc) (.seq (copyProg .acc .e0 .sc) (.seq (minusIf .acc)
    (.seq (transferProg .acc (fun k => decide (k = .R))) (.seq (pushL [BSym.sep, .sep])
    (.seq (transferProg .orig (fun k => decide (k = .R))) (.seq (minusIf .e0)
    (.seq (transferProg .e0 (fun k => decide (k = .R))) (pushL [BSym.sep, .sep, .sep]))))))))

lemma exec_rPart (s : Store) (he0 : s .e0 = []) (hsc : s .sc = []) :
    ∃ t n, n ≤ 12 * (s .acc).length + 3 * (s .orig).length + 40 ∧ rPart.Exec s t n ∧
      t .R = (mn (s .acc).tail ++ (s .acc).tail ++ [BSym.sep, .sep] ++ s .orig ++
        mn (s .acc).tail ++ (s .acc).tail ++ [BSym.sep, .sep, .sep]).reverse ++ s .R ∧
      t .out = s .out := by
  set a := (s .acc).tail with ha
  have e1 := exec_popAct .acc s
  set s1 := Function.update s .acc a with hs1
  obtain ⟨n2, hn2, e2⟩ := exec_copy .acc .e0 .sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 .e0 (s1 .acc ++ s1 .e0) with hs2
  obtain ⟨n3, hn3, e3⟩ := ro_minusIf .acc s2
  set s3 := Function.update s2 .R ((mn (s2 .acc)).reverse ++ s2 .R) with hs3
  obtain ⟨n4, hn4, e4⟩ := exec_transferR .acc (by decide) s3
  set s4 := Function.update (Function.update s3 .acc []) .R ((s3 .acc).reverse ++ s3 .R) with hs4
  have e5 := exec_pushL [BSym.sep, .sep] s4
  set s5 := Function.update s4 .R ([BSym.sep, .sep].reverse ++ s4 .R) with hs5
  obtain ⟨n6, hn6, e6⟩ := exec_transferR .orig (by decide) s5
  set s6 := Function.update (Function.update s5 .orig []) .R ((s5 .orig).reverse ++ s5 .R) with hs6
  obtain ⟨n7, hn7, e7⟩ := ro_minusIf .e0 s6
  set s7 := Function.update s6 .R ((mn (s6 .e0)).reverse ++ s6 .R) with hs7
  obtain ⟨n8, hn8, e8⟩ := exec_transferR .e0 (by decide) s7
  set s8 := Function.update (Function.update s7 .e0 []) .R ((s7 .e0).reverse ++ s7 .R) with hs8
  have e9 := exec_pushL [BSym.sep, .sep, .sep] s8
  refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 e9))))))), ?_, ?_⟩
  · have la : a.length ≤ (s .acc).length := by rw [ha]; simp
    simp only [hs1, hs2, hs3, hs4, hs5, hs6, hs7, Function.update_self, ne_eq,
      reduceCtorEq, not_false_eq_true, Function.update_of_ne, he0, List.append_nil,
      List.length_reverse, List.length_append, List.length_cons, List.length_nil] at hn2 hn4 hn6 hn8 ⊢
    omega
  · simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, he0]
  · simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8]

/-- the arc matrix rows, in output order. -/
def row0 (V : ℕ) : List BSym :=
  [BSym.sep, .sep] ++ (List.replicate V [BSym.one, .sep, .sep]).flatten ++ [BSym.one, .sep, .one, .sep]

def rowL (V : ℕ) : List BSym :=
  [BSym.sep, .sep] ++ (List.replicate V [BSym.sep, .sep]).flatten ++ [BSym.sep, .sep]

def roChunk : StackProg Key BSym :=
  .seq (pushL [BSym.sep, .one, .sep, .sep]) (.seq (emitNu [BSym.sep]) (.seq (pushL [BSym.sep, .sep, .sep])
    (.seq (emitNu [BSym.one, .sep, .sep]) (.seq (pushL [BSym.one, .sep, .one, .sep]) (.seq midPhase
    (.seq (pushL [BSym.sep, .sep]) (.seq (emitNu [BSym.sep, .sep]) (pushL [BSym.sep, .sep]))))))))

def roBound (V : ℕ) : ℕ := V * (16 * V + 30) + 60 * V + 100

lemma ro_roChunk (V : ℕ) (s : Store) (hnu : s .nu = List.replicate V .one)
    (hc1 : s .c1 = []) (hc2 : s .c2 = []) (hsc : s .sc = []) :
    ROnly roChunk ([BSym.sep, .one, .sep, .sep] ++ (List.replicate V [BSym.sep]).flatten ++
      [BSym.sep, .sep, .sep] ++ (List.replicate V [BSym.one, .sep, .sep]).flatten ++
      [BSym.one, .sep, .one, .sep] ++ (List.replicate V (midRow V)).flatten ++ [BSym.sep, .sep] ++
      (List.replicate V [BSym.sep, .sep]).flatten ++ [BSym.sep, .sep]) (roBound V) s := by
  have h := ro_seq (ro_pushL [BSym.sep, .one, .sep, .sep] s) (ro_seq (ro_emitNu [BSym.sep] V _
    (by simp [hnu]) (by simp [hc1]) (by simp [hsc])) (ro_seq (ro_pushL [BSym.sep, .sep, .sep] _)
    (ro_seq (ro_emitNu [BSym.one, .sep, .sep] V _ (by simp [hnu]) (by simp [hc1]) (by simp [hsc]))
    (ro_seq (ro_pushL [BSym.one, .sep, .one, .sep] _) (ro_seq (ro_midPhase V _ (by simp [hnu])
    (by simp [hc1]) (by simp [hc2]) (by simp [hsc])) (ro_seq (ro_pushL [BSym.sep, .sep] _)
    (ro_seq (ro_emitNu [BSym.sep, .sep] V _ (by simp [hnu]) (by simp [hc1]) (by simp [hsc]))
    (ro_pushL [BSym.sep, .sep] _))))))))
  obtain ⟨n, hn, e⟩ := h
  refine ⟨n, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil] at hn
    unfold roBound; nlinarith
  · simpa only [roChunk, List.append_assoc] using e

def outProg : StackProg Key BSym :=
  .seq (transferProg .bc (fun k => decide (k = .R))) (.seq roChunk
    (.seq rPart (transferProg .R (fun k => decide (k = .out)))))

lemma exec_outProg (V : ℕ) (s : Store) (hR : s .R = []) (hc1 : s .c1 = []) (hc2 : s .c2 = [])
    (hsc : s .sc = []) (he0 : s .e0 = []) (hnu : s .nu = List.replicate V .one)
    (hout : s .out = []) :
    ∃ t n, n ≤ 3 * (s .bc).length + 12 * (s .acc).length + 3 * (s .orig).length + roBound V +
        3 * ((s .bc).length + 4 * V * V + 30 * V + 2 * (s .acc).length + (s .orig).length + 60) + 100 ∧
      outProg.Exec s t n ∧
      t .out = s .bc ++ ([BSym.sep, .one, .sep, .sep] ++ (List.replicate V [BSym.sep]).flatten ++
      [BSym.sep, .sep, .sep] ++ (List.replicate V [BSym.one, .sep, .sep]).flatten ++
      [BSym.one, .sep, .one, .sep] ++ (List.replicate V (midRow V)).flatten ++ [BSym.sep, .sep] ++
      (List.replicate V [BSym.sep, .sep]).flatten ++ [BSym.sep, .sep]) ++
      (mn (s .acc).tail ++ (s .acc).tail ++ [BSym.sep, .sep] ++ s .orig ++
        mn (s .acc).tail ++ (s .acc).tail ++ [BSym.sep, .sep, .sep]) := by
  set X : List BSym := [BSym.sep, .one, .sep, .sep] ++ (List.replicate V [BSym.sep]).flatten ++
      [BSym.sep, .sep, .sep] ++ (List.replicate V [BSym.one, .sep, .sep]).flatten ++
      [BSym.one, .sep, .one, .sep] ++ (List.replicate V (midRow V)).flatten ++ [BSym.sep, .sep] ++
      (List.replicate V [BSym.sep, .sep]).flatten ++ [BSym.sep, .sep] with hX
  obtain ⟨n1, hn1, e1⟩ := exec_transferR .bc (by decide) s
  set s1 := Function.update (Function.update s .bc []) .R ((s .bc).reverse ++ s .R) with hs1
  obtain ⟨n2, hn2, e2⟩ := ro_roChunk V s1 (by simp [hs1, hnu]) (by simp [hs1, hc1])
    (by simp [hs1, hc2]) (by simp [hs1, hsc])
  rw [← hX] at e2
  set s2 := Function.update s1 .R (X.reverse ++ s1 .R) with hs2
  obtain ⟨t3, n3, hn3, e3, h3R, h3out⟩ := exec_rPart s2 (by simp [hs2, hs1, he0])
    (by simp [hs2, hs1, hsc])
  obtain ⟨n4, hn4, e4⟩ := exec_transfer .R (fun k => decide (k = .out)) (t3 .R) t3 rfl
  have h2acc : s2 .acc = s .acc := by simp [hs2, hs1]
  have h2orig : s2 .orig = s .orig := by simp [hs2, hs1]
  have h2R : s2 .R = X.reverse ++ (s .bc).reverse := by simp [hs2, hs1, hR]
  have h2out : s2 .out = [] := by simp [hs2, hs1, hout]
  rw [h2acc, h2orig, h2R] at h3R
  refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 e4)), ?_⟩
  · have hXl : X.length ≤ 4 * V * V + 30 * V + 60 := by
      simp only [hX, midRow, List.length_append, len_rep_flat, List.length_cons, List.length_nil]
      nlinarith
    have hm := len_mn (s .acc).tail
    have hal : (s .acc).tail.length ≤ (s .acc).length := by simp
    rw [h3R] at hn4
    simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil] at hn4
    rw [h2acc, h2orig] at hn3
    omega
  · simp only [transferStore, if_true, h3R, h3out, h2out, decide_true]
    simp [hX]


/-! ## encInts algebra -/

lemma encInts_cons (z : ℤ) (l : List ℤ) : encInts (z :: l) = encInt z ++ encInts l := by
  simp [encInts]

lemma encInts_append (l l' : List ℤ) : encInts (l ++ l') = encInts l ++ encInts l' := by
  simp [encInts]

lemma encInts_flatten (L : List (List ℤ)) : encInts L.flatten = (L.map encInts).flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [encInts_append, ih]

lemma encInts_replicate_flatten (V : ℕ) (l : List ℤ) :
    encInts (List.replicate V l).flatten = (List.replicate V (encInts l)).flatten := by
  rw [encInts_flatten, List.map_replicate]

lemma encInts_natCast (l : List ℕ) : encInts (l.map (fun k : ℕ => (k : ℤ))) = encNats l := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.map_cons, encInts_cons, ih]
    simp [encInt, encNats]

/-! ## splitting `ofFn` over `Fin (V + 2)` -/

lemma ofFn_split {α : Type} {V : ℕ} (f : Fin (V + 2) → α) :
    List.ofFn f = f 0 :: (List.ofFn fun i : Fin V => f i.castSucc.succ) ++ [f (Fin.last (V + 1))] := by
  rw [List.ofFn_succ, List.ofFn_succ']
  simp [Fin.succ_last]

lemma mid_ne_zero {V : ℕ} (i : Fin V) : (i.castSucc.succ : Fin (V + 2)) ≠ 0 := Fin.succ_ne_zero _

lemma mid_ne_last {V : ℕ} (i : Fin V) : (i.castSucc.succ : Fin (V + 2)) ≠ Fin.last (V + 1) := by
  intro h; have := congrArg Fin.val h; simp at this; omega

lemma zero_ne_last' (V : ℕ) : (0 : Fin (V + 2)) ≠ Fin.last (V + 1) := by
  intro h; have := congrArg Fin.val h; simp at this

lemma last_ne_zero' (V : ℕ) : Fin.last (V + 1) ≠ (0 : Fin (V + 2)) := (zero_ne_last' V).symm

lemma flatten_ofFn_single {β : Type} : ∀ {n : ℕ} (g : Fin n → β),
    (List.ofFn fun i => [g i]).flatten = List.ofFn g := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ n ih => intro g; simp [List.ofFn_succ, ih]

/-! ## the code of the PARTITION project -/

def rowZ (V : ℕ) (a b c : List ℤ) : List ℤ := a ++ (List.replicate V b).flatten ++ c

def matZ (V : ℕ) : List ℤ :=
  rowZ V [0, 0] [1, 0] [1, 1] ++ (List.replicate V (rowZ V [0, 0] [0, 0] [1, 0])).flatten ++
    rowZ V [0, 0] [0, 0] [0, 0]

lemma flatten_flatten_ofFn {β : Type} {n : ℕ} (F : Fin n → List (List β)) :
    (List.ofFn F).flatten.flatten = (List.ofFn fun i => (F i).flatten).flatten := by
  rw [List.flatten_flatten, List.map_ofFn]; rfl

lemma ofFn_split_eq {α : Type} {V : ℕ} (f : Fin (V + 2) → α) (a c : α) (g : Fin V → α)
    (h0 : f 0 = a) (hm : ∀ i : Fin V, f i.castSucc.succ = g i) (hl : f (Fin.last (V + 1)) = c) :
    List.ofFn f = a :: List.ofFn g ++ [c] := by
  rw [ofFn_split, h0, hl]
  have : (fun i : Fin V => f i.castSucc.succ) = g := funext hm
  rw [this]

lemma ofFn_split_const {α : Type} {V : ℕ} (f : Fin (V + 2) → α) (a b c : α) (h0 : f 0 = a)
    (hm : ∀ i : Fin V, f i.castSucc.succ = b) (hl : f (Fin.last (V + 1)) = c) :
    List.ofFn f = a :: List.replicate V b ++ [c] := by
  rw [ofFn_split_eq f a c (fun _ => b) h0 hm hl, List.ofFn_const]

lemma flatten_row {V : ℕ} {β : Type} (a b c : List β) :
    (a :: List.replicate V b ++ [c]).flatten = a ++ (List.replicate V b).flatten ++ c := by
  simp

def Ep (ν : ℕ) : Finset (Fin (ν + 2) × Fin (ν + 2)) :=
  Finset.univ.filter fun e : Fin (ν + 2) × Fin (ν + 2) =>
    (e.1 = 0 ∧ e.2 ≠ 0) ∨ (e.1 ≠ 0 ∧ e.1 ≠ Fin.last (ν + 1) ∧ e.2 = Fin.last (ν + 1))

def δp (ν : ℕ) (i j : Fin (ν + 2)) : ℤ := if i = 0 ∧ j = Fin.last (ν + 1) then 1 else 0

lemma mem_Ep (ν : ℕ) (i j : Fin (ν + 2)) : (i, j) ∈ Ep ν ↔
    (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ i ≠ Fin.last (ν + 1) ∧ j = Fin.last (ν + 1)) := by
  unfold Ep; rw [Finset.mem_filter]; simp

lemma mat_gen (ν : ℕ) :
    (List.ofFn fun i : Fin (ν + 2) => List.ofFn fun j : Fin (ν + 2) =>
      [if (i, j) ∈ Ep ν then (1 : ℤ) else 0, δp ν i j]).flatten.flatten = matZ ν := by
  have hz := zero_ne_last' ν
  have hl := last_ne_zero' ν
  simp only [mem_Ep, δp]
  rw [flatten_flatten_ofFn]
  rw [ofFn_split_const _ (rowZ ν [0, 0] [1, 0] [1, 1]) (rowZ ν [0, 0] [0, 0] [1, 0])
    (rowZ ν [0, 0] [0, 0] [0, 0])]
  · simp [matZ, rowZ]
  · rw [ofFn_split_const _ [0, 0] [1, 0] [1, 1], flatten_row, rowZ] <;> (try intro j) <;>
      simp [hz, hl, mid_ne_zero, mid_ne_last]
  · intro i
    rw [ofFn_split_const _ [0, 0] [0, 0] [1, 0], flatten_row, rowZ] <;> (try intro j) <;>
      simp [hz, hl, mid_ne_zero, mid_ne_last]
  · rw [ofFn_split_const _ [0, 0] [0, 0] [0, 0], flatten_row, rowZ] <;> (try intro j) <;>
      simp [hz, hl, mid_ne_zero, mid_ne_last]

lemma mat_pp (s : List ℕ) :
    (List.ofFn fun i => List.ofFn fun j =>
      [if (i, j) ∈ (partitionProject s.get).E then (1 : ℤ) else 0,
        (partitionProject s.get).δ i j]).flatten.flatten = matZ s.length := by
  exact mat_gen s.length

def rp {ν : ℕ} (f : Fin ν → ℕ) (i : Fin (ν + 2)) : ℤ :=
  if i = 0 ∨ i = Fin.last (ν + 1) then -((∑ l, (f l : ℤ)) / 2) else (partitionSize f i : ℤ)

lemma r_gen {ν : ℕ} (f : Fin ν → ℕ) :
    (List.ofFn fun i : Fin (ν + 2) => List.ofFn fun _ : Fin 1 => rp f i).flatten =
      [-((∑ l, (f l : ℤ)) / 2)] ++ List.ofFn (fun i => (f i : ℤ)) ++ [-((∑ l, (f l : ℤ)) / 2)] := by
  have hl := last_ne_zero' ν
  simp only [List.ofFn_const, List.replicate_one]
  rw [flatten_ofFn_single, ofFn_split_eq _ (-((∑ l, (f l : ℤ)) / 2)) (-((∑ l, (f l : ℤ)) / 2))
    (fun i => (f i : ℤ))]
  · simp
  · simp [rp]
  · intro i
    have := i.isLt
    simp only [rp, mid_ne_zero, mid_ne_last, or_self, if_false, partitionSize, Fin.val_succ,
      Fin.coe_castSucc]
    rw [dif_pos ⟨by omega, by omega⟩]
    simp
  · simp [rp]

lemma r_pp (s : List ℕ) :
    (List.ofFn fun i => List.ofFn fun k => (partitionProject s.get).r i k).flatten =
      [-((s.sum / 2 : ℕ) : ℤ)] ++ s.map (fun k : ℕ => (k : ℤ)) ++ [-((s.sum / 2 : ℕ) : ℤ)] := by
  have hsum : (∑ l : Fin s.length, ((s.get l : ℕ) : ℤ)) / 2 = ((s.sum / 2 : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, ← List.sum_ofFn, List.ofFn_get]; omega
  have hmap : List.ofFn (fun i : Fin s.length => ((s.get i : ℕ) : ℤ)) = s.map (fun k : ℕ => (k : ℤ)) := by
    have := List.ofFn_getElem_eq_map s (fun k : ℕ => (k : ℤ))
    simpa using this
  have h := r_gen s.get
  rw [hsum, hmap] at h
  exact h

theorem code_pp (s : List ℕ) :
    (partitionProject s.get).code =
      [(s.length : ℤ), 1] ++ ([0] ++ List.replicate s.length 0 ++ [0]) ++ matZ s.length ++
        ([-((s.sum / 2 : ℕ) : ℤ)] ++ s.map (fun k : ℕ => (k : ℤ)) ++ [-((s.sum / 2 : ℕ) : ℤ)]) ++
        [0] ++ [0] := by
  have hp : (List.ofFn fun i => (((partitionProject s.get).p i : ℕ) : ℤ)) =
      [0] ++ List.replicate s.length 0 ++ [0] := by
    have : (List.ofFn fun i => (((partitionProject s.get).p i : ℕ) : ℤ)) =
        List.ofFn (fun _ : Fin (s.length + 2) => (0 : ℤ)) := rfl
    rw [this, List.ofFn_const, List.replicate_succ, List.replicate_succ']
    simp
  simp only [CumInstance.code]
  rw [hp, mat_pp, r_pp]
  simp [partitionProject]

/-! ## injectivity of the instance code -/

def bval' : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval' l)

lemma bval'_bits (n : ℕ) : bval' (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval']
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval', ih]

lemma sep_split_inj : ∀ {u u' R R' : List BSym}, BSym.sep ∉ u → BSym.sep ∉ u' →
    u ++ BSym.sep :: R = u' ++ BSym.sep :: R' → u = u' ∧ R = R' := by
  intro u
  induction u with
  | nil =>
    intro u' R R' _ hu' h
    rcases u' with _ | ⟨a, u'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu'
  | cons a u ih =>
    intro u' R R' hu hu' h
    rcases u' with _ | ⟨b, u'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih (fun hm => hu (List.mem_cons_of_mem _ hm))
        (fun hm => hu' (List.mem_cons_of_mem _ hm)) h.2
      exact ⟨by rw [h.1, h1], h2⟩

def digU (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++
    (Nat.bits z.natAbs).map (fun b => if b then BSym.one else BSym.zero)

lemma encInt_eq_digU (z : ℤ) : encInt z = digU z ++ [BSym.sep] := by
  simp [encInt, encNat, digU]

lemma sep_not_mem_digU (z : ℤ) : BSym.sep ∉ digU z := by
  simp only [digU, List.mem_append, List.mem_map, not_or]
  constructor
  · split_ifs <;> simp
  · rintro ⟨b, -, hb⟩; cases b <;> simp at hb

lemma map_bits_inj {a b : List Bool}
    (h : a.map (fun b => if b then BSym.one else BSym.zero) =
      b.map (fun b => if b then BSym.one else BSym.zero)) : a = b := by
  refine List.map_injective_iff.mpr ?_ h
  intro x y hxy; cases x <;> cases y <;> simp_all

lemma digU_inj {z z' : ℤ} (h : digU z = digU z') : z = z' := by
  have key : ∀ {z z' : ℤ}, digU z = digU z' → (z < 0 ↔ z' < 0) := by
    intro z z' h
    by_contra hne
    simp only [digU] at h
    rcases lt_or_ge z 0 with hz | hz <;> rcases lt_or_ge z' 0 with hz' | hz'
    · exact hne (iff_of_true hz hz')
    · rw [if_pos hz, if_neg (not_lt.2 hz')] at h
      cases hb : Nat.bits z'.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · rw [if_neg (not_lt.2 hz), if_pos hz'] at h
      cases hb : Nat.bits z.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · exact hne (iff_of_false (not_lt.2 hz) (not_lt.2 hz'))
  have hs := key h
  have habs : z.natAbs = z'.natAbs := by
    simp only [digU] at h
    by_cases hz : z < 0
    · rw [if_pos hz, if_pos (hs.1 hz)] at h
      simp only [List.singleton_append, List.cons.injEq, true_and] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
    · rw [if_neg hz, if_neg (fun h' => hz (hs.2 h'))] at h
      simp only [List.nil_append] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
  omega

lemma encInts_inj : ∀ (l l' : List ℤ), encInts l = encInts l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rcases l' with _ | ⟨z, l'⟩
    · rfl
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
  | cons z l ih =>
    intro l' h
    rcases l' with _ | ⟨z', l'⟩
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
    · rw [encInts_cons, encInts_cons, encInt_eq_digU, encInt_eq_digU] at h
      simp only [List.append_assoc, List.singleton_append] at h
      obtain ⟨h1, h2⟩ := sep_split_inj (sep_not_mem_digU z) (sep_not_mem_digU z') h
      rw [digU_inj h1, ih l' h2]

lemma flatten_inj {β : Type} : ∀ (L L' : List (List β)), L.map List.length = L'.map List.length →
    L.flatten = L'.flatten → L = L' := by
  intro L
  induction L with
  | nil => intro L' hl _; cases L' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons l L ih =>
    intro L' hl h
    rcases L' with _ | ⟨l', L'⟩
    · simp at hl
    · simp only [List.map_cons, List.cons.injEq] at hl
      simp only [List.flatten_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h hl.1
      rw [h1, ih L' hl.2 h2]

theorem code_inj {x y : CumInstance} (h : x.code = y.code) : x = y := by
  obtain ⟨n, m, p, E, δ, r, Rl, Ru⟩ := x
  obtain ⟨n', m', p', E', δ', r', Rl', Ru'⟩ := y
  simp only [CumInstance.code, List.cons_append, List.nil_append, List.cons.injEq,
    Nat.cast_inj] at h
  obtain ⟨rfl, rfl, h⟩ := h
  obtain ⟨h, hRu⟩ := List.append_inj' h (by simp)
  obtain ⟨h, hRl⟩ := List.append_inj' h (by simp)
  obtain ⟨h, hr⟩ := List.append_inj' h (by simp [List.length_flatten, List.map_ofFn, Function.comp_def])
  obtain ⟨hp, hM⟩ := List.append_inj' h (by simp [List.length_flatten, List.map_ofFn, Function.comp_def])
  have hRu' := List.ofFn_injective hRu
  have hRl' := List.ofFn_injective hRl
  have hp' : p = p' := by
    funext i; have := congrFun (List.ofFn_injective hp) i; simpa using this
  have hr1 := flatten_inj _ _ (by simp [List.map_ofFn, Function.comp_def]) hr
  have hr2 := List.ofFn_injective hr1
  have hr' : r = r' := by
    funext i k; exact congrFun (List.ofFn_injective (congrFun hr2 i)) k
  have hM1 := flatten_inj _ _ (by simp [List.map_ofFn, Function.comp_def, List.map_flatten]) hM
  have hM2 := flatten_inj _ _ (by simp [List.map_ofFn, Function.comp_def]) hM1
  have hM3 := List.ofFn_injective hM2
  have hij : ∀ i j, ([if (i, j) ∈ E then (1 : ℤ) else 0, δ i j] : List ℤ) =
      [if (i, j) ∈ E' then (1 : ℤ) else 0, δ' i j] := fun i j =>
    congrFun (List.ofFn_injective (congrFun hM3 i)) j
  have hδ : δ = δ' := by
    funext i j; have := hij i j; simp only [List.cons.injEq] at this; exact this.2.1
  have hE : E = E' := by
    ext ⟨i, j⟩
    have := hij i j
    simp only [List.cons.injEq] at this
    have h1 := this.1
    split_ifs at h1 with ha hb hb <;> simp_all
  subst hp' hE hδ hr' hRl' hRu'
  rfl

theorem encode_inj {x y : CumInstance} (h : x.encode = y.encode) : x = y :=
  code_inj (encInts_inj _ _ h)

theorem encode_ne_nil (x : CumInstance) : x.encode ≠ [] := by
  simp [CumInstance.encode, CumInstance.code, encInts_cons, encInt_eq_digU]

/-! ## well-formedness and PARTITION bookkeeping -/

lemma rp_mid {ν : ℕ} (f : Fin ν → ℕ) (i : Fin ν) : rp f i.castSucc.succ = (f i : ℤ) := by
  have := i.isLt
  simp only [rp, mid_ne_zero, mid_ne_last, or_self, if_false, partitionSize, Fin.val_succ,
    Fin.coe_castSucc]
  rw [dif_pos ⟨by omega, by omega⟩]
  simp

lemma sum_rp {ν : ℕ} (f : Fin ν → ℕ) :
    ∑ i : Fin (ν + 2), rp f i = (∑ l, (f l : ℤ)) - 2 * ((∑ l, (f l : ℤ)) / 2) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [rp_mid, Fin.succ_last]
  have h0 : rp f 0 = -((∑ l, (f l : ℤ)) / 2) := by simp [rp]
  have hl : rp f (Fin.last (ν + 1)) = -((∑ l, (f l : ℤ)) / 2) := by simp [rp]
  rw [h0, hl]; ring

lemma Ep_irrefl (ν : ℕ) : ∀ e ∈ Ep ν, e.1 ≠ e.2 := by
  rintro ⟨i, j⟩ he'
  rw [mem_Ep] at he'
  rcases he' with ⟨h1, h2⟩ | ⟨-, h2, h3⟩
  · intro h; exact h2 (h.symm.trans h1)
  · intro h; exact h2 (h.trans h3)

lemma pp_wf_iff {ν : ℕ} (f : Fin ν → ℕ) (hν : 1 ≤ ν) :
    (partitionProject f).WellFormed ↔ Even (∑ i, f i) := by
  have key : ∀ k, (∑ i, (partitionProject f).r i k) =
      (∑ l, (f l : ℤ)) - 2 * ((∑ l, (f l : ℤ)) / 2) := fun _ => sum_rp f
  have hcast : (∑ l, (f l : ℤ)) = ((∑ l, f l : ℕ) : ℤ) := by push_cast; rfl
  rw [Nat.even_iff]
  unfold CumInstance.WellFormed
  constructor
  · rintro ⟨-, -, -, -, -, h⟩
    have h0 := h ⟨0, Nat.one_pos⟩
    rw [key, hcast] at h0
    change (0 : ℤ) ≤ _ ∧ _ ≤ (0 : ℤ) at h0
    omega
  · intro he
    refine ⟨hν, rfl, rfl, Ep_irrefl ν, fun _ => le_rfl, fun k => ?_⟩
    rw [key, hcast]
    change (0 : ℤ) ≤ _ ∧ _ ≤ (0 : ℤ)
    omega

lemma sum_as_ite {m : ℕ} (A : Finset (Fin m)) (g : Fin m → ℕ) :
    ∑ i ∈ A, g i = ∑ i, if i ∈ A then g i else 0 := by
  rw [← Finset.sum_filter]; congr 1; ext; simp

lemma split_zero_iff {n : ℕ} (f : Fin (n + 1) → ℕ) (h0 : f 0 = 0) :
    (∃ A : Finset (Fin (n + 1)), ∑ i ∈ A, f i = ∑ i ∈ Aᶜ, f i) ↔
      ∃ B : Finset (Fin n), ∑ i ∈ B, f i.succ = ∑ i ∈ Bᶜ, f i.succ := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨Finset.univ.filter (fun i => i.succ ∈ A), ?_⟩
    rw [sum_as_ite A, sum_as_ite Aᶜ, Fin.sum_univ_succ, Fin.sum_univ_succ, h0] at hA
    rw [sum_as_ite (Finset.univ.filter (fun i => i.succ ∈ A)),
      sum_as_ite (Finset.univ.filter (fun i => i.succ ∈ A))ᶜ]
    simpa using hA
  · rintro ⟨B, hB⟩
    refine ⟨B.map (Fin.succEmb n), ?_⟩
    rw [sum_as_ite B, sum_as_ite Bᶜ] at hB
    rw [sum_as_ite (B.map (Fin.succEmb n)), sum_as_ite (B.map (Fin.succEmb n))ᶜ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, h0]
    have hm : ∀ i : Fin n, (i.succ ∈ B.map (Fin.succEmb n)) ↔ i ∈ B := by
      intro i
      exact Finset.mem_map' (Fin.succEmb n)
    simp only [Finset.mem_compl, hm]
    simpa using hB

lemma partitionYes_cons_zero (sl : List ℕ) : PartitionYes (0 :: sl) ↔ PartitionYes sl := by
  unfold PartitionYes
  have := split_zero_iff (n := sl.length) (fun i => (0 :: sl).get i) rfl
  simpa using this

lemma even_of_partitionYes {s : List ℕ} (h : PartitionYes s) : Even (∑ i, s.get i) := by
  obtain ⟨A, hA⟩ := h
  rw [← Finset.sum_add_sum_compl A, ← hA]
  exact ⟨_, rfl⟩

lemma sum_get (s : List ℕ) : ∑ i, s.get i = s.sum := by
  rw [← List.sum_ofFn, List.ofFn_get]

/-! ## the code of the project as the machine writes it -/

def gB (b : Bool) : BSym := if b then BSym.one else BSym.zero

lemma gB_eq : gB = fun b => if b then BSym.one else BSym.zero := rfl

lemma encInts_nil : encInts [] = [] := rfl

lemma encNats_cons_zero (sl : List ℕ) : encNats (0 :: sl) = [BSym.sep] ++ encNats sl := by
  simp [encNats, encNat]

def midRowC (V : ℕ) : List BSym :=
  [BSym.sep, .sep] ++ (List.replicate V [BSym.sep, .sep]).flatten ++ [BSym.one, .sep, .sep]

def mnC (l : List BSym) : List BSym := if l = [] then [] else [BSym.minus]

lemma encInts_replicate (V : ℕ) (z : ℤ) :
    encInts (List.replicate V z) = (List.replicate V (encInt z)).flatten := by
  induction V with
  | zero => rfl
  | succ V ih => simp [List.replicate_succ, encInts_cons, ih]

lemma encInt_zero : encInt 0 = [BSym.sep] := by simp [encInt, encNat]

lemma encInt_one : encInt 1 = [BSym.one, BSym.sep] := by
  have h1 : Nat.bits 1 = [true] := by
    have := Nat.bits_append_bit 0 true (by simp)
    simpa using this
  simp [encInt, encNat, h1]

lemma encInt_natCast (V : ℕ) : encInt (V : ℤ) = (Nat.bits V).map gB ++ [BSym.sep] := by
  have : ¬ ((V : ℤ) < 0) := by omega
  simp [encInt, encNat, gB_eq, this]

lemma bits_eq_nil_iff (h : ℕ) : Nat.bits h = [] ↔ h = 0 := by
  constructor
  · intro hb; rw [← bval'_bits h, hb]; rfl
  · rintro rfl; simp

lemma encInt_neg_nat (h : ℕ) :
    encInt (-(h : ℤ)) = mnC ((Nat.bits h).map gB) ++ (Nat.bits h).map gB ++ [BSym.sep] := by
  by_cases h0 : h = 0
  · subst h0; simp [encInt, encNat, mnC]
  · have hne : (Nat.bits h).map gB ≠ [] := by
      simpa [List.map_eq_nil_iff, bits_eq_nil_iff] using h0
    have hlt : -(h : ℤ) < 0 := by omega
    simp only [encInt, if_pos hlt, mnC, if_neg hne, encNat, Int.natAbs_neg, Int.natAbs_natCast]
    simp [gB_eq]

theorem encode_pp_spec (sl : List ℕ) :
    (partitionProject (0 :: sl).get).encode =
      (Nat.bits (sl.length + 1)).map gB ++
      ([BSym.sep, .one, .sep, .sep] ++ (List.replicate (sl.length + 1) [BSym.sep]).flatten ++
      [BSym.sep, .sep, .sep] ++ (List.replicate (sl.length + 1) [BSym.one, .sep, .sep]).flatten ++
      [BSym.one, .sep, .one, .sep] ++ (List.replicate (sl.length + 1) (midRowC (sl.length + 1))).flatten ++
      [BSym.sep, .sep] ++ (List.replicate (sl.length + 1) [BSym.sep, .sep]).flatten ++ [BSym.sep, .sep]) ++
      (mnC ((Nat.bits (sl.sum / 2)).map gB) ++ (Nat.bits (sl.sum / 2)).map gB ++ [BSym.sep, .sep] ++
        encNats sl ++ mnC ((Nat.bits (sl.sum / 2)).map gB) ++ (Nat.bits (sl.sum / 2)).map gB ++
        [BSym.sep, .sep, .sep]) := by
  have hc := code_pp (0 :: sl)
  simp only [List.length_cons, List.sum_cons, zero_add] at hc
  rw [CumInstance.encode, hc]
  simp only [encInts_append, encInts_cons, encInts_nil, encInts_replicate, encInts_replicate_flatten,
    encInts_natCast, encNats_cons_zero, matZ, rowZ, encInt_zero, encInt_one, encInt_natCast,
    encInt_neg_nat]
  simp [midRowC, List.append_assoc]


/-! ## feasibility of the PARTITION project (Theorem 2.12.1, p. 131) -/

lemma Ep_ord (ν : ℕ) : ∀ e ∈ Ep ν, e.1.val < e.2.val := by
  rintro ⟨i, j⟩ he
  rw [mem_Ep] at he
  rcases he with ⟨rfl, hj⟩ | ⟨-, hil, rfl⟩
  · have : j.val ≠ 0 := fun h => hj (Fin.ext (by simpa using h))
    simp only [Fin.val_zero]; omega
  · have : i.val ≠ ν + 1 := fun h => hil (Fin.ext (by simpa using h))
    have := i.isLt
    simp only [Fin.val_last]; omega

lemma inv_formula {ν : ℕ} (f : Fin ν → ℕ) (S : Fin (ν + 2) → ℝ) (k : Fin (partitionProject f).m)
    (t : ℝ) :
    (partitionProject f).inventory S k t = ∑ j : Fin (ν + 2), if S j ≤ t then rp f j else 0 := by
  unfold CumInstance.inventory CumInstance.activeSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hr : (partitionProject f).r j k = rp f j := rfl
  have hp : ((partitionProject f).p j : ℝ) = 0 := by simp [partitionProject]
  rw [hr, hp]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; rcases h1 with ⟨-, h⟩ | ⟨-, h⟩ <;> linarith
  · rcases lt_trichotomy (rp f j) 0 with h | h | h
    · exact absurd (Or.inl ⟨h, h2⟩) h1
    · exact h.symm
    · exact absurd (Or.inr ⟨h, by linarith⟩) h1
  · rfl

noncomputable def Sdef {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) : ℝ :=
  if h : j = 0 ∨ j = Fin.last (ν + 1) then (if j = 0 then 0 else 1)
  else (if (⟨j.val - 1, by
      have := j.isLt
      simp only [not_or, Fin.ext_iff, Fin.val_zero, Fin.val_last] at h
      omega⟩ : Fin ν) ∈ A then 0 else 1)

lemma Sdef_zero {ν : ℕ} (A : Finset (Fin ν)) : Sdef A 0 = 0 := by simp [Sdef]

lemma Sdef_last {ν : ℕ} (A : Finset (Fin ν)) : Sdef A (Fin.last (ν + 1)) = 1 := by
  simp [Sdef, last_ne_zero']

lemma Sdef_mid {ν : ℕ} (A : Finset (Fin ν)) (i : Fin ν) :
    Sdef A i.castSucc.succ = if i ∈ A then 0 else 1 := by
  unfold Sdef
  rw [dif_neg (by simp [mid_ne_zero, mid_ne_last])]
  simp

lemma Sdef_nonneg {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) : 0 ≤ Sdef A j := by
  unfold Sdef; split_ifs <;> norm_num

lemma Sdef_le_one {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) : Sdef A j ≤ 1 := by
  unfold Sdef; split_ifs <;> norm_num

lemma Sdef_arcs {ν : ℕ} (A : Finset (Fin ν)) :
    ∀ e ∈ Ep ν, (δp ν e.1 e.2 : ℝ) ≤ Sdef A e.2 - Sdef A e.1 := by
  rintro ⟨i, j⟩ he
  rw [mem_Ep] at he
  rcases he with ⟨rfl, hj⟩ | ⟨hi0, -, rfl⟩
  · simp only [δp, Sdef_zero, sub_zero, true_and]
    split_ifs with hjl
    · subst hjl; rw [Sdef_last]; norm_num
    · simpa using Sdef_nonneg A j
  · simp only [δp, hi0, false_and, if_false, Sdef_last, Int.cast_zero]
    linarith [Sdef_le_one A i]

lemma sum_ite_mem_univ {ν : ℕ} (A : Finset (Fin ν)) (f : Fin ν → ℕ) :
    (∑ i, if i ∈ A then (f i : ℤ) else 0) = ((∑ i ∈ A, f i : ℕ) : ℤ) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]; push_cast; rfl

lemma sum_split {ν : ℕ} (g : Fin (ν + 2) → ℤ) :
    ∑ j, g j = g 0 + ∑ i : Fin ν, g i.castSucc.succ + g (Fin.last (ν + 1)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]; ring

lemma inv_Sdef {ν : ℕ} (f : Fin ν → ℕ) (A : Finset (Fin ν))
    (hA : ∑ i ∈ A, f i = ∑ i ∈ Aᶜ, f i) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j : Fin (ν + 2), if Sdef A j ≤ t then rp f j else 0) = 0 := by
  have htot := Finset.sum_add_sum_compl A f
  have hcast : (∑ l, (f l : ℤ)) = ((∑ l, f l : ℕ) : ℤ) := by push_cast; rfl
  have h0 : rp f 0 = -((∑ l, (f l : ℤ)) / 2) := by simp [rp]
  have hl : rp f (Fin.last (ν + 1)) = -((∑ l, (f l : ℤ)) / 2) := by simp [rp]
  rw [sum_split]
  simp only [Sdef_zero, Sdef_mid, Sdef_last, rp_mid, if_pos ht, h0, hl, hcast]
  by_cases h1 : 1 ≤ t
  · rw [if_pos h1]
    have : ∀ i : Fin ν, (if (if i ∈ A then (0 : ℝ) else 1) ≤ t then (f i : ℤ) else 0) = f i := by
      intro i; split_ifs with h <;> simp_all
    simp only [this, hcast]
    omega
  · rw [if_neg h1]
    have : ∀ i : Fin ν, (if (if i ∈ A then (0 : ℝ) else 1) ≤ t then (f i : ℤ) else 0) =
        if i ∈ A then (f i : ℤ) else 0 := by
      intro i; split_ifs with h h' h' <;> simp_all
    simp only [this, sum_ite_mem_univ]
    omega

theorem feasible_iff_gen {ν : ℕ} (s : Fin ν → ℕ) (hs : Even (∑ i, s i)) :
    (partitionProject s).IsAcyclic ∧
      ((∃ S, (partitionProject s).Feasible S) ↔
        ∃ A : Finset (Fin ν), ∑ i ∈ A, s i = ∑ i ∈ Aᶜ, s i) := by
  refine ⟨⟨fun i => i.val, Ep_ord ν⟩, ?_, ?_⟩
  · rintro ⟨S, h⟩
    have hS0 : S (0 : Fin (ν + 2)) = 0 := h.1.1
    have harc : ((δp ν 0 (Fin.last (ν + 1)) : ℤ) : ℝ) ≤
        S (Fin.last (ν + 1) : Fin (ν + 2)) - S (0 : Fin (ν + 2)) :=
      h.1.2.2 ((0 : Fin (ν + 2)), Fin.last (ν + 1))
        (show ((0 : Fin (ν + 2)), Fin.last (ν + 1)) ∈ Ep ν from
          (mem_Ep ν _ _).2 (Or.inl ⟨rfl, last_ne_zero' ν⟩))
    have hlast : (1 : ℝ) ≤ S (Fin.last (ν + 1) : Fin (ν + 2)) := by
      simp [δp, hS0] at harc; linarith
    have h2 := h.2 ⟨0, Nat.one_pos⟩ 0 le_rfl
    rw [inv_formula s S] at h2
    change (0 : ℤ) ≤ _ ∧ _ ≤ (0 : ℤ) at h2
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last] at h2
    simp only [hS0, le_refl, if_true, rp_mid] at h2
    rw [if_neg (by linarith)] at h2
    have h0 : rp s 0 = -((∑ l, (s l : ℤ)) / 2) := by simp [rp]
    rw [h0] at h2
    refine ⟨Finset.univ.filter (fun i : Fin ν => S (i.castSucc.succ : Fin (ν + 2)) ≤ 0), ?_⟩
    have hA : (∑ i : Fin ν, if S (i.castSucc.succ : Fin (ν + 2)) ≤ 0 then (s i : ℤ) else 0) =
        ((∑ i ∈ Finset.univ.filter (fun i : Fin ν => S (i.castSucc.succ : Fin (ν + 2)) ≤ 0),
          s i : ℕ) : ℤ) := by
      rw [Finset.sum_filter]; push_cast; rfl
    rw [hA] at h2
    have htot := Finset.sum_add_sum_compl
      (Finset.univ.filter (fun i : Fin ν => S (i.castSucc.succ : Fin (ν + 2)) ≤ 0)) s
    have hcast : (∑ l, (s l : ℤ)) = ((∑ l, s l : ℕ) : ℤ) := by push_cast; rfl
    rw [hcast] at h2
    rw [Nat.even_iff] at hs
    omega
  · rintro ⟨A, hA⟩
    refine ⟨@Sdef ν A, ⟨Sdef_zero A, fun i => Sdef_nonneg A i, Sdef_arcs A⟩, fun k t ht => ?_⟩
    rw [inv_formula s (@Sdef ν A)]
    change (0 : ℤ) ≤ _ ∧ _ ≤ (0 : ℤ)
    rw [inv_Sdef s A hA t ht]
    simp


/-! ## The whole machine and the reduction function -/

lemma enc_eq_map_gB (x : List Bool) : enc x = x.map gB := rfl

lemma midRow_eq (V : ℕ) : midRow V = midRowC V := rfl

lemma mn_eq (l : List BSym) : mn l = mnC l := rfl

lemma encNats_inj {a b : List ℕ} (h : encNats a = encNats b) : a = b := by
  rw [← encInts_natCast, ← encInts_natCast] at h
  exact List.map_injective_iff.2 (fun x y hxy => by exact_mod_cast hxy) (encInts_inj _ _ h)

open Classical in
noncomputable def Fred (w : List BSym) : List BSym :=
  if h : ∃ sl, w = encNats sl then (partitionProject (0 :: h.choose).get).encode else []

lemma Fred_valid (sl : List ℕ) : Fred (encNats sl) = (partitionProject (0 :: sl).get).encode := by
  have h : ∃ s, encNats sl = encNats s := ⟨sl, rfl⟩
  rw [Fred, dif_pos h, show h.choose = sl from (encNats_inj h.choose_spec).symm]

lemma Fred_invalid {w : List BSym} (hw : ¬ ∃ sl, w = encNats sl) : Fred w = [] := by
  rw [Fred, dif_neg hw]

lemma pp_acyclic {ν : ℕ} (f : Fin ν → ℕ) : (partitionProject f).IsAcyclic :=
  ⟨fun i => i.val, Ep_ord ν⟩

theorem Fred_correct (C : CumInstance → Prop) (hC : ∀ sl : List ℕ, C (partitionProject (0 :: sl).get)) :
    ∀ w, w ∈ partitionLang ↔ Fred w ∈ cumFeasLang C := by
  intro w
  constructor
  · rintro ⟨sl, hyes, rfl⟩
    rw [Fred_valid]
    have heven := even_of_partitionYes ((partitionYes_cons_zero sl).2 hyes)
    exact ⟨_, (pp_wf_iff _ (by simp)).2 heven, hC sl,
      ((feasible_iff_gen _ heven).2).2 ((partitionYes_cons_zero sl).2 hyes), rfl⟩
  · rintro ⟨x, hwf, -, hfeas, hx⟩
    by_cases hw : ∃ sl, w = encNats sl
    · obtain ⟨sl, rfl⟩ := hw
      rw [Fred_valid] at hx
      have hxe := encode_inj hx
      subst hxe
      have heven := (pp_wf_iff _ (by simp)).1 hwf
      exact ⟨sl, (partitionYes_cons_zero sl).1 (((feasible_iff_gen _ heven).2).1 hfeas), rfl⟩
    · rw [Fred_invalid hw] at hx
      exact absurd hx.symm (encode_ne_nil x)

def preAct (_ : Key → Option BSym) (k : Key) : StackAct BSym :=
  if k = .nu then .push .one else if k = .bc then .push .one else .keep

def mainProg : StackProg Key BSym :=
  .seq (copyProg .inp .orig .sc)
    (.seq parseLoop
      (.branch (fun h => (h .bad).isSome) skipP
        (.seq (copyProg .nu .c1 .sc) (.seq (.act preAct) (.seq countLoop outProg)))))

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

lemma exec_main (w : List BSym) : ∃ t n, n ≤ 400 * (w.length + 1) ^ 2 + 400 ∧
    mainProg.Exec (fun j => if j = .inp then w else []) t n ∧ t .out = Fred w := by
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
    set t := PS sa [] (enc (Nat.bits (0 + T))) (List.replicate N .one ++ []) [] [] [] with ht
    have hbr : (fun h : Key → Option BSym => (h .bad).isSome) (fun k => (t k).head?) = false := by
      simp [ht, PS]
    obtain ⟨n3, hn3, e3⟩ := exec_copy .nu .c1 .sc (by decide) (by decide) (by decide) t
      (by simp [ht, PS, hsa, hs0])
    set t3 := Function.update t .c1 (t .nu ++ t .c1) with ht3
    have e4 := StackProg.Exec.act preAct t3
    set t4 := StackProg.applyAct preAct t3 with ht4
    have v4 : ∀ k, t4 k = if k = .nu then List.replicate (N + 1) .one
        else if k = .bc then [.one] else if k = .c1 then List.replicate N .one else t k := by
      intro k
      cases k <;> simp [ht4, ht3, StackProg.applyAct, preAct, StackAct.apply, ht, PS, hsa, hs0,
        List.replicate_succ]
    obtain ⟨n5, hn5, e5⟩ := exec_count N 1 t4 (by rw [v4]; simp) (by rw [v4]; simp [enc, bits_one, toB])
      (by rw [v4]; simp [ht, PS, hsa, hs0]) (by rw [v4]; simp [ht, PS])
      (by rw [v4]; simp [ht, PS]) (by rw [v4]; simp [ht, PS])
    set t5 := Function.update (Function.update t4 .c1 []) .bc (enc (Nat.bits (1 + N))) with ht5
    have v5 : ∀ k, k ≠ .c1 → k ≠ .bc → t5 k = t4 k := by
      intro k k1 k2; simp [ht5, k1, k2]
    obtain ⟨t6, n6, hn6, e6, hout⟩ := exec_outProg (N + 1) t5
      (by rw [v5 _ (by decide) (by decide), v4]; simp [ht, PS, hsa, hs0])
      (by simp [ht5]) (by rw [v5 _ (by decide) (by decide), v4]; simp [ht, PS, hsa, hs0])
      (by rw [v5 _ (by decide) (by decide), v4]; simp [ht, PS, hsa, hs0])
      (by rw [v5 _ (by decide) (by decide), v4]; simp [ht, PS, hsa, hs0])
      (by rw [v5 _ (by decide) (by decide), v4]; simp)
      (by rw [v5 _ (by decide) (by decide), v4]; simp [ht, PS, hsa, hs0])
    have hbc : t5 .bc = enc (Nat.bits (N + 1)) := by simp [ht5, Nat.add_comm]
    have hacc : t5 .acc = enc (Nat.bits T) := by
      rw [v5 _ (by decide) (by decide), v4]; simp [ht, PS]
    have horig : t5 .orig = w := by
      rw [v5 _ (by decide) (by decide), v4]; simp [ht, PS, hsa, hs0]
    refine ⟨t6, n1 + 1 + (n2 + 1 + (1 + (n3 + 1 + (1 + 1 + (n5 + 1 + n6))))), ?_,
      StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.branchFalse hbr
        (StackProg.Exec.seq e3 (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 e6))))), ?_⟩
    · have hNL : N ≤ w.length := by rw [hsl]; exact len_sl sl
      have hTL : (Nat.bits T).length ≤ w.length := by
        have := len_bits_sum sl 0; simp at this; rw [hsl]; simpa [hT] using this
      have hbcL : (Nat.bits (N + 1)).length ≤ N + 1 := len_bits_le _
      rw [hbc, hacc, horig] at hn6
      simp only [enc, List.length_map] at hn6
      have hn3' : n3 ≤ 6 * N + 3 := by simpa [ht, PS] using hn3
      unfold roBound at hn6
      set L := w.length with hL
      have m1 : (N + 1) * (16 * (N + 1) + 30) ≤ (L + 1) * (16 * (L + 1) + 30) :=
        Nat.mul_le_mul (by omega) (by omega)
      have m2 : 4 * (N + 1) * (N + 1) ≤ 4 * (L + 1) * (L + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have m3 : N * (6 * (1 + N) + 30) ≤ L * (6 * (1 + L) + 30) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · rw [hout, hbc, hacc, horig, hsl, Fred_valid, encode_pp_spec]
      have hdiv : (enc (Nat.bits T)).tail = enc (Nat.bits (T / 2)) := by
        rw [bits_div_two]; simp [enc, List.map_tail]
      rw [hdiv]
      simp only [enc_eq_map_gB, midRow_eq, mn_eq, hN, hT]
  · obtain ⟨i', a', nu', z', rfl⟩ := hinv (fun sl h => hw ⟨sl, h⟩)
    refine ⟨_, n1 + 1 + (n2 + 1 + (1 + 1)), ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.branchTrue (by simp [PS]) (exec_skip _))), ?_⟩
    · nlinarith
    · rw [Fred_invalid hw]; simp [PS, hsa, hs0]

theorem Fred_exec (w : List BSym) : ∃ s n, n ≤ w.length ^ 2000 + 2000 ∧
    mainProg.Exec (fun j => if j = .inp then w else []) s n ∧ s .out = Fred w := by
  obtain ⟨t, n, hn, e, ho⟩ := exec_main w
  exact ⟨t, n, le_trans hn (absorb2000 _), e, ho⟩

end P5c6

open ProjSchedTW.Complexity in
theorem solution :
    CookPvsNP.PolyReducible partitionLang (cumFeasLang CumInstance.IsAcyclic) :=
  ⟨P5c6.Fred, CookPvsNP.stack_program_polytime P5c6.mainProg .inp .out P5c6.Fred 2000 P5c6.Fred_exec,
    P5c6.Fred_correct _ (fun _ => P5c6.pp_acyclic _)⟩
