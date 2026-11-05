-- Prove2me | solution 1 for TwoAgentSched.Knapsack.knapsack_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:34:17.334803+00:00
-- url     : https://prove2.me/submissions/80c03c57-4d10-4927-b364-264525383be7

import Mathlib
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_TwoAgentSched_Knapsack_Problem51
import Definitions.Def_TwoAgentSched_Knapsack_Construction
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_TwoAgentSched_Knapsack_theorem_5_2_equivalence

section KS_Gen
set_option autoImplicit false

namespace KS
open CookPvsNP

section generic
variable {K A : Type} [DecidableEq K]

/-! ### A generic "move while" loop -/

def mmTest (p : A → Bool) (src : K) (h : K → Option A) : Bool :=
  match h src with
  | some a => p a
  | none => false

def mmAct (src : K) (g : A → K → Option A) (h : K → Option A) (k : K) : StackAct A :=
  if k = src then .pop else
    match h src with
    | some a => (match g a k with
      | some b => .push b
      | none => .keep)
    | none => .keep

def mapMove (p : A → Bool) (src : K) (g : A → K → Option A) : StackProg K A :=
  .loop (mmTest p src) (.act (mmAct src g))

def mmStore (src : K) (g : A → K → Option A) (t r : List A) (s : K → List A) : K → List A :=
  fun k => if k = src then r else (t.reverse.filterMap (fun a => g a k)) ++ s k

def stopAt (p : A → Bool) (r : List A) : Prop :=
  match r.head? with
  | some a => p a = false
  | none => True

lemma exec_mapMove (p : A → Bool) (src : K) (g : A → K → Option A) (r : List A)
    (hr : stopAt p r) :
    ∀ (t : List A) (s : K → List A), s src = t ++ r → (∀ a ∈ t, p a = true) →
      (mapMove p src g).Exec s (mmStore src g t r s) (3 * t.length + 1) := by
  intro t
  induction t with
  | nil =>
    intro s hs _
    have : mmStore src g [] r s = s := by
      funext k; simp only [mmStore]; split_ifs with h
      · subst h; simpa using hs.symm
      · simp
    rw [this]
    apply StackProg.Exec.loopFalse
    simp only [mmTest, hs, List.nil_append]
    unfold stopAt at hr
    rcases r with _ | ⟨a, r⟩
    · rfl
    · simpa using hr
  | cons a t ih =>
    intro s hs hp
    set s1 := StackProg.applyAct (mmAct src g) s with hs1
    have e1 : s1 src = t ++ r := by
      simp [hs1, StackProg.applyAct, mmAct, StackAct.apply, hs]
    have hpost : mmStore src g t r s1 = mmStore src g (a :: t) r s := by
      funext k
      simp only [mmStore]
      by_cases hk : k = src
      · simp [hk]
      · simp only [hk, if_false, hs1, StackProg.applyAct, mmAct, hs, List.cons_append,
          List.head?_cons, List.reverse_cons, List.filterMap_append, List.append_assoc]
        cases hg : g a k <;> simp [StackAct.apply, hg]
    rw [← hpost]
    have := StackProg.Exec.loopTrue (test := mmTest p src) (p := .act (mmAct src g))
      (by simp [mmTest, hs, hp a (by simp)]) (StackProg.Exec.act (mmAct src g) s)
      (ih s1 e1 (fun b hb => hp b (by simp [hb])))
    have h3 : 1 + 1 + 1 + (3 * t.length + 1) = 3 * (a :: t).length + 1 := by simp; ring
    rw [h3] at this
    exact this

/-! ### transfer and copy (as in the platform's stack library) -/

lemma exec_transfer (src : K) (targets : K → Bool) :
    ∀ (l : List A) (s : K → List A), s src = l →
      (transferProg src targets).Exec s (transferStore src targets s) (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro s hs
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
    have hex := ih s1 e1
    have hpost : transferStore src targets s1 = transferStore src targets s := by
      funext k; simp only [transferStore]
      by_cases k1 : k = src
      · simp [k1]
      by_cases k2 : targets k = true
      · simp [k1, k2, e1, hs, hs1, StackProg.applyAct, transferAct, StackAct.apply]
      · simp [k1, k2, hs1, StackProg.applyAct, transferAct, StackAct.apply]
    rw [← hpost]; subst hs1
    have := StackProg.Exec.loopTrue (by simp [hs]) (StackProg.Exec.act _ _) hex
    have h3 : 1 + 1 + 1 + (3 * l.length + 1) = 3 * (a :: l).length + 1 := by simp; ring
    rw [h3] at this; exact this

lemma exec_copy (src dst scr : K) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (s : K → List A) (hs : s scr = []) :
    (copyProg src dst scr).Exec s (Function.update s dst (s src ++ s dst))
      (6 * (s src).length + 3) := by
  have e1 := exec_transfer src (fun k => decide (k = scr)) (s src) s rfl
  set s1 := transferStore src (fun k => decide (k = scr)) s with hs1
  have hs1scr : s1 scr = (s src).reverse := by simp [hs1, transferStore, h2.symm, hs]
  have e2 := exec_transfer scr (fun k => decide (k = src ∨ k = dst)) _ s1 hs1scr
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
  have := StackProg.Exec.seq e1 e2
  simp only [List.length_reverse] at this
  have h4 : 3 * (s src).length + 1 + 1 + (3 * (s src).length + 1) = 6 * (s src).length + 3 := by
    ring
  rw [h4] at this; exact this

/-! ### single actions -/

def actP (f : (K → Option A) → K → StackAct A) : StackProg K A := .act f

lemma exec_act (f : (K → Option A) → K → StackAct A) (s : K → List A) :
    (StackProg.act f).Exec s (StackProg.applyAct f s) 1 := StackProg.Exec.act f s

end generic

end KS
end KS_Gen


section KS_Arith
set_option autoImplicit false

namespace KS

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

lemma bits_inj {a b : ℕ} (h : Nat.bits a = Nat.bits b) : a = b := by
  rw [← bval_bits a, ← bval_bits b, h]

lemma bval_lt (l : List Bool) : bval l < 2 ^ l.length := by
  induction l with
  | nil => simp [bval]
  | cons b t ih =>
    simp only [bval, List.length_cons, pow_succ]
    cases b <;> simp [Nat.bit] <;> omega

lemma bval_append (l l' : List Bool) : bval (l ++ l') = bval l + 2 ^ l.length * bval l' := by
  induction l with
  | nil => simp [bval]
  | cons b t ih =>
    simp only [List.cons_append, bval, ih, List.length_cons, pow_succ]
    cases b <;> simp [Nat.bit] <;> ring

lemma bval_replicate_false (j : ℕ) : bval (List.replicate j false) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, bval, ih, Nat.bit]

lemma bval_replicate_true (j : ℕ) : bval (List.replicate j true) = 2 ^ j - 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, bval, ih, Nat.bit, cond_true, pow_succ]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega

/-- every digit string is a canonical string followed by high zeros -/
lemma exists_canon_split (l : List Bool) :
    ∃ j, l = Nat.bits (bval l) ++ List.replicate j false := by
  induction l with
  | nil => exact ⟨0, by simp [bval]⟩
  | cons b t ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases h0 : b = false ∧ bval t = 0
    · obtain ⟨rfl, ht⟩ := h0
      refine ⟨j + 1, ?_⟩
      have : bval (false :: t) = 0 := by simp [bval, ht, Nat.bit]
      rw [this, hj, ht]; simp [List.replicate_succ]
    · refine ⟨j, ?_⟩
      have hb : bval (b :: t) = Nat.bit b (bval t) := rfl
      rw [hb, Nat.bits_append_bit]
      · conv_lhs => rw [hj]
        rfl
      · intro h; cases b
        · exact absurd ⟨rfl, h⟩ h0
        · rfl

lemma bits_length_le_of_lt {k L : ℕ} (h : k < 2 ^ L) : (Nat.bits k).length ≤ L := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.2 h

lemma lt_two_pow_bits (k : ℕ) : k < 2 ^ (Nat.bits k).length := by
  have := bval_lt (Nat.bits k); rwa [bval_bits] at this

lemma bits_bit (b : Bool) (n : ℕ) (h : n ≠ 0 ∨ b = true) :
    Nat.bits (Nat.bit b n) = b :: Nat.bits n := by
  rw [Nat.bits_append_bit]
  intro hn; rcases h with h | h
  · exact absurd hn h
  · exact h

/-- `2^L` -/
lemma bits_two_pow (L : ℕ) : Nat.bits (2 ^ L) = List.replicate L false ++ [true] := by
  induction L with
  | zero => simp
  | succ L ih =>
    have : 2 ^ (L + 1) = Nat.bit false (2 ^ L) := by simp [Nat.bit, pow_succ]; ring
    rw [this, bits_bit _ _ (Or.inl (by positivity)), ih]; simp [List.replicate_succ]

/-- `b + 2^L` with `b < 2^L` -/
lemma bits_add_two_pow (b L : ℕ) (h : (Nat.bits b).length ≤ L) :
    Nat.bits (b + 2 ^ L) =
      Nat.bits b ++ List.replicate (L - (Nat.bits b).length) false ++ [true] := by
  have hc := canon_bits_bval b
  have key : bval (Nat.bits b ++ List.replicate (L - (Nat.bits b).length) false ++ [true]) =
      b + 2 ^ L := by
    rw [bval_append, bval_append, bval_replicate_false, hc.2]
    simp [bval, Nat.bit]
    first | omega | (rw [← pow_add]; congr 2; omega)
  have hcan : Canon (Nat.bits b ++ List.replicate (L - (Nat.bits b).length) false ++ [true]) := by
    have : ∀ l : List Bool, Canon (l ++ [true]) := by
      intro l; induction l with
      | nil => simp [Canon]
      | cons a t ih => exact ⟨fun h => by simp at h, ih⟩
    exact this _
  rw [← key, bits_bval hcan]

/-- `2^L * D + 2^L - 1` -/
lemma bits_ones_append (L D : ℕ) :
    Nat.bits (2 ^ L * D + (2 ^ L - 1)) = List.replicate L true ++ Nat.bits D := by
  induction L with
  | zero => simp
  | succ L ih =>
    have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have : 2 ^ (L + 1) * D + (2 ^ (L + 1) - 1) = Nat.bit true (2 ^ L * D + (2 ^ L - 1)) := by
      simp only [Nat.bit, cond_true, pow_succ]
      have e : 2 ^ L * 2 * D = 2 * (2 ^ L * D) := by ring
      rw [e]; omega
    rw [this, bits_bit _ _ (Or.inr rfl), ih]; simp [List.replicate_succ]

/-! ## addition -/

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

lemma length_addB_le (x y : List Bool) (c : Bool) :
    (addB x y c).length ≤ x.length + y.length + 1 := by
  induction x, y, c using addB.induct <;> simp_all [addB] <;> omega

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

/-! ## subtraction with borrow -/

def bor (x y c : Bool) : Bool := (!x && (y || c)) || (x && y && c)

def subB : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], c => ([], c)
  | x :: xs, [], c => ((x ^^ c) :: (subB xs [] (bor x false c)).1, (subB xs [] (bor x false c)).2)
  | [], y :: ys, c => ((y ^^ c) :: (subB [] ys (bor false y c)).1, (subB [] ys (bor false y c)).2)
  | x :: xs, y :: ys, c =>
    ((x ^^ y ^^ c) :: (subB xs ys (bor x y c)).1, (subB xs ys (bor x y c)).2)

lemma subB_spec (x y : List Bool) (c : Bool) :
    bval (subB x y c).1 + bval y + c.toNat =
      bval x + (subB x y c).2.toNat * 2 ^ (subB x y c).1.length := by
  induction x, y, c using subB.induct with
  | case1 c => simp [subB, bval]
  | case2 x xs c ih =>
    simp only [subB, bval, List.length_cons, pow_succ] at ih ⊢
    cases x <;> cases c <;> simp [bor, Nat.bit] at ih ⊢ <;> nlinarith [ih]
  | case3 y ys c ih =>
    simp only [subB, bval, List.length_cons, pow_succ] at ih ⊢
    cases y <;> cases c <;> simp [bor, Nat.bit] at ih ⊢ <;> nlinarith [ih]
  | case4 x xs y ys c ih =>
    simp only [subB, bval, List.length_cons, pow_succ] at ih ⊢
    cases x <;> cases y <;> cases c <;> simp [bor, Nat.bit] at ih ⊢ <;> nlinarith [ih]

lemma length_subB (x y : List Bool) (c : Bool) :
    (subB x y c).1.length = max x.length y.length := by
  induction x, y, c using subB.induct <;> simp_all [subB]

lemma subB_noborrow (x y : List Bool) (hle : bval y ≤ bval x) :
    (subB x y false).2 = false ∧ bval (subB x y false).1 = bval x - bval y := by
  have h := subB_spec x y false
  have hlt := bval_lt (subB x y false).1
  cases hb : (subB x y false).2
  · simp [hb] at h; exact ⟨rfl, by omega⟩
  · exfalso; simp [hb] at h; omega

lemma subB_borrow (x y : List Bool) (hlt : bval x < bval y) : (subB x y false).2 = true := by
  have h := subB_spec x y false
  cases hb : (subB x y false).2
  · simp [hb] at h; omega
  · rfl

end KS
end KS_Arith


section KS_Tok
set_option autoImplicit false

namespace KS
open ProjSchedTW.Complexity

/-! ## Symbols -/

def ne (a : BSym) : Bool := decide (a ≠ .sep)
def isOne (a : BSym) : Bool := decide (a = .one)
def isDigS (a : BSym) : Bool := decide (a = .zero ∨ a = .one)
def toB (b : Bool) : BSym := if b then .one else .zero
def enc (x : List Bool) : List BSym := x.map toB
def tokOf (k : ℕ) : List BSym := enc (Nat.bits k)

@[simp] lemma ne_sep : ne .sep = false := rfl
@[simp] lemma ne_zero : ne .zero = true := rfl
@[simp] lemma ne_one : ne .one = true := rfl
@[simp] lemma ne_minus : ne .minus = true := rfl

lemma ne_toB (b : Bool) : ne (toB b) = true := by cases b <;> rfl

lemma enc_ne (x : List Bool) : ∀ a ∈ enc x, ne a = true := by
  intro a ha; simp only [enc, List.mem_map] at ha; obtain ⟨b, -, rfl⟩ := ha; exact ne_toB b

lemma tokOf_ne (k : ℕ) : ∀ a ∈ tokOf k, ne a = true := enc_ne _

lemma map_isOne_enc (x : List Bool) : (enc x).map isOne = x := by
  induction x with
  | nil => rfl
  | cons b t ih => cases b <;> simp_all [enc, toB, isOne]

lemma enc_inj {x y : List Bool} (h : enc x = enc y) : x = y := by
  rw [← map_isOne_enc x, ← map_isOne_enc y, h]

lemma tokOf_inj {a b : ℕ} (h : tokOf a = tokOf b) : a = b := bits_inj (enc_inj h)

lemma tokOf_one : tokOf 1 = [.one] := by
  simp [tokOf, enc, toB, Nat.bits]

lemma encNat_eq (k : ℕ) : encNat k = tokOf k ++ [.sep] := by
  simp [encNat, tokOf, enc, toB]

lemma encNats_cons (k : ℕ) (l : List ℕ) : encNats (k :: l) = tokOf k ++ .sep :: encNats l := by
  simp [encNats, encNat_eq]

lemma encNats_append (l l' : List ℕ) : encNats (l ++ l') = encNats l ++ encNats l' := by
  simp [encNats]

/-! ## sep-free splitting -/

lemma tw_split (t r : List BSym) (ht : ∀ a ∈ t, ne a = true) :
    (t ++ .sep :: r).takeWhile ne = t ∧ (t ++ .sep :: r).dropWhile ne = .sep :: r := by
  rw [List.takeWhile_append_of_pos ht, List.dropWhile_append_of_pos ht]
  simp

lemma tw_nil (t : List BSym) (ht : ∀ a ∈ t, ne a = true) :
    t.takeWhile ne = t ∧ t.dropWhile ne = [] := by
  induction t with
  | nil => simp
  | cons a t ih =>
    have ha := ht a (by simp)
    have := ih (fun b hb => ht b (by simp [hb]))
    simp [List.takeWhile_cons, List.dropWhile_cons, ha, this.1, this.2]

lemma sep_split_inj {u u' R R' : List BSym} (hu : ∀ a ∈ u, ne a = true)
    (hu' : ∀ a ∈ u', ne a = true) (h : u ++ .sep :: R = u' ++ .sep :: R') : u = u' ∧ R = R' := by
  have e1 := tw_split u R hu
  have e2 := tw_split u' R' hu'
  rw [h] at e1
  refine ⟨e1.1.symm.trans e2.1, ?_⟩
  have := e1.2.symm.trans e2.2
  simpa using this

/-- tokens with their separators -/
def joinT (ts : List (List BSym)) : List BSym := ts.flatMap (· ++ [.sep])

lemma joinT_cons (t : List BSym) (ts : List (List BSym)) :
    joinT (t :: ts) = t ++ .sep :: joinT ts := by simp [joinT]

lemma joinT_append (ts ts' : List (List BSym)) : joinT (ts ++ ts') = joinT ts ++ joinT ts' := by
  simp [joinT]

lemma encNats_eq_joinT (l : List ℕ) : encNats l = joinT (l.map tokOf) := by
  induction l with
  | nil => rfl
  | cons k l ih => rw [encNats_cons, List.map_cons, joinT_cons, ih]

lemma joinT_inj : ∀ (ts ts' : List (List BSym)), (∀ t ∈ ts, ∀ a ∈ t, ne a = true) →
    (∀ t ∈ ts', ∀ a ∈ t, ne a = true) → joinT ts = joinT ts' → ts = ts'
  | [], [], _, _, _ => rfl
  | [], t :: ts', _, _, h => by simp [joinT] at h
  | t :: ts, [], _, _, h => by simp [joinT] at h
  | t :: ts, t' :: ts', h1, h2, h => by
    rw [joinT_cons, joinT_cons] at h
    obtain ⟨e1, e2⟩ := sep_split_inj (h1 t (by simp)) (h2 t' (by simp)) h
    rw [e1, joinT_inj ts ts' (fun s hs => h1 s (by simp [hs])) (fun s hs => h2 s (by simp [hs])) e2]

/-- every string is a sequence of tokens followed by a sep-free rest -/
lemma exists_joinT : ∀ (N : ℕ) (l : List BSym), l.length ≤ N →
    ∃ ts r, l = joinT ts ++ r ∧ (∀ t ∈ ts, ∀ a ∈ t, ne a = true) ∧ (∀ a ∈ r, ne a = true) := by
  intro N
  induction N with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact ⟨[], [], by simp [joinT], by simp, by simp⟩
  | succ N ih =>
    intro l hl
    by_cases hall : ∀ a ∈ l, ne a = true
    · exact ⟨[], l, by simp [joinT], by simp, hall⟩
    · push_neg at hall
      obtain ⟨t, r, hlr, ht, hr⟩ : ∃ t r, l = t ++ .sep :: r ∧ (∀ a ∈ t, ne a = true) ∧ True := by
        refine ⟨l.takeWhile ne, (l.dropWhile ne).tail, ?_, fun a ha => ?_, trivial⟩
        · have hd := List.head?_dropWhile_not ne l
          have hne : l.dropWhile ne ≠ [] := by
            intro h0; rw [List.dropWhile_eq_nil_iff] at h0
            obtain ⟨a, ha, hna⟩ := hall; simp [h0 a ha] at hna
          obtain ⟨a, rest, hrest⟩ := List.exists_cons_of_ne_nil hne
          rw [hrest] at hd ⊢
          simp only [List.head?_cons] at hd
          have ha : a = .sep := by cases a <;> simp_all [ne]
          subst ha
          conv_lhs => rw [← List.takeWhile_append_dropWhile (p := ne) (l := l), hrest]
          rfl
        · exact List.mem_takeWhile_imp ha
      obtain ⟨ts, r', h1, h2, h3⟩ := ih r (by rw [hlr] at hl; simp at hl; omega)
      refine ⟨t :: ts, r', ?_, ?_, h3⟩
      · rw [hlr, h1, joinT_cons]; simp
      · intro s hs; simp at hs; rcases hs with rfl | hs
        · exact ht
        · exact h2 s hs

/-! ## canonical tokens -/

def zStep (a : BSym) (z : List BSym) : List BSym :=
  if a = .zero then (if z = [] then [.one] else z) else if a = .one then z.tail else z

def zF : List BSym → List BSym → List BSym
  | [], z => z
  | a :: t, z => zF t (zStep a z)

def canonTok (t : List BSym) : Bool := t.all isDigS && (zF t []).isEmpty

lemma zF_enc_nil_iff (y : List Bool) : ∀ z : List BSym, (z = [] ∨ z = [.one]) →
    (zF (enc y) z = [] ↔ (y = [] → z = []) ∧ Canon y) := by
  induction y with
  | nil => intro z _; simp [zF, enc, Canon]
  | cons b l ih =>
    intro z hz
    simp only [enc, List.map_cons, zF] at ih ⊢
    rcases hz with rfl | rfl <;> cases b <;>
      simp [toB, Canon, zStep, ih [] (Or.inl rfl), ih [.one] (Or.inr rfl)]

lemma enc_of_dig (t : List BSym) (h : ∀ a ∈ t, isDigS a = true) : enc (t.map isOne) = t := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (by simp)
    simp only [List.map_cons, enc] at ih ⊢
    rw [ih (fun b hb => h b (by simp [hb]))]
    cases a <;> simp_all [isDigS, isOne, toB]

lemma canonTok_iff (t : List BSym) : canonTok t = true ↔ ∃ k, t = tokOf k := by
  constructor
  · intro h
    simp only [canonTok, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h
    have he := enc_of_dig t h.1
    rw [← he] at h
    have hc := ((zF_enc_nil_iff _ [] (Or.inl rfl)).1 h.2).2
    refine ⟨bval (t.map isOne), ?_⟩
    rw [tokOf, bits_bval hc, he]
  · rintro ⟨k, rfl⟩
    simp only [canonTok, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff]
    refine ⟨fun a ha => ?_, ?_⟩
    · simp only [tokOf, enc, List.mem_map] at ha; obtain ⟨b, -, rfl⟩ := ha
      cases b <;> rfl
    · exact (zF_enc_nil_iff _ [] (Or.inl rfl)).2 ⟨fun _ => rfl, (canon_bits_bval k).1⟩

/-! ## token-level loops: dropping tokens and summing tokens -/

def dropToks : ℕ → List BSym → List BSym
  | 0, l => l
  | k + 1, l => dropToks k (l.dropWhile ne).tail

lemma len_dw_tail (l : List BSym) (h : l ≠ []) : ((l.dropWhile ne).tail).length < l.length := by
  have := List.length_dropWhile_le ne l
  rcases hd : l.dropWhile ne with _ | ⟨a, r⟩
  · simp; exact List.length_pos_of_ne_nil h
  · rw [hd] at this; simp at this ⊢; omega

def sumAcc (acc : List Bool) (l : List BSym) : List Bool :=
  if h : l = [] then acc else
    sumAcc (addB acc ((l.takeWhile ne).map isOne) false) ((l.dropWhile ne).tail)
termination_by l.length
decreasing_by exact len_dw_tail l h

lemma sumAcc_nil (acc : List Bool) : sumAcc acc [] = acc := by
  rw [sumAcc]; simp

lemma sumAcc_cons_tok (acc : List Bool) (t r : List BSym) (ht : ∀ a ∈ t, ne a = true) :
    sumAcc acc (t ++ .sep :: r) = sumAcc (addB acc (t.map isOne) false) r := by
  rw [sumAcc, dif_neg (by simp), (tw_split t r ht).1, (tw_split t r ht).2]; rfl

lemma sumAcc_encNats (acc : List Bool) (l : List ℕ) :
    bval (sumAcc acc (encNats l)) = bval acc + l.sum := by
  induction l generalizing acc with
  | nil => simp [encNats, sumAcc_nil]
  | cons k l ih =>
    rw [encNats_cons, sumAcc_cons_tok _ _ _ (tokOf_ne k), ih, bval_addB, tokOf,
      map_isOne_enc, bval_bits]
    simp; ring

lemma dropToks_encNats (l1 l2 : List ℕ) : dropToks l1.length (encNats (l1 ++ l2)) = encNats l2 := by
  induction l1 with
  | nil => rfl
  | cons k l ih =>
    simp only [List.length_cons, dropToks, List.cons_append, encNats_cons]
    rw [(tw_split _ _ (tokOf_ne k)).2]; exact ih

lemma count_sep_encNats (l : List ℕ) : (encNats l).count .sep = l.length := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [encNats_cons, List.count_append, List.count_cons, ih]
    have : (tokOf k).count .sep = 0 := by
      rw [List.count_eq_zero]; intro h; have := tokOf_ne k _ h; simp at this
    simp [this]

/-- the length of the sum stays linear -/
lemma len_sumAcc : ∀ (N : ℕ) (acc : List Bool) (l : List BSym), l.length ≤ N →
    (sumAcc acc l).length ≤ acc.length + 2 * l.length := by
  intro N
  induction N with
  | zero =>
    intro acc l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [sumAcc_nil]
  | succ N ih =>
    intro acc l hl
    by_cases h0 : l = []
    · subst h0; simp [sumAcc_nil]
    rw [sumAcc, dif_neg h0]
    have hlt := len_dw_tail l h0
    have h1 := ih (addB acc ((l.takeWhile ne).map isOne) false) ((l.dropWhile ne).tail)
      (by omega)
    have h2 := length_addB_le acc ((l.takeWhile ne).map isOne) false
    have h3 : (l.takeWhile ne).length + 2 * ((l.dropWhile ne).tail).length + 1 ≤ 2 * l.length := by
      have e := congrArg List.length (List.takeWhile_append_dropWhile (p := ne) (l := l))
      rw [List.length_append] at e
      have := List.length_pos_of_ne_nil h0
      rcases hd : l.dropWhile ne with _ | ⟨a, r⟩
      · rw [hd] at e; simp at e ⊢; omega
      · rw [hd] at e; simp at e ⊢; omega
    simp only [List.length_map] at h2
    omega

/-- numbers of a list are bounded by the length of its code -/
lemma sum_lt_pow (l : List ℕ) : l.sum + 1 ≤ 2 ^ (encNats l).length := by
  induction l with
  | nil => simp [encNats]
  | cons k l ih =>
    rw [encNats_cons]
    simp only [List.sum_cons, List.length_append, List.length_cons, pow_add, pow_succ]
    have hk : k + 1 ≤ 2 ^ (tokOf k).length := by
      simp only [tokOf, enc, List.length_map]; exact lt_two_pow_bits k
    have h1 := Nat.mul_le_mul hk ih
    have h2 : 2 ^ (tokOf k).length * (2 ^ (encNats l).length * 2) =
        2 * (2 ^ (tokOf k).length * 2 ^ (encNats l).length) := by ring
    rw [h2]
    have h3 : k + l.sum + 1 ≤ (k + 1) * (l.sum + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
    omega

end KS
end KS_Tok


section KS_Sched
set_option autoImplicit false
open TwoAgentSched.Knapsack MooreLateJobs.Shared

namespace KN

/-- The instance with A-jobs `p^A_i = u_i`, `w^A_i = w_i` and one B-job of length `P`. -/
def mI {n : ℕ} (u w : Fin n → ℕ) (P : ℕ) : Instance where
  nA := n
  nB := 1
  pA := u
  wA := w
  pB := fun _ => P

def aJ {n : ℕ} (u w : Fin n → ℕ) (P : ℕ) (i : Fin n) : Fin (mI u w P).nA ⊕ Fin (mI u w P).nB :=
  Sum.inl i

def bJ {n : ℕ} (u w : Fin n → ℕ) (P : ℕ) : Fin (mI u w P).nA ⊕ Fin (mI u w P).nB :=
  Sum.inr ⟨0, Nat.one_pos⟩

end KN

lemma kn_ct_eq {ι : Type*} [DecidableEq ι] [Fintype ι] (t : ι → ℝ) (l : List ι)
    (hl : IsSchedule Finset.univ l) (j : ι) :
    completionTime t l j = ∑ y, if l.idxOf y ≤ l.idxOf j then t y else 0 := by
  have hj : j ∈ l := (hl.2 j).2 (Finset.mem_univ j)
  unfold completionTime completionAt
  have hnd' : (l.take (l.idxOf j + 1)).Nodup := hl.1.sublist (List.take_sublist _ _)
  rw [← List.sum_toFinset _ hnd', ← Finset.sum_filter]
  congr 1
  ext y
  have hyl : y ∈ l := (hl.2 y).2 (Finset.mem_univ y)
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.mem_take_iff_idxOf_lt hyl]
  omega

instance kn_sumLawfulBEq {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [BEq.beq, Sum.instBEq.beq]
  rfl := by
    intro a
    rcases a with a | a <;> simp [BEq.beq, Sum.instBEq.beq]

theorem kn_sumBEq_eq {α β : Type*} [DecidableEq α] [DecidableEq β] :
    (Sum.instBEq : BEq (α ⊕ β)) = instBEqOfDecidableEq := by
  have : ∀ a b : α ⊕ β, (Sum.instBEq : BEq (α ⊕ β)).beq a b = (instBEqOfDecidableEq : BEq (α ⊕ β)).beq a b := by
    intro a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [BEq.beq, Sum.instBEq.beq]
  cases h1 : (Sum.instBEq : BEq (α ⊕ β)) with
  | mk f =>
    cases h2 : (instBEqOfDecidableEq : BEq (α ⊕ β)) with
    | mk g =>
      have e : f = g := by
        funext a b
        have := this a b
        rw [h1, h2] at this
        exact this
      rw [e]

namespace KN
variable {n : ℕ} (u w : Fin n → ℕ) (P : ℕ)

abbrev Jb := Fin (mI u w P).nA ⊕ Fin (mI u w P).nB

lemma kn_ct_eq' (l : List (Jb u w P)) (hl : IsSchedule Finset.univ l) (j : Jb u w P) :
    completionTime (mI u w P).p l j =
      ∑ y, if l.idxOf y ≤ l.idxOf j then (mI u w P).p y else 0 := by
  rw [kn_ct_eq _ l hl]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [kn_sumBEq_eq]

def bI : Fin (mI u w P).nB := ⟨0, Nat.one_pos⟩

lemma sum_nB (g : Fin (mI u w P).nB → ℝ) :
    ∑ k, g k = g (bI u w P) := by
  rw [Finset.sum_eq_single (bI u w P)]
  · intro b _ hb
    exfalso; apply hb; apply Fin.ext
    have := b.2
    simp only [mI] at this ⊢
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

lemma tA (i : Fin n) : (mI u w P).p (aJ u w P i) = (u i : ℝ) := rfl
lemma tB (k : Fin (mI u w P).nB) : (mI u w P).p (Sum.inr k) = (P : ℝ) := rfl

lemma idx_ne (l : List (Jb u w P)) (hl : IsSchedule Finset.univ l) (i : Fin n) :
    l.idxOf (aJ u w P i) ≠ l.idxOf (bJ u w P) := by
  intro h
  have hai : aJ u w P i ∈ l := (hl.2 _).2 (Finset.mem_univ _)
  have := (List.idxOf_inj hai).1 h
  exact absurd this (by simp [aJ, bJ])

/-- completion time of the B-job -/
lemma CB (l : List (Jb u w P)) (hl : IsSchedule Finset.univ l) :
    (mI u w P).C l (bJ u w P) = (P : ℝ) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => l.idxOf (aJ u w P i) < l.idxOf (bJ u w P)),
        (u i : ℝ) := by
  unfold Instance.C
  rw [kn_ct_eq' u w P l hl, Fintype.sum_sum_type, sum_nB, Finset.sum_filter]
  have hbb : (Sum.inr (bI u w P) : Jb u w P) = bJ u w P := rfl
  rw [hbb, if_pos le_rfl, add_comm]
  rw [show (mI u w P).p (bJ u w P) = (P : ℝ) from rfl]
  congr 1
  refine Finset.sum_congr rfl (fun (i : Fin n) _ => ?_)
  have hne := idx_ne u w P l hl i
  have e1 : l.idxOf (Sum.inl i : Jb u w P) = l.idxOf (aJ u w P i) := rfl
  rw [e1]
  by_cases h : l.idxOf (aJ u w P i) < l.idxOf (bJ u w P)
  · rw [if_pos h.le, if_pos h]; rfl
  · rw [if_neg (fun h' => h (lt_of_le_of_ne h' hne)), if_neg h]

lemma CA_bounds (l : List (Jb u w P)) (hl : IsSchedule Finset.univ l) (i : Fin n) :
    (u i : ℝ) + (if l.idxOf (aJ u w P i) < l.idxOf (bJ u w P) then 0 else (P : ℝ)) ≤
        (mI u w P).C l (aJ u w P i) ∧
      (mI u w P).C l (aJ u w P i) ≤
        (uHat u : ℝ) + (if l.idxOf (aJ u w P i) < l.idxOf (bJ u w P) then 0 else (P : ℝ)) := by
  unfold Instance.C
  rw [kn_ct_eq' u w P l hl, Fintype.sum_sum_type, sum_nB]
  have hbi : (l.idxOf (Sum.inr (bI u w P) : Jb u w P) ≤ l.idxOf (aJ u w P i)) ↔
      ¬ (l.idxOf (aJ u w P i) < l.idxOf (bJ u w P)) := by
    rw [not_lt]; rfl
  have hB : (if l.idxOf (Sum.inr (bI u w P) : Jb u w P) ≤ l.idxOf (aJ u w P i) then
        (mI u w P).p (Sum.inr (bI u w P)) else 0) =
      (if l.idxOf (aJ u w P i) < l.idxOf (bJ u w P) then 0 else (P : ℝ)) := by
    by_cases h : l.idxOf (aJ u w P i) < l.idxOf (bJ u w P)
    · rw [if_neg (fun h' => (hbi.1 h') h), if_pos h]
    · rw [if_pos (hbi.2 h), if_neg h]; rfl
  rw [hB]
  have hnn : ∀ y : Jb u w P, 0 ≤ (mI u w P).p y := by
    intro y; rcases y with y | y
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  constructor
  · have h1 : (u i : ℝ) ≤ ∑ a, if l.idxOf (Sum.inl a : Jb u w P) ≤ l.idxOf (aJ u w P i) then
        (mI u w P).p (Sum.inl a) else 0 := by
      have := Finset.single_le_sum (f := fun a : Fin n => if l.idxOf (Sum.inl a : Jb u w P) ≤
          l.idxOf (aJ u w P i) then (mI u w P).p (Sum.inl a) else 0)
        (fun a _ => by split_ifs; exact hnn _; exact le_refl _) (Finset.mem_univ i)
      have e : (if l.idxOf (Sum.inl i : Jb u w P) ≤ l.idxOf (aJ u w P i) then
          (mI u w P).p (Sum.inl i) else 0) = (u i : ℝ) := by
        have e1 : l.idxOf (Sum.inl i : Jb u w P) = l.idxOf (aJ u w P i) := rfl
        rw [e1, if_pos (le_refl _)]; rfl
      rw [e] at this; exact this
    linarith
  · have h1 : (∑ a, if l.idxOf (Sum.inl a : Jb u w P) ≤ l.idxOf (aJ u w P i) then
        (mI u w P).p (Sum.inl a) else 0) ≤ (uHat u : ℝ) := by
      unfold uHat; push_cast
      refine Finset.sum_le_sum (fun a _ => ?_)
      split_ifs
      · exact le_refl _
      · exact Nat.cast_nonneg _
    linarith

end KN

namespace KN
variable {n : ℕ} (u w : Fin n → ℕ) (P : ℕ)

lemma inr_eq_b (k : Fin (mI u w P).nB) : (Sum.inr k : Jb u w P) = bJ u w P := by
  have : k = bI u w P := by
    apply Fin.ext
    have := k.2
    simp only [mI] at this
    simp [bI]; omega
  rw [this]; rfl

lemma wsum_eq (S : Finset (Fin n)) :
    ∑ i, (w i : ℝ) * ((uHat u : ℝ) + (if i ∈ S then 0 else (P : ℝ))) =
      (wHat w : ℝ) * (uHat u : ℝ) + (P : ℝ) * ((wHat w : ℝ) - ∑ i ∈ S, (w i : ℝ)) := by
  have h1 : ∀ i, (w i : ℝ) * ((uHat u : ℝ) + (if i ∈ S then 0 else (P : ℝ))) =
      (w i : ℝ) * (uHat u : ℝ) + ((P : ℝ) * (w i : ℝ) -
        (if i ∈ S then (P : ℝ) * (w i : ℝ) else 0)) := by
    intro i; split_ifs <;> ring
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  unfold wHat; push_cast; ring

end KN

namespace KN
variable {n : ℕ} (u w : Fin n → ℕ) (P : ℕ)

lemma wsum_lb (S : Finset (Fin n)) :
    ∑ i, (w i : ℝ) * ((u i : ℝ) + (if i ∈ S then 0 else (P : ℝ))) =
      ∑ i, (w i : ℝ) * (u i : ℝ) + (P : ℝ) * ((wHat w : ℝ) - ∑ i ∈ S, (w i : ℝ)) := by
  have h1 : ∀ i, (w i : ℝ) * ((u i : ℝ) + (if i ∈ S then 0 else (P : ℝ))) =
      (w i : ℝ) * (u i : ℝ) + ((P : ℝ) * (w i : ℝ) -
        (if i ∈ S then (P : ℝ) * (w i : ℝ) else 0)) := by
    intro i; split_ifs <;> ring
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  unfold wHat; push_cast; ring

end KN

namespace KN

theorem schedA {n : ℕ} (u w : Fin n → ℕ) (P b W' : ℕ) (hP : wHat w * uHat u < P)
    (hW : W' ≤ wHat w) (S : Finset (Fin n))
    (hu : ∑ i ∈ S, u i ≤ b) (hw : W' ≤ ∑ i ∈ S, w i)
    (l : List (Fin (mI u w P).nA ⊕ Fin (mI u w P).nB))
    (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hS : ∀ i : Fin n, i ∈ S ↔ l.idxOf (aJ u w P i) < l.idxOf (bJ u w P)) :
    (mI u w P).Meets ((P * (wHat w - W') + P - 1 : ℕ) : ℝ) ((b + P : ℕ) : ℝ) l := by
  have hSeq : S = Finset.univ.filter (fun i : Fin n => l.idxOf (aJ u w P i) < l.idxOf (bJ u w P)) := by
    ext i; rw [Finset.mem_filter]; simp [hS i]
  have hP1 : 1 ≤ P := by omega
  refine ⟨hl, ?_, ?_⟩
  · unfold Instance.sumWC
    have hCi : ∀ i : Fin n, (mI u w P).C l (Sum.inl i) ≤
        (uHat u : ℝ) + (if i ∈ S then 0 else (P : ℝ)) := by
      intro i
      have := (CA_bounds u w P l hl i).2
      have e : (if l.idxOf (aJ u w P i) < l.idxOf (bJ u w P) then (0 : ℝ) else (P : ℝ)) =
          (if i ∈ S then 0 else (P : ℝ)) := by
        by_cases h : i ∈ S
        · rw [if_pos h, if_pos ((hS i).1 h)]
        · rw [if_neg h, if_neg (fun h' => h ((hS i).2 h'))]
      rw [e] at this; exact this
    have hwS : (W' : ℝ) ≤ ∑ i ∈ S, (w i : ℝ) := by
      have : (W' : ℝ) ≤ ((∑ i ∈ S, w i : ℕ) : ℝ) := by exact_mod_cast hw
      simpa using this
    have hPR : ((wHat w * uHat u : ℕ) : ℝ) + 1 ≤ (P : ℝ) := by exact_mod_cast hP
    push_cast at hPR
    have hcast : ((P * (wHat w - W') + P - 1 : ℕ) : ℝ) = (P : ℝ) * ((wHat w : ℝ) - W') + P - 1 := by
      rw [Nat.cast_sub (by nlinarith), Nat.cast_add, Nat.cast_mul, Nat.cast_sub hW]; simp
    rw [hcast]
    calc ∑ h, ((mI u w P).wA h : ℝ) * (mI u w P).C l (Sum.inl h)
        ≤ ∑ i : Fin n, (w i : ℝ) * ((uHat u : ℝ) + (if i ∈ S then 0 else (P : ℝ))) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hCi i) (Nat.cast_nonneg _))
      _ = (wHat w : ℝ) * (uHat u : ℝ) + (P : ℝ) * ((wHat w : ℝ) - ∑ i ∈ S, (w i : ℝ)) :=
          wsum_eq u w P S
      _ ≤ (P : ℝ) * ((wHat w : ℝ) - W') + P - 1 := by
          have hP0 : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
          nlinarith
  · intro k
    rw [inr_eq_b u w P k, CB u w P l hl, ← hSeq]
    push_cast
    have : ((∑ i ∈ S, u i : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hu
    push_cast at this
    linarith

theorem schedB {n : ℕ} (u w : Fin n → ℕ) (P b W' : ℕ) (hP1 : 1 ≤ P)
    (hW : W' ≤ wHat w)
    (l : List (Fin (mI u w P).nA ⊕ Fin (mI u w P).nB))
    (hl : (mI u w P).Meets ((P * (wHat w - W') + P - 1 : ℕ) : ℝ) ((b + P : ℕ) : ℝ) l) :
    ∃ S : Finset (Fin n), ∑ i ∈ S, u i ≤ b ∧ W' ≤ ∑ i ∈ S, w i := by
  obtain ⟨hs, hwc, hcb⟩ := hl
  set S := Finset.univ.filter (fun i : Fin n => l.idxOf (aJ u w P i) < l.idxOf (bJ u w P)) with hSdef
  refine ⟨S, ?_, ?_⟩
  · have h := hcb (bI u w P)
    rw [inr_eq_b u w P, CB u w P l hs, ← hSdef] at h
    push_cast at h
    have : ((∑ i ∈ S, u i : ℕ) : ℝ) ≤ (b : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · by_contra hcon
    replace hcon := not_le.1 hcon
    have h1 : ((∑ i ∈ S, w i : ℕ) : ℝ) + 1 ≤ (W' : ℝ) := by exact_mod_cast hcon
    push_cast at h1
    have hlb : ∀ i : Fin n, (u i : ℝ) + (if i ∈ S then 0 else (P : ℝ)) ≤
        (mI u w P).C l (Sum.inl i) := by
      intro i
      have := (CA_bounds u w P l hs i).1
      have e : (if l.idxOf (aJ u w P i) < l.idxOf (bJ u w P) then (0 : ℝ) else (P : ℝ)) =
          (if i ∈ S then 0 else (P : ℝ)) := by
        simp [hSdef]
      rw [e] at this; exact this
    have hsum : ∑ i : Fin n, (w i : ℝ) * ((u i : ℝ) + (if i ∈ S then 0 else (P : ℝ))) ≤
        (mI u w P).sumWC l := by
      unfold Instance.sumWC
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlb i) (Nat.cast_nonneg _))
    rw [wsum_lb u w P S] at hsum
    have hq := hsum.trans hwc
    have hcast : ((P * (wHat w - W') + P - 1 : ℕ) : ℝ) = (P : ℝ) * ((wHat w : ℝ) - W') + P - 1 := by
      rw [Nat.cast_sub (by nlinarith), Nat.cast_add, Nat.cast_mul, Nat.cast_sub hW]; simp
    rw [hcast] at hq
    have hwu : (0 : ℝ) ≤ ∑ i, (w i : ℝ) * (u i : ℝ) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP1
    nlinarith

end KN

namespace KN

theorem schedYes {n : ℕ} (u w : Fin n → ℕ) (P b W' : ℕ) (hP : wHat w * uHat u < P)
    (hW : W' ≤ wHat w) (S : Finset (Fin n))
    (hu : ∑ i ∈ S, u i ≤ b) (hw : W' ≤ ∑ i ∈ S, w i) :
    (mI u w P).RecYes ((P * (wHat w - W') + P - 1 : ℕ) : ℝ) ((b + P : ℕ) : ℝ) := by
    classical
    let A : List (Jb u w P) := S.toList.map (fun i => aJ u w P i)
    let C : List (Jb u w P) := (Sᶜ).toList.map (fun i => aJ u w P i)
    let l : List (Jb u w P) := A ++ (bJ u w P :: C)
    have hinj : Function.Injective (fun i : Fin n => (aJ u w P i : Jb u w P)) := by
      intro i j h; exact Sum.inl.inj h
    have hbA : bJ u w P ∉ A := by
      simp [A, aJ, bJ]
    have hbC : bJ u w P ∉ C := by
      simp [C, aJ, bJ]
    have hAmem : ∀ i, aJ u w P i ∈ A ↔ i ∈ S := by
      intro i; simp only [A]; rw [List.mem_map_of_injective hinj, Finset.mem_toList]
    have hCmem : ∀ i, aJ u w P i ∈ C ↔ i ∉ S := by
      intro i; simp only [C]; rw [List.mem_map_of_injective hinj, Finset.mem_toList, Finset.mem_compl]
    have hsched : MooreLateJobs.Shared.IsSchedule Finset.univ l := by
      refine ⟨?_, ?_⟩
      · refine List.nodup_append.2 ⟨(Finset.nodup_toList S).map hinj, ?_, ?_⟩
        · exact List.nodup_cons.2 ⟨hbC, (Finset.nodup_toList _).map hinj⟩
        · intro x hx y hy hxy
          subst hxy
          simp only [A, List.mem_map, Finset.mem_toList] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          rcases List.mem_cons.1 hy with h | h
          · simp [aJ, bJ] at h
          · have := (hCmem i).1 h
            exact this hi
      · intro x
        simp only [Finset.mem_univ, iff_true]
        rcases x with i | k
        · by_cases hi : i ∈ S
          · exact List.mem_append_left _ ((hAmem i).2 hi)
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ ((hCmem i).2 hi))
        · have : (Sum.inr k : Jb u w P) = bJ u w P := inr_eq_b u w P k
          rw [this]
          exact List.mem_append_right _ (List.mem_cons_self)
    have hidxb : l.idxOf (bJ u w P) = A.length := by
      show (A ++ (bJ u w P :: C)).idxOf (bJ u w P) = A.length
      rw [List.idxOf_append_of_notMem hbA]; simp
    have hS : ∀ i : Fin n, i ∈ S ↔ l.idxOf (aJ u w P i) < l.idxOf (bJ u w P) := by
      intro i
      rw [hidxb]
      constructor
      · intro hi
        show (A ++ (bJ u w P :: C)).idxOf (aJ u w P i) < A.length
        rw [List.idxOf_append_of_mem ((hAmem i).2 hi)]
        exact List.idxOf_lt_length_iff.2 ((hAmem i).2 hi)
      · intro h
        by_contra hi
        have hnA : aJ u w P i ∉ A := fun h' => hi ((hAmem i).1 h')
        have : A.length ≤ (A ++ (bJ u w P :: C)).idxOf (aJ u w P i) := by
          rw [List.idxOf_append_of_notMem hnA]; omega
        exact absurd h (not_lt.2 this)
    exact ⟨l, schedA u w P b W' hP hW S hu hw l hsched hS⟩

theorem schedNo {n : ℕ} (u w : Fin n → ℕ) (P b W' : ℕ) (hP1 : 1 ≤ P)
    (hW : W' ≤ wHat w)
    (h : (mI u w P).RecYes ((P * (wHat w - W') + P - 1 : ℕ) : ℝ) ((b + P : ℕ) : ℝ)) :
    ∃ S : Finset (Fin n), ∑ i ∈ S, u i ≤ b ∧ W' ≤ ∑ i ∈ S, w i := by
  obtain ⟨l, hl⟩ := h
  exact schedB u w P b W' hP1 hW l hl

end KN
end KS_Sched


section KS_Spec
set_option autoImplicit false

namespace KS
open ProjSchedTW.Complexity TwoAgentSched.Knapsack

/-! ## The reduction function -/

def wdig (tW : List BSym) : Option (List Bool) :=
  if tW.head? = some BSym.minus then
    (if tW.tail ≠ [] ∧ canonTok tW.tail = true then some [] else none)
  else if canonTok tW = true then some (tW.map isOne) else none

def outP (L : ℕ) : List BSym := enc (List.replicate L false ++ [true]) ++ [BSym.sep]
def outQA (L : ℕ) (D : List Bool) : List BSym :=
  enc (List.replicate L true ++ Nat.bits (bval D)) ++ [BSym.sep]
def outQB (L : ℕ) (tB : List BSym) : List BSym :=
  tB ++ List.replicate (L - tB.length) BSym.zero ++ [BSym.one, BSym.sep]

def accOf (z1 : List BSym) : List Bool :=
  sumAcc [] (dropToks (((z1.dropWhile ne).tail.count BSym.sep + 1) / 2) (z1.dropWhile ne).tail)

def Fbody (L : ℕ) (tW tB z1 : List BSym) : List BSym :=
  if canonTok tB = true then
    match wdig tW with
    | none => []
    | some wd =>
      if (subB (accOf z1) wd false).2 = true then [] else
        z1.takeWhile ne ++ [BSym.sep, BSym.one, BSym.sep] ++ (z1.dropWhile ne).tail ++ outP L ++
          outQA L (subB (accOf z1) wd false).1 ++ outQB L tB
  else []

def F (x : List BSym) : List BSym :=
  match x.reverse with
  | BSym.sep :: v1 =>
    match v1.dropWhile ne with
    | BSym.sep :: v3 =>
      if v3.dropWhile ne = [] then [] else
        Fbody x.length (v1.takeWhile ne).reverse (v3.takeWhile ne).reverse
          (v3.dropWhile ne).reverse
    | _ => []
  | _ => []

/-! ## shape of the input -/

lemma rev_ne (t : List BSym) (h : ∀ a ∈ t, ne a = true) : ∀ a ∈ t.reverse, ne a = true := by
  intro a ha; exact h a (List.mem_reverse.1 ha)

lemma F_eq (z1' tB tW : List BSym) (hB : ∀ a ∈ tB, ne a = true) (hW : ∀ a ∈ tW, ne a = true) :
    F (z1' ++ [BSym.sep] ++ tB ++ BSym.sep :: tW ++ [BSym.sep]) =
      Fbody (z1' ++ [BSym.sep] ++ tB ++ BSym.sep :: tW ++ [BSym.sep]).length tW tB (z1' ++ [BSym.sep]) := by
  have hrev : (z1' ++ [BSym.sep] ++ tB ++ BSym.sep :: tW ++ [BSym.sep]).reverse =
      BSym.sep :: (tW.reverse ++ BSym.sep :: (tB.reverse ++ BSym.sep :: z1'.reverse)) := by simp
  have s1 := tw_split tW.reverse (tB.reverse ++ BSym.sep :: z1'.reverse) (rev_ne tW hW)
  have s2 := tw_split tB.reverse z1'.reverse (rev_ne tB hB)
  unfold F
  rw [hrev]
  simp only
  rw [s1.2]
  simp only
  rw [s2.2, if_neg (by simp), s1.1, s2.1]
  simp

lemma F_cases (x : List BSym) : F x = [] ∨ ∃ z1' tB tW, (∀ a ∈ tB, ne a = true) ∧
    (∀ a ∈ tW, ne a = true) ∧ x = z1' ++ [BSym.sep] ++ tB ++ BSym.sep :: tW ++ [BSym.sep] := by
  by_cases h0 : F x = []
  · exact Or.inl h0
  right
  rcases hx : x.reverse with _ | ⟨a, v1⟩
  · exfalso; apply h0; unfold F; rw [hx]
  have ha : a = BSym.sep := by
    by_contra hne; apply h0; unfold F; rw [hx]; cases a <;> simp_all
  subst ha
  rcases hd : v1.dropWhile ne with _ | ⟨c, v3⟩
  · exfalso; apply h0; unfold F; rw [hx]; simp only; rw [hd]
  have hc : c = BSym.sep := by
    have := List.head?_dropWhile_not ne v1
    rw [hd] at this; simp at this; cases c <;> simp_all [ne]
  subst hc
  rcases hd3 : v3.dropWhile ne with _ | ⟨e, v5⟩
  · exfalso; apply h0; unfold F; rw [hx]; simp only; rw [hd]; simp only; rw [if_pos hd3]
  have he : e = BSym.sep := by
    have := List.head?_dropWhile_not ne v3
    rw [hd3] at this; simp at this; cases e <;> simp_all [ne]
  subst he
  refine ⟨v5.reverse, (v3.takeWhile ne).reverse, (v1.takeWhile ne).reverse,
    rev_ne _ (fun a ha => List.mem_takeWhile_imp ha),
    rev_ne _ (fun a ha => List.mem_takeWhile_imp ha), ?_⟩
  have e1 : v1 = v1.takeWhile ne ++ BSym.sep :: v3 := by
    rw [← hd]; exact (List.takeWhile_append_dropWhile).symm
  have e3 : v3 = v3.takeWhile ne ++ BSym.sep :: v5 := by
    rw [← hd3]; exact (List.takeWhile_append_dropWhile).symm
  obtain ⟨A, hA⟩ : ∃ A, v1.takeWhile ne = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, v3.takeWhile ne = B := ⟨_, rfl⟩
  rw [hA] at e1 ⊢; rw [hB] at e3 ⊢
  have : x = (x.reverse).reverse := by simp
  rw [this, hx, e1, e3]
  simp

/-! ## encoding facts -/

lemma encNats_snoc_sep (l : List ℕ) (h : l ≠ []) : ∃ z', encNats l = z' ++ [BSym.sep] := by
  induction l with
  | nil => exact absurd rfl h
  | cons k l ih =>
    by_cases hl : l = []
    · subst hl; exact ⟨tokOf k, by simp [encNats, encNat_eq]⟩
    · obtain ⟨z', hz⟩ := ih hl
      exact ⟨tokOf k ++ BSym.sep :: z', by rw [encNats_cons, hz]; simp⟩

lemma encInts_natCast (l : List ℕ) : encInts (l.map (fun k : ℕ => (k : ℤ))) = encNats l := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons, encInts, List.flatMap_cons] at ih ⊢
    rw [ih]; simp [encInt, encNats]

lemma encInt_nat (k : ℕ) : encInt (k : ℤ) = tokOf k ++ [BSym.sep] := by
  simp [encInt, encNat_eq]

lemma encInt_neg (k : ℕ) (hk : k ≠ 0) : encInt (-(k : ℤ)) = BSym.minus :: tokOf k ++ [BSym.sep] := by
  simp [encInt, Nat.pos_of_ne_zero hk, encNat_eq]

lemma knapsackCode_eq {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ) :
    knapsackCode u w b W = encNats (n :: (List.ofFn u ++ List.ofFn w)) ++ encInt b ++ encInt W := by
  unfold knapsackCode
  have hu : (List.ofFn fun i => (u i : ℤ)) = (List.ofFn u).map (fun k : ℕ => (k : ℤ)) := by
    simp [List.map_ofFn, Function.comp_def]
  have hw : (List.ofFn fun i => (w i : ℤ)) = (List.ofFn w).map (fun k : ℕ => (k : ℤ)) := by
    simp [List.map_ofFn, Function.comp_def]
  rw [hu, hw, ← encInts_natCast]
  simp [encInts, List.flatMap_append]

lemma wdig_spec (tW : List BSym) (wd : List Bool) (h : wdig tW = some wd) :
    ∃ W : ℤ, tW ++ [BSym.sep] = encInt W ∧ bval wd = W.toNat := by
  unfold wdig at h
  split_ifs at h with h1 h2 h3
  · cases h
    obtain ⟨k, hk⟩ := (canonTok_iff _).1 h2.2
    have hk0 : k ≠ 0 := by rintro rfl; apply h2.1; rw [hk]; simp [tokOf, enc]
    refine ⟨-(k : ℤ), ?_, by simp [bval]⟩
    have htw : tW = BSym.minus :: tW.tail := by
      rcases tW with _ | ⟨a, t⟩
      · simp at h1
      · simp at h1; rw [h1]; rfl
    rw [encInt_neg k hk0, htw, ← hk]
  · cases h
    obtain ⟨k, hk⟩ := (canonTok_iff _).1 h3
    refine ⟨(k : ℤ), by rw [encInt_nat, hk], ?_⟩
    rw [hk, tokOf, map_isOne_enc, bval_bits]; simp

lemma wdig_of (W : ℤ) (d : List BSym) (hd : d ++ [BSym.sep] = encInt W) :
    ∃ wd, wdig d = some wd ∧ bval wd = W.toNat := by
  by_cases hW : W < 0
  · have hk : W.natAbs ≠ 0 := by omega
    have e := encInt_neg W.natAbs hk
    have hW' : -(W.natAbs : ℤ) = W := by omega
    rw [hW'] at e
    rw [e] at hd
    have hd' : d = BSym.minus :: tokOf W.natAbs := by
      exact List.append_cancel_right hd
    refine ⟨[], ?_, by simp [bval]; omega⟩
    have hne : tokOf W.natAbs ≠ [] := by
      intro h0; have := congrArg bval (congrArg (List.map isOne) h0)
      rw [tokOf, map_isOne_enc, bval_bits] at this; simp [bval] at this; omega
    simp [wdig, hd', hne, (canonTok_iff _).2 ⟨_, rfl⟩]
  · have hk : W = (W.toNat : ℤ) := by omega
    have e := encInt_nat W.toNat
    rw [← hk] at e
    rw [e] at hd
    have hd' : d = tokOf W.toNat := List.append_cancel_right hd
    refine ⟨Nat.bits W.toNat, ?_, bval_bits _⟩
    have hh : d.head? ≠ some BSym.minus := by
      rw [hd']; simp only [tokOf, enc]
      cases h : Nat.bits W.toNat with
      | nil => simp
      | cons b t => cases b <;> simp [toB]
    have hh' : (tokOf W.toNat).head? ≠ some BSym.minus := by rw [← hd']; exact hh
    rw [hd']; unfold wdig
    rw [if_neg hh', if_pos ((canonTok_iff _).2 ⟨_, rfl⟩), tokOf, map_isOne_enc]

/-! ## the body on a well-formed prefix -/

lemma accOf_eq (k : ℕ) (us ws : List ℕ) (hu : us.length = k) (hw : ws.length = k) :
    bval (accOf (tokOf k ++ BSym.sep :: encNats (us ++ ws))) = ws.sum := by
  unfold accOf
  rw [(tw_split _ _ (tokOf_ne k)).2]
  simp only [List.tail_cons]
  rw [count_sep_encNats, List.length_append, hu, hw,
    show (k + k + 1) / 2 = us.length by omega, dropToks_encNats, sumAcc_encNats]
  simp [bval]

lemma encInt_split (W : ℤ) : ∃ d, encInt W = d ++ [BSym.sep] ∧ ∀ a ∈ d, ne a = true := by
  refine ⟨(if W < 0 then [BSym.minus] else []) ++ tokOf W.natAbs, ?_, ?_⟩
  · simp [encInt, encNat_eq]
  · intro a ha
    simp only [List.mem_append] at ha
    rcases ha with ha | ha
    · split_ifs at ha <;> simp_all
    · exact tokOf_ne _ a ha

lemma tokOf_two_pow (L : ℕ) : tokOf (2 ^ L) = enc (List.replicate L false ++ [true]) := by
  rw [tokOf, bits_two_pow]

lemma outP_eq (L : ℕ) : outP L = tokOf (2 ^ L) ++ [BSym.sep] := by
  rw [outP, tokOf_two_pow]

lemma outQA_eq (L : ℕ) (D : List Bool) :
    outQA L D = tokOf (2 ^ L * bval D + (2 ^ L - 1)) ++ [BSym.sep] := by
  rw [outQA, tokOf, bits_ones_append]

lemma outQB_eq (L b : ℕ) (h : (tokOf b).length ≤ L) :
    outQB L (tokOf b) = tokOf (b + 2 ^ L) ++ [BSym.sep] := by
  have h' : (Nat.bits b).length ≤ L := by simpa [tokOf, enc] using h
  simp only [outQB, tokOf]
  rw [bits_add_two_pow b L h']
  simp [enc, toB]

lemma codeList_mI {n : ℕ} (u w : Fin n → ℕ) (P QA QB : ℕ) :
    (KN.mI u w P).codeList QA QB = n :: 1 :: (List.ofFn u ++ List.ofFn w ++ [P, QA, QB]) := by
  simp [Instance.codeList, KN.mI]

theorem F_yes {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ) (hK : KnapsackYes u w b W) :
    F (knapsackCode u w b W) ∈ targetLang := by
  obtain ⟨S, hSu, hSw⟩ := hK
  have hb0 : 0 ≤ b := le_trans (by positivity) hSu
  obtain ⟨b', rfl⟩ : ∃ b' : ℕ, b = (b' : ℤ) := ⟨b.toNat, by omega⟩
  obtain ⟨dW, hdW, hdWne⟩ := encInt_split W
  obtain ⟨z1', hz1'⟩ := encNats_snoc_sep (n :: (List.ofFn u ++ List.ofFn w)) (by simp)
  set x := knapsackCode u w (b' : ℤ) W with hxdef
  have hx : x = z1' ++ [BSym.sep] ++ tokOf b' ++ BSym.sep :: dW ++ [BSym.sep] := by
    rw [hxdef, knapsackCode_eq, hz1', encInt_nat, hdW]; simp
  have hF := F_eq z1' (tokOf b') dW (tokOf_ne b') hdWne
  rw [← hx] at hF
  set L := x.length with hL
  have hz1 : z1' ++ [BSym.sep] = tokOf n ++ BSym.sep :: encNats (List.ofFn u ++ List.ofFn w) := by
    rw [← hz1', encNats_cons]
  obtain ⟨wd, hwd, hwdv⟩ := wdig_of W dW hdW.symm
  have hacc : bval (accOf (z1' ++ [BSym.sep])) = wHat w := by
    rw [hz1, accOf_eq n (List.ofFn u) (List.ofFn w) (by simp) (by simp), List.sum_ofFn]; rfl
  have hWle : W.toNat ≤ wHat w := by
    have h1 : ∑ i ∈ S, w i ≤ wHat w := Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    have : W ≤ (wHat w : ℤ) := le_trans hSw (by exact_mod_cast h1)
    omega
  have hsub := subB_noborrow (accOf (z1' ++ [BSym.sep])) wd (by rw [hacc, hwdv]; exact hWle)
  rw [hacc, hwdv] at hsub
  set D := (subB (accOf (z1' ++ [BSym.sep])) wd false).1 with hD
  have hLb : (tokOf b').length ≤ L := by rw [hL, hx]; simp; omega
  have hP1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  set P := 2 ^ L with hP
  -- the output
  have hout : F x = encNats ((KN.mI u w P).codeList (P * (wHat w - W.toNat) + P - 1) (b' + P)) := by
    rw [hF, Fbody, if_pos ((canonTok_iff _).2 ⟨_, rfl⟩), hwd]
    simp only
    have ht : (z1' ++ [BSym.sep]).takeWhile ne = tokOf n := by
      rw [hz1]; exact (tw_split _ _ (tokOf_ne n)).1
    have hdr : ((z1' ++ [BSym.sep]).dropWhile ne).tail = encNats (List.ofFn u ++ List.ofFn w) := by
      rw [hz1, (tw_split _ _ (tokOf_ne n)).2]; rfl
    rw [if_neg (by rw [hsub.1]; decide), ht, hdr, ← hD, outP_eq, outQA_eq, outQB_eq L b' hLb,
      hsub.2, codeList_mI]
    have e : 2 ^ L * (wHat w - W.toNat) + (2 ^ L - 1) = P * (wHat w - W.toNat) + P - 1 := by
      rw [← hP]; omega
    rw [e]
    simp [encNats, encNat_eq, tokOf_one, hP]
  -- feasibility
  have hbound : wHat w * uHat u < P := by
    have h1 := sum_lt_pow (List.ofFn w)
    have h2 := sum_lt_pow (List.ofFn u)
    rw [List.sum_ofFn] at h1 h2
    have hlen : (encNats (List.ofFn u)).length + (encNats (List.ofFn w)).length ≤ L := by
      rw [hL, hxdef, knapsackCode_eq]
      simp [encNats_cons, encNats_append]; omega
    have h3 := Nat.mul_le_mul h1 h2
    have h4 : 2 ^ (encNats (List.ofFn w)).length * 2 ^ (encNats (List.ofFn u)).length ≤ P := by
      rw [← pow_add, hP]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : wHat w * uHat u < (wHat w + 1) * (uHat u + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
    unfold wHat uHat at *
    omega
  have hSw' : W.toNat ≤ ∑ i ∈ S, w i := by
    have : W ≤ ((∑ i ∈ S, w i : ℕ) : ℤ) := hSw
    omega
  have hSu' : ∑ i ∈ S, u i ≤ b' := by exact_mod_cast hSu
  exact ⟨KN.mI u w P, _, _, KN.schedYes u w P b' W.toNat hbound hWle S hSu' hSw', hout⟩


lemma z1_split (z1' : List BSym) : ∃ ms, z1' ++ [BSym.sep] =
      (z1' ++ [BSym.sep]).takeWhile ne ++ BSym.sep :: joinT ms ∧
    ((z1' ++ [BSym.sep]).dropWhile ne).tail = joinT ms ∧ (∀ t ∈ ms, ∀ a ∈ t, ne a = true) := by
  set z1 := z1' ++ [BSym.sep] with hz1
  have hne : z1.dropWhile ne ≠ [] := by
    intro h0; rw [List.dropWhile_eq_nil_iff] at h0
    have := h0 BSym.sep (by simp [hz1]); simp at this
  obtain ⟨a, M, hd⟩ := List.exists_cons_of_ne_nil hne
  have ha : a = BSym.sep := by
    have := List.head?_dropWhile_not ne z1
    rw [hd] at this; simp at this; cases a <;> simp_all [ne]
  subst ha
  have hz : z1 = z1.takeWhile ne ++ BSym.sep :: M := by
    rw [← hd]; exact (List.takeWhile_append_dropWhile).symm
  obtain ⟨ms, r, hM, hms, hr⟩ := exists_joinT M.length M le_rfl
  have hr0 : r = [] := by
    rcases List.eq_nil_or_concat r with h | ⟨r', c, rfl⟩
    · exact h
    · exfalso
      have hc := hr c (by simp)
      have e : z1' ++ [BSym.sep] = (z1.takeWhile ne ++ BSym.sep :: (joinT ms ++ r')) ++ [c] := by
        rw [← hz1]; conv_lhs => rw [hz, hM]
        simp
      have := (List.append_inj' e rfl).2
      simp at this; subst this; simp at hc
  subst hr0
  simp only [List.append_nil] at hM
  refine ⟨ms, ?_, ?_, hms⟩
  · conv_lhs => rw [hz, hM]
  · rw [hd, hM]; rfl

theorem F_no (x : List BSym) (h : F x ∈ targetLang) : x ∈ knapsackLang := by
  obtain ⟨I, QA, QB, hRec, hFx⟩ := h
  have hne : F x ≠ [] := by
    rw [hFx]; obtain ⟨nA, nB, pA, wA, pB⟩ := I
    simp [Instance.codeList, encNats, encNat]
  rcases F_cases x with h0 | ⟨z1', tB, tW, hB, hW, hx⟩
  · exact absurd h0 hne
  have hF := F_eq z1' tB tW hB hW
  rw [← hx] at hF
  set L := x.length with hL
  rw [hF] at hFx hne
  unfold Fbody at hFx hne
  by_cases hcB : canonTok tB = true
  swap
  · exact absurd (by rw [if_neg hcB]) hne
  rw [if_pos hcB] at hFx hne
  rcases hwd : wdig tW with _ | wd
  · rw [hwd] at hne; exact absurd rfl hne
  rw [hwd] at hFx hne
  simp only at hFx hne
  by_cases hbr : (subB (accOf (z1' ++ [BSym.sep])) wd false).2 = true
  · rw [if_pos hbr] at hne; exact absurd rfl hne
  rw [if_neg hbr] at hFx
  obtain ⟨b', hb'⟩ := (canonTok_iff tB).1 hcB
  subst hb'
  obtain ⟨W, hWenc, hWv⟩ := wdig_spec tW wd hwd
  obtain ⟨ms, hz, hM, hms⟩ := z1_split z1'
  set t1 := (z1' ++ [BSym.sep]).takeWhile ne with ht1
  have ht1ne : ∀ a ∈ t1, ne a = true := fun a ha => List.mem_takeWhile_imp ha
  set D := (subB (accOf (z1' ++ [BSym.sep])) wd false).1 with hD
  have hLb : (tokOf b').length ≤ L := by rw [hL, hx]; simp; omega
  rw [hM, outP_eq, outQA_eq, outQB_eq L b' hLb] at hFx
  -- tokens
  have hj : t1 ++ [BSym.sep, BSym.one, BSym.sep] ++ joinT ms ++ (tokOf (2 ^ L) ++ [BSym.sep]) ++
      (tokOf (2 ^ L * bval D + (2 ^ L - 1)) ++ [BSym.sep]) ++ (tokOf (b' + 2 ^ L) ++ [BSym.sep]) =
      joinT ([t1, [BSym.one]] ++ ms ++ [tokOf (2 ^ L), tokOf (2 ^ L * bval D + (2 ^ L - 1)),
        tokOf (b' + 2 ^ L)]) := by
    simp [joinT_append, joinT_cons, joinT]
  rw [hj, encNats_eq_joinT] at hFx
  have hall : ∀ t ∈ [t1, [BSym.one]] ++ ms ++ [tokOf (2 ^ L), tokOf (2 ^ L * bval D + (2 ^ L - 1)),
      tokOf (b' + 2 ^ L)], ∀ a ∈ t, ne a = true := by
    intro t ht
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with ((rfl | rfl) | ht) | (rfl | rfl | rfl)
    · exact ht1ne
    · simp
    · exact hms t ht
    all_goals exact tokOf_ne _
  have hall2 : ∀ t ∈ (I.codeList QA QB).map tokOf, ∀ a ∈ t, ne a = true := by
    intro t ht; simp only [List.mem_map] at ht; obtain ⟨k, -, rfl⟩ := ht; exact tokOf_ne k
  have heq := joinT_inj _ _ hall2 hall hFx.symm
  obtain ⟨nA, nB, pA, wA, pB⟩ := I
  simp only [Instance.codeList, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.cons.injEq] at heq
  obtain ⟨hA1, hB1, heq⟩ := heq
  have hnB : nB = 1 := tokOf_inj (hB1.trans tokOf_one.symm)
  subst hnB
  have hofB : List.ofFn pB = [pB 0] := by simp [List.ofFn_succ]
  rw [hofB, ← List.map_append] at heq
  simp only [List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] at heq
  obtain ⟨hms', heq2⟩ := List.append_inj' heq (by simp)
  simp only [List.cons.injEq, and_true] at heq2
  obtain ⟨hP0, hQA, hQB⟩ := heq2
  have hP0' := tokOf_inj hP0
  have hQA' := tokOf_inj hQA
  have hQB' := tokOf_inj hQB
  -- the prefix is the code of the first numbers
  have hMenc : joinT ms = encNats (List.ofFn pA ++ List.ofFn wA) := by
    rw [encNats_eq_joinT, ← hms', List.map_append]
  have hz1 : z1' ++ [BSym.sep] = tokOf nA ++ BSym.sep :: encNats (List.ofFn pA ++ List.ofFn wA) := by
    rw [hz, ← hMenc, ← hA1]
  have hacc : bval (accOf (z1' ++ [BSym.sep])) = wHat wA := by
    rw [hz1, accOf_eq nA (List.ofFn pA) (List.ofFn wA) (by simp) (by simp), List.sum_ofFn]; rfl
  have hle : W.toNat ≤ wHat wA := by
    by_contra hlt
    have := subB_borrow (accOf (z1' ++ [BSym.sep])) wd (by rw [hacc, hWv]; omega)
    exact hbr this
  have hsub := subB_noborrow (accOf (z1' ++ [BSym.sep])) wd (by rw [hacc, hWv]; exact hle)
  rw [hacc, hWv] at hsub
  have hDv : bval D = wHat wA - W.toNat := hsub.2
  set P := 2 ^ L with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hI : (⟨nA, 1, pA, wA, pB⟩ : Instance) = KN.mI pA wA P := by
    simp only [KN.mI, Instance.mk.injEq, heq_eq_eq, true_and]
    funext i; rw [Fin.fin_one_eq_zero i]; exact hP0'
  have hQA2 : QA = P * (wHat wA - W.toNat) + P - 1 := by rw [hQA', hDv]; omega
  rw [hI, hQA2, hQB'] at hRec
  obtain ⟨S, hSu, hSw⟩ := KN.schedNo pA wA P b' W.toNat hP1 hle hRec
  refine ⟨nA, pA, wA, (b' : ℤ), W, ⟨S, by exact_mod_cast hSu, ?_⟩, ?_⟩
  · have : (W.toNat : ℤ) ≤ ((∑ i ∈ S, wA i : ℕ) : ℤ) := by exact_mod_cast hSw
    omega
  · rw [knapsackCode_eq, encNats_cons, ← hz1, encInt_nat, ← hWenc, hx]
    simp


theorem F_correct (x : List BSym) : x ∈ knapsackLang ↔ F x ∈ targetLang := by
  constructor
  · rintro ⟨n, u, w, b, W, hK, rfl⟩; exact F_yes u w b W hK
  · exact F_no x

end KS
end KS_Spec


section KS_Loops
set_option autoImplicit false

namespace KS
open CookPvsNP ProjSchedTW.Complexity

section loops
variable {K : Type} [DecidableEq K]

abbrev St (K : Type) := K → List BSym

def bitOf : Option BSym → Bool
  | some .one => true
  | _ => false

def isD : Option BSym → Bool
  | some .sep => false
  | some _ => true
  | none => false

def carS (c : Bool) : List BSym := if c then [.one] else []

lemma isSome_carS (c : Bool) : (carS c).head?.isSome = c := by cases c <;> rfl

/-! ### adder -/

def addAct (src dst tmp car : K) (h : K → Option BSym) (j : K) : StackAct BSym :=
  if j = dst then .pop
  else if j = src then (if isD (h src) then .pop else .keep)
  else if j = tmp then .push (toB (bitOf (h dst) ^^ bitOf (h src) ^^ (h car).isSome))
  else if j = car then
    (if (bitOf (h dst) && bitOf (h src)) || ((h car).isSome && (bitOf (h dst) ^^ bitOf (h src)))
      then (if (h car).isSome then .keep else .push .one)
      else (if (h car).isSome then .pop else .keep))
  else .keep

def addTest (src dst car : K) (h : K → Option BSym) : Bool :=
  isD (h src) || (h dst).isSome || (h car).isSome

def addLoop (src dst tmp car : K) : StackProg K BSym :=
  .loop (addTest src dst car) (.act (addAct src dst tmp car))

lemma car_act (a b c : Bool) :
    StackAct.apply (if (a && b) || (c && (a ^^ b)) then (if c then .keep else .push .one)
      else (if c then .pop else .keep)) (carS c) = carS ((a && b) || (c && (a ^^ b))) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma bitOf_enc_head (x : List Bool) : bitOf (enc x).head? = x.headD false := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

lemma isSome_enc_head (x : List Bool) : (enc x).head?.isSome = !x.isEmpty := by
  cases x <;> rfl

lemma src_heads (t r : List BSym) (ht : ∀ a ∈ t, ne a = true) (hr : isD r.head? = false) :
    bitOf (t ++ r).head? = (t.map isOne).headD false ∧ isD (t ++ r).head? = !t.isEmpty := by
  cases t with
  | nil =>
    simp only [List.nil_append, List.map_nil, List.headD_nil, List.isEmpty_nil, Bool.not_true]
    refine ⟨?_, hr⟩
    rcases r with _ | ⟨a, r⟩
    · rfl
    · cases a <;> simp_all [bitOf, isD]
  | cons a t =>
    have ha := ht a (by simp)
    cases a <;> simp_all [bitOf, isD, isOne]

lemma meas_step (x y : List Bool) (c : Bool) (h0 : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    x.tail.length + y.tail.length +
      ((x.headD false && y.headD false) || (c && (x.headD false ^^ y.headD false))).toNat + 1 ≤
      x.length + y.length + c.toNat := by
  rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;>
    (try cases x0) <;> (try cases y0) <;> simp_all <;> omega

lemma test_step (x y : List Bool) (c : Bool) (h0 : ¬ (x = [] ∧ y = [] ∧ c = false)) :
    ((!y.isEmpty) || (!x.isEmpty) || c) = true := by
  rcases x with _ | ⟨x0, x⟩ <;> rcases y with _ | ⟨y0, y⟩ <;> cases c <;> simp_all

lemma exec_addLoop (src dst tmp car : K) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : src ≠ car)
    (h4 : dst ≠ tmp) (h5 : dst ≠ car) (h6 : tmp ≠ car) (r : List BSym) (hr : isD r.head? = false) :
    ∀ (N : ℕ) (x : List Bool) (t : List BSym) (c : Bool) (s : St K),
      x.length + t.length + c.toNat ≤ N → (∀ a ∈ t, ne a = true) →
      s dst = enc x → s src = t ++ r → s car = carS c →
      (addLoop src dst tmp car).Exec s
        (Function.update (Function.update (Function.update (Function.update s dst []) src r) tmp
          ((enc (addB x (t.map isOne) c)).reverse ++ s tmp)) car [])
        (3 * (addB x (t.map isOne) c).length + 1) := by
  intro N
  induction N with
  | zero =>
    intro x t c s hN ht hx hs hc
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht0 : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hc0 : c = false := by cases c <;> simp_all
    subst hx0 ht0 hc0
    have e : Function.update (Function.update (Function.update (Function.update s dst []) src r) tmp
        ((enc (addB [] (([] : List BSym).map isOne) false)).reverse ++ s tmp)) car [] = s := by
      funext k
      simp only [Function.update_apply]
      split_ifs with k1 k2 k3 k4 <;> subst_vars <;> simp_all [addB, enc, carS]
    rw [e]
    simp only [List.map_nil, addB, List.length_nil, mul_zero, zero_add]
    apply StackProg.Exec.loopFalse
    simp [addTest, hx, hs, hc, carS, enc, hr]
  | succ N ih =>
    intro x t c s hN ht hx hs hc
    have hh := src_heads t r ht hr
    by_cases h0 : x = [] ∧ t = [] ∧ c = false
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      have e : Function.update (Function.update (Function.update (Function.update s dst []) src r) tmp
          ((enc (addB [] (([] : List BSym).map isOne) false)).reverse ++ s tmp)) car [] = s := by
        funext k
        simp only [Function.update_apply]
        split_ifs with k1 k2 k3 k4 <;> subst_vars <;> simp_all [addB, enc, carS]
      rw [e]
      simp only [List.map_nil, addB, List.length_nil, mul_zero, zero_add]
      apply StackProg.Exec.loopFalse
      simp [addTest, hx, hs, hc, carS, enc, hr]
    set y := t.map isOne with hy
    have hstep := addB_step x y c (by
      intro h; apply h0; refine ⟨h.1, ?_, h.2.2⟩
      have := h.2.1; rw [hy] at this; exact List.map_eq_nil_iff.1 this)
    set x0 := x.headD false
    set y0 := y.headD false
    set c' := (x0 && y0) || (c && (x0 ^^ y0)) with hc'
    set s1 := StackProg.applyAct (addAct src dst tmp car) s with hs1
    have e_dst : s1 dst = enc x.tail := by
      simp [hs1, StackProg.applyAct, addAct, StackAct.apply, hx, enc]
    have e_src : s1 src = t.tail ++ r := by
      simp only [hs1, StackProg.applyAct, addAct, if_neg h1, if_pos rfl, hs, hh.2]
      cases t with
      | nil => simp [StackAct.apply]
      | cons a t => simp [StackAct.apply]
    have e_car : s1 car = carS c' := by
      simp only [hs1, StackProg.applyAct, addAct, if_neg h5.symm, if_neg h3.symm, if_neg h6.symm,
        if_pos rfl, hx, hs, hc, bitOf_enc_head, hh.1, isSome_carS]
      exact car_act _ _ _
    have e_tmp : s1 tmp = toB (x0 ^^ y0 ^^ c) :: s tmp := by
      have : (fun k => (s k).head?) dst = (enc x).head? := by simp [hx]
      simp only [hs1, StackProg.applyAct, addAct, if_neg h4.symm, if_neg h2.symm, ite_true]
      rw [hx, hs, hc, bitOf_enc_head, hh.1, isSome_carS]; rfl
    have e_oth : ∀ k, k ≠ src → k ≠ dst → k ≠ tmp → k ≠ car → s1 k = s k := by
      intro k k1 k2 k3 k4
      simp [hs1, StackProg.applyAct, addAct, k1, k2, k3, k4, StackAct.apply]
    have hny : ¬ (x = [] ∧ y = [] ∧ c = false) := by
      intro h; apply h0; refine ⟨h.1, ?_, h.2.2⟩
      have := h.2.1; rw [hy] at this; exact List.map_eq_nil_iff.1 this
    have hlen : x.tail.length + t.tail.length + c'.toNat ≤ N := by
      have : x.tail.length + y.tail.length + c'.toNat + 1 ≤ x.length + y.length + c.toNat :=
        meas_step x y c hny
      have e1 : y.tail.length = t.tail.length := by rw [hy]; simp
      have e2 : y.length = t.length := by rw [hy, List.length_map]
      rw [e1, e2] at this
      omega
    have hrec := ih x.tail t.tail c' s1 hlen (fun a ha => ht a (List.mem_of_mem_tail ha))
      e_dst e_src e_car
    have htest : addTest src dst car (fun k => (s k).head?) = true := by
      have := test_step x y c hny
      have e : y.isEmpty = t.isEmpty := by rw [hy]; cases t <;> rfl
      simp only [addTest]
      rw [hs, hh.2, hx, hc, isSome_enc_head, isSome_carS, ← e]; exact this
    have hyt : t.tail.map isOne = y.tail := by rw [hy, List.map_tail]
    rw [hyt] at hrec
    have hpost : Function.update (Function.update (Function.update (Function.update s1 dst [])
        src r) tmp ((enc (addB x.tail y.tail c')).reverse ++ s1 tmp)) car [] =
        Function.update (Function.update (Function.update (Function.update s dst []) src r) tmp
          ((enc (addB x y c)).reverse ++ s tmp)) car [] := by
      funext k
      simp only [Function.update_apply]
      by_cases k4 : k = car
      · simp [k4]
      by_cases k3 : k = tmp
      · subst k3; simp [k4, e_tmp, hstep, enc, c', x0, y0]
      by_cases k2 : k = src
      · subst k2; simp [h1, h2, h3]
      by_cases k1 : k = dst
      · subst k1; simp [h4, h5, Ne.symm h1]
      simp [k1, k2, k3, k4, e_oth k k2 k1 k3 k4]
    rw [hpost] at hrec
    have := StackProg.Exec.loopTrue htest (StackProg.Exec.act (addAct src dst tmp car) s) hrec
    rw [hstep] at this ⊢
    have e3 : 1 + 1 + 1 + (3 * (addB x.tail y.tail c').length + 1) =
        3 * ((x0 ^^ y0 ^^ c) :: addB x.tail y.tail c').length + 1 := by simp; ring
    rw [e3] at this
    exact this


lemma split_tok (l : List BSym) : ∃ tok rd, l = tok ++ rd ∧ (∀ a ∈ tok, ne a = true) ∧
    stopAt ne rd ∧ isD rd.head? = false ∧ l.takeWhile ne = tok ∧ l.dropWhile ne = rd := by
  refine ⟨l.takeWhile ne, l.dropWhile ne, (List.takeWhile_append_dropWhile).symm,
    fun a ha => List.mem_takeWhile_imp ha, ?_, ?_, rfl, rfl⟩
  · have := List.head?_dropWhile_not ne l
    unfold stopAt
    cases h : l.dropWhile ne with
    | nil => trivial
    | cons a r => rw [h] at this; simpa using this
  · have := List.head?_dropWhile_not ne l
    cases h : l.dropWhile ne with
    | nil => rfl
    | cons a r => rw [h] at this; simp at this; cases a <;> simp_all [isD, ne]

/-! ### summing all tokens of a stack -/

def sumBody (m3 acc tmp car : K) : StackProg K BSym :=
  .seq (addLoop m3 acc tmp car) (.seq (transferProg tmp (fun k => decide (k = acc))) (popProg m3))

def sumLoop (m3 acc tmp car : K) : StackProg K BSym :=
  .loop (fun h => (h m3).isSome) (sumBody m3 acc tmp car)

lemma exec_sumLoop (m3 acc tmp car : K) (h1 : m3 ≠ acc) (h2 : m3 ≠ tmp) (h3 : m3 ≠ car)
    (h4 : acc ≠ tmp) (h5 : acc ≠ car) (h6 : tmp ≠ car) (T : ℕ) :
    ∀ (N : ℕ) (l : List BSym) (xb : List Bool) (s : St K), l.length ≤ N →
      xb.length + 2 * l.length ≤ T →
      s m3 = l → s acc = enc xb → s tmp = [] → s car = [] →
      ∃ n ≤ l.length * (6 * T + 13) + 1, (sumLoop m3 acc tmp car).Exec s
        (Function.update (Function.update s m3 []) acc (enc (sumAcc xb l))) n := by
  intro N
  induction N with
  | zero =>
    intro l xb s hl _ hm ha _ _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    refine ⟨1, by simp, ?_⟩
    have e : Function.update (Function.update s m3 []) acc (enc (sumAcc xb [])) = s := by
      funext k; simp only [Function.update_apply, sumAcc_nil]
      split_ifs with k1 k2 <;> subst_vars <;> simp_all
    rw [e]; exact StackProg.Exec.loopFalse (by simp [hm])
  | succ N ih =>
    intro l xb s hl hT hm ha ht hc
    by_cases h0 : l = []
    · subst h0
      refine ⟨1, by simp, ?_⟩
      have e : Function.update (Function.update s m3 []) acc (enc (sumAcc xb [])) = s := by
        funext k; simp only [Function.update_apply, sumAcc_nil]
        split_ifs with k1 k2 <;> subst_vars <;> simp_all
      rw [e]; exact StackProg.Exec.loopFalse (by simp [hm])
    obtain ⟨tok, rd, hl', htokne, -, hrdD, htok, hrd⟩ := split_tok l
    have hm' : s m3 = tok ++ rd := by rw [hm, ← hl']
    have e1 := exec_addLoop m3 acc tmp car h1 h2 h3 h4 h5 h6 rd hrdD _ xb tok false s le_rfl htokne
      ha hm' (by simp [hc, carS])
    set xb' := addB xb (tok.map isOne) false with hxb'
    set s1 := Function.update (Function.update (Function.update (Function.update s acc []) m3 rd)
      tmp ((enc xb').reverse ++ s tmp)) car [] with hs1
    have e2 := exec_transfer tmp (fun k => decide (k = acc)) _ s1 rfl
    set s2 := transferStore tmp (fun k => decide (k = acc)) s1 with hs2
    have e3 := StackProg.Exec.act (fun _ k => if k = m3 then StackAct.pop else .keep) s2
    set s3 := StackProg.applyAct (fun _ k => if k = m3 then StackAct.pop else .keep) s2 with hs3
    have v_m3 : s3 m3 = rd.tail := by
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, transferStore, h1, h2, h3, h1.symm, h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Function.update_apply]
    have v_acc : s3 acc = enc xb' := by
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, transferStore, h1.symm, h4, h5, ht, h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Function.update_apply]
    have v_tmp : s3 tmp = [] := by
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, transferStore, h2.symm, h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Function.update_apply]
    have v_car : s3 car = [] := by
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, transferStore, h3.symm, h6.symm, h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Function.update_apply]
    have v_oth : ∀ k, k ≠ m3 → k ≠ acc → k ≠ tmp → k ≠ car → s3 k = s k := by
      intro k k1 k2 k3 k4
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, transferStore, k1, k2, k3, k4]
    have hlenrd : rd.tail.length + 1 ≤ l.length ∧
        tok.length + 2 * rd.tail.length + 1 ≤ 2 * l.length := by
      have e := congrArg List.length hl'
      rw [List.length_append] at e
      have := List.length_pos_of_ne_nil h0
      rcases hrd' : rd with _ | ⟨a, r⟩
      · rw [hrd'] at e; simp at e ⊢; omega
      · rw [hrd'] at e; simp at e ⊢; omega
    have hlx : xb'.length ≤ xb.length + tok.length + 1 := by
      have := length_addB_le xb (tok.map isOne) false; simpa [hxb'] using this
    obtain ⟨m, hm, e4⟩ := ih rd.tail xb' s3 (by omega) (by omega) v_m3 v_acc v_tmp v_car
    have hsum : sumAcc xb l = sumAcc xb' rd.tail := by
      rw [sumAcc, dif_neg h0, htok, hrd]
    have hpost : Function.update (Function.update s3 m3 []) acc (enc (sumAcc xb' rd.tail)) =
        Function.update (Function.update s m3 []) acc (enc (sumAcc xb l)) := by
      rw [hsum]; funext k
      simp only [Function.update_apply]
      by_cases k2 : k = acc
      · simp [k2]
      by_cases k1 : k = m3
      · simp [k1, k2]
      by_cases k3 : k = tmp
      · subst k3; simp [k1, k2, v_tmp, ht]
      by_cases k4 : k = car
      · subst k4; simp [k1, k2, v_car, hc]
      simp [k1, k2, v_oth k k1 k2 k3 k4]
    rw [hpost] at e4
    have htest : (fun h : K → Option BSym => (h m3).isSome) (fun k => (s k).head?) = true := by
      rcases l with _ | ⟨a, l⟩
      · exact absurd rfl h0
      · simp [hm]
    have hex := StackProg.Exec.loopTrue htest (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)) e4
    refine ⟨_, ?_, hex⟩
    have hs1t : (s1 tmp).length = xb'.length := by
      simp [hs1, Function.update_apply, h6, ht, enc]
    rw [hs1t]
    have hstep : 3 * xb'.length + 1 + 1 + (3 * xb'.length + 1 + 1 + 1) ≤ 6 * T + 12 := by omega
    have hmul : rd.tail.length * (6 * T + 13) + 1 + (6 * T + 13) ≤ l.length * (6 * T + 13) + 1 := by
      have : rd.tail.length + 1 ≤ l.length := by omega
      nlinarith
    omega

/-! ### skipping tokens -/

def skipBody (m3 mc : K) : StackProg K BSym :=
  .seq (mapMove ne m3 (fun _ _ => none))
    (.seq (.act (fun _ j => if j = m3 ∨ j = mc then .pop else .keep)) (popProg mc))

def skipLoop (m3 mc : K) : StackProg K BSym :=
  .loop (fun h => (h mc).isSome) (skipBody m3 mc)

lemma exec_skipLoop (m3 mc : K) (hne : m3 ≠ mc) :
    ∀ (c : ℕ) (l : List BSym) (s : St K), s mc = List.replicate c .one → s m3 = l →
      ∃ n ≤ (3 * l.length + 8) * c + 1, (skipLoop m3 mc).Exec s
        (Function.update (Function.update s mc []) m3 (dropToks ((c + 1) / 2) l)) n := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro l s hc hl
    rcases c with _ | c
    · refine ⟨1, by simp, ?_⟩
      have e : Function.update (Function.update s mc []) m3 (dropToks ((0 + 1) / 2) l) = s := by
        funext k; simp only [Function.update_apply]
        split_ifs with k1 k2 <;> subst_vars <;> simp_all [dropToks]
      rw [e]; exact StackProg.Exec.loopFalse (by simp [hc])
    obtain ⟨tok, rd, hl', htokne, hstop, -, htok, hrd⟩ := split_tok l
    have e1 := exec_mapMove ne m3 (fun _ _ => none) rd hstop tok s (by rw [hl, ← hl'])
      htokne
    set s1 := mmStore m3 (fun (_ : BSym) (_ : K) => (none : Option BSym)) tok rd s with hs1
    have e2 := StackProg.Exec.act (fun _ j => if j = m3 ∨ j = mc then StackAct.pop else .keep) s1
    set s2 := StackProg.applyAct (fun _ j => if j = m3 ∨ j = mc then StackAct.pop else .keep) s1
      with hs2
    have e3 := StackProg.Exec.act (fun _ k => if k = mc then StackAct.pop else .keep) s2
    set s3 := StackProg.applyAct (fun _ k => if k = mc then StackAct.pop else .keep) s2 with hs3
    have v_mc : s3 mc = List.replicate (c - 1) .one := by
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, mmStore, hne.symm, hc,
        List.tail_replicate]
    have v_m3 : s3 m3 = rd.tail := by
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, mmStore, hne]
    have v_oth : ∀ k, k ≠ m3 → k ≠ mc → s3 k = s k := by
      intro k k1 k2
      simp [hs3, hs2, hs1, StackProg.applyAct, StackAct.apply, mmStore, k1, k2]
    obtain ⟨m, hm, e4⟩ := ih (c - 1) (by omega) rd.tail s3 v_mc v_m3
    have hdrop : dropToks ((c + 1 + 1) / 2) l = dropToks ((c - 1 + 1) / 2) rd.tail := by
      have : (c + 1 + 1) / 2 = (c - 1 + 1) / 2 + 1 := by omega
      rw [this, dropToks, hrd]
    have hpost : Function.update (Function.update s3 mc []) m3 (dropToks ((c - 1 + 1) / 2) rd.tail)
        = Function.update (Function.update s mc []) m3 (dropToks ((c + 1 + 1) / 2) l) := by
      rw [hdrop]; funext k; simp only [Function.update_apply]
      by_cases k1 : k = m3
      · simp [k1]
      by_cases k2 : k = mc
      · simp [k1, k2]
      simp [k1, k2, v_oth k k1 k2]
    rw [hpost] at e4
    have hex := StackProg.Exec.loopTrue (by simp [hc]) (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)) e4
    refine ⟨_, ?_, hex⟩
    have hrl : rd.tail.length ≤ l.length := by
      have := congrArg List.length hl'; simp at this
      have := @List.length_tail _ rd; omega
    have htl : tok.length ≤ l.length := by
      have := congrArg List.length hl'; simp at this; omega
    have hm2 : m ≤ (3 * l.length + 8) * (c - 1) + 1 := by
      calc m ≤ (3 * rd.tail.length + 8) * (c - 1) + 1 := hm
        _ ≤ (3 * l.length + 8) * (c - 1) + 1 := by gcongr
    have : (3 * l.length + 8) * (c - 1) + (3 * l.length + 8) ≤ (3 * l.length + 8) * (c + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    omega


/-! ### scanning a token for canonicity -/

def scanAct (src bad z : K) (h : K → Option BSym) (j : K) : StackAct BSym :=
  if j = src then .pop
  else if j = z then (match h src with
    | some .zero => (if (h z).isSome then .keep else .push .one)
    | some .one => .pop
    | _ => .keep)
  else if j = bad then (match h src with
    | some .zero => .keep
    | some .one => .keep
    | _ => .push .one)
  else .keep

def scanLoop (src bad z : K) : StackProg K BSym :=
  .loop (fun h => (h src).isSome) (.act (scanAct src bad z))

lemma exec_scanLoop (src bad z : K) (h1 : src ≠ bad) (h2 : src ≠ z) (h3 : bad ≠ z) :
    ∀ (t : List BSym) (s : St K), s src = t →
      (scanLoop src bad z).Exec s
        (Function.update (Function.update (Function.update s src []) z (zF t (s z))) bad
          (List.replicate (t.countP (fun a => !isDigS a)) .one ++ s bad)) (3 * t.length + 1) := by
  intro t
  induction t with
  | nil =>
    intro s hs
    have e : Function.update (Function.update (Function.update s src []) z (zF [] (s z))) bad
        (List.replicate (([] : List BSym).countP (fun a => !isDigS a)) .one ++ s bad) = s := by
      funext k; simp only [Function.update_apply, zF, List.countP_nil, List.replicate_zero,
        List.nil_append]
      split_ifs with k1 k2 k3 <;> subst_vars <;> simp_all
    rw [e]; exact StackProg.Exec.loopFalse (by simp [hs])
  | cons a t ih =>
    intro s hs
    set s1 := StackProg.applyAct (scanAct src bad z) s with hs1
    have v_src : s1 src = t := by simp [hs1, StackProg.applyAct, scanAct, StackAct.apply, hs]
    have v_z : s1 z = zStep a (s z) := by
      simp only [hs1, StackProg.applyAct, scanAct, if_neg (Ne.symm h2), ite_true, hs,
        List.head?_cons]
      cases a <;> simp [zStep, StackAct.apply] <;> cases s z <;> simp
    have v_bad : s1 bad = (if isDigS a then s bad else .one :: s bad) := by
      simp only [hs1, StackProg.applyAct, scanAct, if_neg (Ne.symm h1), if_neg h3, ite_true, hs,
        List.head?_cons]
      cases a <;> simp [isDigS, StackAct.apply]
    have v_oth : ∀ k, k ≠ src → k ≠ z → k ≠ bad → s1 k = s k := by
      intro k k1 k2 k3; simp [hs1, StackProg.applyAct, scanAct, k1, k2, k3, StackAct.apply]
    have e := ih s1 v_src
    have hpost : Function.update (Function.update (Function.update s1 src []) z (zF t (s1 z))) bad
        (List.replicate (t.countP (fun a => !isDigS a)) .one ++ s1 bad) =
        Function.update (Function.update (Function.update s src []) z (zF (a :: t) (s z))) bad
          (List.replicate ((a :: t).countP (fun a => !isDigS a)) .one ++ s bad) := by
      funext k; simp only [Function.update_apply]
      by_cases k3 : k = bad
      · subst k3; simp only [if_true, v_bad, List.countP_cons]
        cases isDigS a <;> simp [List.replicate_succ']
      by_cases k2 : k = z
      · subst k2; simp [k3, v_z, zF]
      by_cases k1 : k = src
      · subst k1; simp [h1, h2]
      simp [k1, k2, k3, v_oth k k1 k2 k3]
    rw [hpost] at e
    have := StackProg.Exec.loopTrue (by simp [hs]) (StackProg.Exec.act (scanAct src bad z) s) e
    have h3' : 1 + 1 + 1 + (3 * t.length + 1) = 3 * (a :: t).length + 1 := by simp; ring
    rw [h3'] at this; exact this

/-! ### subtraction -/

def subAct (dst src tmp car : K) (h : K → Option BSym) (j : K) : StackAct BSym :=
  if j = dst then .pop
  else if j = src then .pop
  else if j = tmp then .push (toB (bitOf (h dst) ^^ bitOf (h src) ^^ (h car).isSome))
  else if j = car then
    (if bor (bitOf (h dst)) (bitOf (h src)) ((h car).isSome)
      then (if (h car).isSome then .keep else .push .one)
      else (if (h car).isSome then .pop else .keep))
  else .keep

def subLoop (dst src tmp car : K) : StackProg K BSym :=
  .loop (fun h => (h dst).isSome || (h src).isSome) (.act (subAct dst src tmp car))

lemma subB_step (x y : List Bool) (c : Bool) (h : ¬ (x = [] ∧ y = [])) :
    subB x y c = ((x.headD false ^^ y.headD false ^^ c) ::
      (subB x.tail y.tail (bor (x.headD false) (y.headD false) c)).1,
      (subB x.tail y.tail (bor (x.headD false) (y.headD false) c)).2) := by
  match x, y with
  | [], [] => simp at h
  | a :: xs, [] => simp [subB]
  | [], b :: ys => simp [subB]
  | a :: xs, b :: ys => simp [subB]

lemma bor_act (a b c : Bool) :
    StackAct.apply (if bor a b c then (if c then .keep else .push .one)
      else (if c then .pop else .keep)) (carS c) = carS (bor a b c) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma exec_subLoop (dst src tmp car : K) (h1 : dst ≠ src) (h2 : dst ≠ tmp) (h3 : dst ≠ car)
    (h4 : src ≠ tmp) (h5 : src ≠ car) (h6 : tmp ≠ car) :
    ∀ (N : ℕ) (x y : List Bool) (c : Bool) (s : St K), x.length + y.length ≤ N →
      s dst = enc x → s src = enc y → s car = carS c →
      (subLoop dst src tmp car).Exec s
        (Function.update (Function.update (Function.update (Function.update s dst []) src [])
          tmp ((enc (subB x y c).1).reverse ++ s tmp)) car (carS (subB x y c).2))
        (3 * max x.length y.length + 1) := by
  intro N
  induction N with
  | zero =>
    intro x y c s hN hx hy hc
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx0 hy0
    have e : Function.update (Function.update (Function.update (Function.update s dst []) src [])
        tmp ((enc (subB [] [] c).1).reverse ++ s tmp)) car (carS (subB [] [] c).2) = s := by
      funext k; simp only [Function.update_apply, subB]
      split_ifs with k1 k2 k3 k4 <;> subst_vars <;> simp_all [enc]
    rw [e]; simp only [List.length_nil, max_self, mul_zero, zero_add]
    exact StackProg.Exec.loopFalse (by simp [hx, hy, enc])
  | succ N ih =>
    intro x y c s hN hx hy hc
    by_cases h0 : x = [] ∧ y = []
    · obtain ⟨rfl, rfl⟩ := h0
      have e : Function.update (Function.update (Function.update (Function.update s dst []) src [])
          tmp ((enc (subB [] [] c).1).reverse ++ s tmp)) car (carS (subB [] [] c).2) = s := by
        funext k; simp only [Function.update_apply, subB]
        split_ifs with k1 k2 k3 k4 <;> subst_vars <;> simp_all [enc]
      rw [e]; simp only [List.length_nil, max_self, mul_zero, zero_add]
      exact StackProg.Exec.loopFalse (by simp [hx, hy, enc])
    have hstep := subB_step x y c h0
    set x0 := x.headD false
    set y0 := y.headD false
    set c' := bor x0 y0 c with hc'
    set s1 := StackProg.applyAct (subAct dst src tmp car) s with hs1
    have v_dst : s1 dst = enc x.tail := by
      simp [hs1, StackProg.applyAct, subAct, StackAct.apply, hx, enc]
    have v_src : s1 src = enc y.tail := by
      simp [hs1, StackProg.applyAct, subAct, StackAct.apply, hy, enc, Ne.symm h1]
    have v_car : s1 car = carS c' := by
      simp only [hs1, StackProg.applyAct, subAct, if_neg (Ne.symm h3), if_neg (Ne.symm h5),
        if_neg (Ne.symm h6), ite_true]
      simp only [hx, hy, hc, bitOf_enc_head, isSome_carS]
      exact bor_act _ _ _
    have v_tmp : s1 tmp = toB (x0 ^^ y0 ^^ c) :: s tmp := by
      simp only [hs1, StackProg.applyAct, subAct, if_neg (Ne.symm h2), if_neg (Ne.symm h4),
        ite_true]
      simp only [hx, hy, hc, bitOf_enc_head, isSome_carS, StackAct.apply]; rfl
    have v_oth : ∀ k, k ≠ dst → k ≠ src → k ≠ tmp → k ≠ car → s1 k = s k := by
      intro k k1 k2 k3 k4
      simp [hs1, StackProg.applyAct, subAct, k1, k2, k3, k4, StackAct.apply]
    have hlen : x.tail.length + y.tail.length ≤ N := by
      rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp_all <;> omega
    have e := ih x.tail y.tail c' s1 hlen v_dst v_src v_car
    have hpost : Function.update (Function.update (Function.update (Function.update s1 dst [])
        src []) tmp ((enc (subB x.tail y.tail c').1).reverse ++ s1 tmp)) car
          (carS (subB x.tail y.tail c').2) =
        Function.update (Function.update (Function.update (Function.update s dst []) src [])
          tmp ((enc (subB x y c).1).reverse ++ s tmp)) car (carS (subB x y c).2) := by
      funext k; simp only [Function.update_apply]
      by_cases k4 : k = car
      · simp [k4, hstep, c']
      by_cases k3 : k = tmp
      · subst k3; simp [k4, v_tmp, hstep, enc, x0, y0, c']
      by_cases k2 : k = src
      · subst k2; simp [Ne.symm h1, h4, h5]
      by_cases k1 : k = dst
      · subst k1; simp [h2, h3]
      simp [k1, k2, k3, k4, v_oth k k1 k2 k3 k4]
    rw [hpost] at e
    have htest : (fun h : K → Option BSym => (h dst).isSome || (h src).isSome)
        (fun k => (s k).head?) = true := by
      simp only [hx, hy, isSome_enc_head]
      rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp_all
    have := StackProg.Exec.loopTrue htest (StackProg.Exec.act (subAct dst src tmp car) s) e
    have hm : 1 + 1 + 1 + (3 * max x.tail.length y.tail.length + 1) =
        3 * max x.length y.length + 1 := by
      rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp_all <;> omega
    rw [hm] at this; exact this

/-! ### padding -/

lemma rep_comm (n : ℕ) (a : BSym) (X : List BSym) :
    List.replicate n a ++ a :: X = a :: (List.replicate n a ++ X) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

def padSym : Option BSym → BSym
  | some a => a
  | none => BSym.zero

def padAct (c1 tB R : K) (h : K → Option BSym) (j : K) : StackAct BSym :=
  if j = c1 then .pop else if j = tB then .pop else if j = R then .push (padSym (h tB)) else .keep

def padLoop (c1 tB R : K) : StackProg K BSym :=
  .loop (fun h => (h c1).isSome) (.act (padAct c1 tB R))

lemma exec_padLoop (c1 tB R : K) (h1 : c1 ≠ tB) (h2 : c1 ≠ R) (h3 : tB ≠ R) :
    ∀ (l d : List BSym) (s : St K), s c1 = l → s tB = d → d.length ≤ l.length →
      (padLoop c1 tB R).Exec s
        (Function.update (Function.update (Function.update s c1 []) tB []) R
          ((d ++ List.replicate (l.length - d.length) BSym.zero).reverse ++ s R)) (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro d s hl hd hdl
    have hd0 : d = [] := List.eq_nil_of_length_eq_zero (by simpa using hdl)
    subst hd0
    have e : Function.update (Function.update (Function.update s c1 []) tB []) R
        (([] ++ List.replicate (([] : List BSym).length - ([] : List BSym).length) BSym.zero).reverse
          ++ s R) = s := by
      funext k; simp only [Function.update_apply]
      split_ifs with k1 k2 k3 <;> subst_vars <;> simp_all
    rw [e]; exact StackProg.Exec.loopFalse (by simp [hl])
  | cons a l ih =>
    intro d s hl hd hdl
    set s1 := StackProg.applyAct (padAct c1 tB R) s with hs1
    have v_c1 : s1 c1 = l := by simp [hs1, StackProg.applyAct, padAct, StackAct.apply, hl]
    have v_tB : s1 tB = d.tail := by
      simp [hs1, StackProg.applyAct, padAct, StackAct.apply, hd, Ne.symm h1]
    have v_R : s1 R = padSym d.head? :: s R := by
      simp [hs1, StackProg.applyAct, padAct, StackAct.apply, hd, Ne.symm h2, Ne.symm h3]
    have v_oth : ∀ k, k ≠ c1 → k ≠ tB → k ≠ R → s1 k = s k := by
      intro k k1 k2 k3; simp [hs1, StackProg.applyAct, padAct, k1, k2, k3, StackAct.apply]
    have e := ih d.tail s1 v_c1 v_tB (by rcases d with _ | ⟨b, d⟩ <;> simp_all)
    have hpost : Function.update (Function.update (Function.update s1 c1 []) tB []) R
        ((d.tail ++ List.replicate (l.length - d.tail.length) BSym.zero).reverse ++ s1 R) =
        Function.update (Function.update (Function.update s c1 []) tB []) R
          ((d ++ List.replicate ((a :: l).length - d.length) BSym.zero).reverse ++ s R) := by
      funext k; simp only [Function.update_apply]
      by_cases k3 : k = R
      · simp only [k3, if_true, v_R]
        rcases d with _ | ⟨b, d⟩
        · simp [padSym, rep_comm, List.replicate_succ]
        · simp at hdl
          simp [padSym, show l.length + 1 - (d.length + 1) = l.length - d.length by omega]
      by_cases k2 : k = tB
      · subst k2; simp [h3]
      by_cases k1 : k = c1
      · subst k1; simp [h1, h2]
      simp [k1, k2, k3, v_oth k k1 k2 k3]
    rw [hpost] at e
    have := StackProg.Exec.loopTrue (by simp [hl]) (StackProg.Exec.act (padAct c1 tB R) s) e
    have h3' : 1 + 1 + 1 + (3 * l.length + 1) = 3 * (a :: l).length + 1 := by simp; ring
    rw [h3'] at this; exact this

end loops

end KS
end KS_Loops


section KS_Mach
set_option autoImplicit false

namespace KS
open CookPvsNP ProjSchedTW.Complexity

inductive Key
  | inp | rv | cnt | tW | tB | pre | R | m2 | m3 | mc | acc | tmp | car | bad | z | cB | cW | c1
  | sc | d2 | out
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .rv, .cnt, .tW, .tB, .pre, .R, .m2, .m3, .mc, .acc, .tmp, .car, .bad, .z, .cB,
    .cW, .c1, .sc, .d2, .out}
  complete := by intro x; cases x <;> simp

structure Cfg where
  inp : List BSym := []
  rv : List BSym := []
  cnt : List BSym := []
  tW : List BSym := []
  tB : List BSym := []
  pre : List BSym := []
  R : List BSym := []
  m2 : List BSym := []
  m3 : List BSym := []
  mc : List BSym := []
  acc : List BSym := []
  tmp : List BSym := []
  car : List BSym := []
  bad : List BSym := []
  z : List BSym := []
  cB : List BSym := []
  cW : List BSym := []
  c1 : List BSym := []
  sc : List BSym := []
  d2 : List BSym := []
  out : List BSym := []

def Cfg.st (c : Cfg) : St Key := fun k =>
  match k with
  | .inp => c.inp | .rv => c.rv | .cnt => c.cnt | .tW => c.tW | .tB => c.tB | .pre => c.pre
  | .R => c.R | .m2 => c.m2 | .m3 => c.m3 | .mc => c.mc | .acc => c.acc | .tmp => c.tmp
  | .car => c.car | .bad => c.bad | .z => c.z | .cB => c.cB | .cW => c.cW | .c1 => c.c1
  | .sc => c.sc | .d2 => c.d2 | .out => c.out

/-! ## Programs -/

def skipP : StackProg Key BSym := .act (fun _ _ => .keep)

def guard (p q : StackProg Key BSym) : StackProg Key BSym :=
  .seq p (.branch (fun h => (h .bad).isNone) q skipP)

def chkSep (k : Key) : StackProg Key BSym :=
  .act (fun h j => if h k = some .sep then (if j = k then .pop else .keep)
    else (if j = .bad then .push .one else .keep))

def chkNE (k : Key) : StackProg Key BSym :=
  .act (fun h j => if (h k).isSome then .keep else (if j = .bad then .push .one else .keep))

def moveTok (src dst : Key) : StackProg Key BSym :=
  mapMove ne src (fun a j => if j = dst then some a else none)

def moveOne (src dst : Key) : StackProg Key BSym :=
  .act (fun h j => if j = src then .pop else if j = dst then
    (match h src with
     | some a => .push a
     | none => .keep) else .keep)

def zcheck : StackProg Key BSym :=
  .act (fun h j => if (h .z).isSome then
    (if j = .bad then .push .one else if j = .z then .pop else .keep) else .keep)

def borrowChk : StackProg Key BSym :=
  .act (fun h j => if (h .car).isSome then (if j = .bad then .push .one else .keep) else .keep)

def g10 (a : BSym) (j : Key) : Option BSym :=
  if j = .R ∨ j = .m2 then some a else if j = .mc ∧ a = .sep then some .one else none

def constLoop (c : Key) (a : BSym) : StackProg Key BSym :=
  mapMove (fun _ => true) c (fun _ j => if j = .R then some a else none)

def stripP : StackProg Key BSym := mapMove (fun a => decide (a = .zero)) .R (fun _ _ => none)

def PA : StackProg Key BSym := transferProg .inp (fun j => decide (j = .rv ∨ j = .cnt))
def PB : StackProg Key BSym := chkSep .rv
def PC : StackProg Key BSym := .seq (moveTok .rv .tW) (chkSep .rv)
def PD : StackProg Key BSym := .seq (moveTok .rv .tB) (chkNE .rv)
def PE : StackProg Key BSym :=
  .seq (transferProg .rv (fun j => decide (j = .pre))) <|
  .seq (moveTok .pre .R) <| .seq (moveOne .pre .R) <| .seq (pushProg .R .one) <|
  .seq (pushProg .R .sep) <| .seq (mapMove (fun _ => true) .pre g10) <|
  .seq (transferProg .m2 (fun j => decide (j = .m3))) <| .seq (skipLoop .m3 .mc) <|
  .seq (sumLoop .m3 .acc .tmp .car) <| .seq (copyProg .tB .cB .sc) <|
  .seq (scanLoop .cB .bad .z) zcheck
def PF : StackProg Key BSym :=
  .branch (fun h => decide (h .tW = some .minus))
    (.seq (popProg .tW) (.seq (chkNE .tW) (.seq (scanLoop .tW .bad .z) zcheck)))
    (.seq (copyProg .tW .cW .sc) (.seq (scanLoop .cW .bad .z) zcheck))
def PG : StackProg Key BSym := .seq (subLoop .acc .tW .tmp .car) borrowChk
def PH : StackProg Key BSym :=
  .seq (transferProg .tmp (fun j => decide (j = .d2))) <|
  .seq (copyProg .cnt .c1 .sc) <| .seq (constLoop .c1 .zero) <| .seq (pushProg .R .one) <|
  .seq (pushProg .R .sep) <|
  .seq (copyProg .cnt .c1 .sc) <| .seq (constLoop .c1 .one) <|
  .seq (transferProg .d2 (fun j => decide (j = .R))) <| .seq stripP <| .seq (pushProg .R .sep) <|
  .seq (copyProg .cnt .c1 .sc) <| .seq (padLoop .c1 .tB .R) <| .seq (pushProg .R .one) <|
  .seq (pushProg .R .sep) (transferProg .R (fun j => decide (j = .out)))

def prog6 : StackProg Key BSym := guard PG PH
def prog5 : StackProg Key BSym := guard PF prog6
def prog4 : StackProg Key BSym := guard PE prog5
def prog3 : StackProg Key BSym := guard PD prog4
def prog2 : StackProg Key BSym := guard PC prog3
def prog1 : StackProg Key BSym := guard PB prog2
def mainProg : StackProg Key BSym := .seq PA prog1

/-! ## guards -/

lemma exec_skipP (s : St Key) : skipP.Exec s s 1 := by
  have := StackProg.Exec.act (fun (_ : Key → Option BSym) (_ : Key) => (StackAct.keep : StackAct BSym)) s
  have e : StackProg.applyAct (fun (_ : Key → Option BSym) (_ : Key) =>
      (StackAct.keep : StackAct BSym)) s = s := by
    funext k; simp [StackProg.applyAct, StackAct.apply]
  rw [e] at this; exact this

lemma guard_bad {p q : StackProg Key BSym} {s t : St Key} {n : ℕ} (hp : p.Exec s t n)
    (hb : t .bad ≠ []) : (guard p q).Exec s t (n + 1 + (1 + 1)) := by
  refine StackProg.Exec.seq hp (StackProg.Exec.branchFalse ?_ (exec_skipP t))
  cases h : t .bad with
  | nil => exact absurd h hb
  | cons a l => simp [h]

lemma guard_ok {p q : StackProg Key BSym} {s t u : St Key} {n m : ℕ} (hp : p.Exec s t n)
    (hb : t .bad = []) (hq : q.Exec t u m) : (guard p q).Exec s u (n + 1 + (1 + m)) :=
  StackProg.Exec.seq hp (StackProg.Exec.branchTrue (by simp [hb]) hq)

def Cfg.set (c : Cfg) : Key → List BSym → Cfg
  | .inp, v => { c with inp := v }
  | .rv, v => { c with rv := v }
  | .cnt, v => { c with cnt := v }
  | .tW, v => { c with tW := v }
  | .tB, v => { c with tB := v }
  | .pre, v => { c with pre := v }
  | .R, v => { c with R := v }
  | .m2, v => { c with m2 := v }
  | .m3, v => { c with m3 := v }
  | .mc, v => { c with mc := v }
  | .acc, v => { c with acc := v }
  | .tmp, v => { c with tmp := v }
  | .car, v => { c with car := v }
  | .bad, v => { c with bad := v }
  | .z, v => { c with z := v }
  | .cB, v => { c with cB := v }
  | .cW, v => { c with cW := v }
  | .c1, v => { c with c1 := v }
  | .sc, v => { c with sc := v }
  | .d2, v => { c with d2 := v }
  | .out, v => { c with out := v }

lemma st_set (c : Cfg) (k : Key) (v : List BSym) : Function.update c.st k v = (c.set k v).st := by
  funext j; cases k <;> cases j <;> rfl

lemma st_apply (c : Cfg) (k : Key) : c.st k = (match k with
  | .inp => c.inp | .rv => c.rv | .cnt => c.cnt | .tW => c.tW | .tB => c.tB | .pre => c.pre
  | .R => c.R | .m2 => c.m2 | .m3 => c.m3 | .mc => c.mc | .acc => c.acc | .tmp => c.tmp
  | .car => c.car | .bad => c.bad | .z => c.z | .cB => c.cB | .cW => c.cW | .c1 => c.c1
  | .sc => c.sc | .d2 => c.d2 | .out => c.out) := rfl

@[simp] lemma st_inp (c : Cfg) : c.st .inp = c.inp := rfl
@[simp] lemma st_rv (c : Cfg) : c.st .rv = c.rv := rfl
@[simp] lemma st_cnt (c : Cfg) : c.st .cnt = c.cnt := rfl
@[simp] lemma st_tW (c : Cfg) : c.st .tW = c.tW := rfl
@[simp] lemma st_tB (c : Cfg) : c.st .tB = c.tB := rfl
@[simp] lemma st_pre (c : Cfg) : c.st .pre = c.pre := rfl
@[simp] lemma st_R (c : Cfg) : c.st .R = c.R := rfl
@[simp] lemma st_m2 (c : Cfg) : c.st .m2 = c.m2 := rfl
@[simp] lemma st_m3 (c : Cfg) : c.st .m3 = c.m3 := rfl
@[simp] lemma st_mc (c : Cfg) : c.st .mc = c.mc := rfl
@[simp] lemma st_acc (c : Cfg) : c.st .acc = c.acc := rfl
@[simp] lemma st_tmp (c : Cfg) : c.st .tmp = c.tmp := rfl
@[simp] lemma st_car (c : Cfg) : c.st .car = c.car := rfl
@[simp] lemma st_bad (c : Cfg) : c.st .bad = c.bad := rfl
@[simp] lemma st_z (c : Cfg) : c.st .z = c.z := rfl
@[simp] lemma st_cB (c : Cfg) : c.st .cB = c.cB := rfl
@[simp] lemma st_cW (c : Cfg) : c.st .cW = c.cW := rfl
@[simp] lemma st_c1 (c : Cfg) : c.st .c1 = c.c1 := rfl
@[simp] lemma st_sc (c : Cfg) : c.st .sc = c.sc := rfl
@[simp] lemma st_d2 (c : Cfg) : c.st .d2 = c.d2 := rfl
@[simp] lemma st_out (c : Cfg) : c.st .out = c.out := rfl

/-! ## generic store shapes as updates -/

lemma transfer1 (src dst : Key) (h : src ≠ dst) (s : St Key) :
    transferStore src (fun j => decide (j = dst)) s =
      Function.update (Function.update s src []) dst ((s src).reverse ++ s dst) := by
  funext k; simp only [transferStore, Function.update_apply]
  by_cases k1 : k = src
  · subst k1; simp [h]
  · by_cases k2 : k = dst
    · subst k2; simp [Ne.symm h]
    · simp [k1, k2]

lemma transfer2 (src d1 d2 : Key) (h1 : src ≠ d1) (h2 : src ≠ d2) (h3 : d1 ≠ d2) (s : St Key) :
    transferStore src (fun j => decide (j = d1 ∨ j = d2)) s =
      Function.update (Function.update (Function.update s src []) d1 ((s src).reverse ++ s d1)) d2
        ((s src).reverse ++ s d2) := by
  funext k; simp only [transferStore, Function.update_apply]
  by_cases k1 : k = src
  · subst k1; simp [h1, h2]
  · by_cases k2 : k = d1
    · subst k2; simp [k1, h3]
    · by_cases k3 : k = d2
      · subst k3; simp [Ne.symm h2]
      · simp [k1, k2, k3]

lemma mm1 (src dst : Key) (h : src ≠ dst) (t r : List BSym) (s : St Key) :
    mmStore src (fun a j => if j = dst then some a else none) t r s =
      Function.update (Function.update s src r) dst (t.reverse ++ s dst) := by
  funext k; simp only [mmStore, Function.update_apply]
  by_cases k1 : k = src
  · subst k1; simp [h]
  · by_cases k2 : k = dst
    · subst k2; simp [k1]
    · simp [k1, k2]

lemma mm0 (src : Key) (t r : List BSym) (s : St Key) :
    mmStore src (fun (_ : BSym) (_ : Key) => (none : Option BSym)) t r s =
      Function.update s src r := by
  funext k; simp only [mmStore, Function.update_apply]
  by_cases k1 : k = src <;> simp [k1]

lemma mmC (src : Key) (a : BSym) (h : src ≠ .R) (t r : List BSym) (s : St Key) :
    mmStore src (fun _ j => if j = .R then some a else none) t r s =
      Function.update (Function.update s src r) .R (List.replicate t.length a ++ s .R) := by
  funext k; simp only [mmStore, Function.update_apply]
  by_cases k1 : k = src
  · subst k1; simp [h]
  · by_cases k2 : k = .R
    · subst k2
      simp only [k1, if_false, if_true]
      congr 1
      induction t with
      | nil => rfl
      | cons b t ih => simp [List.filterMap_append, ih, List.replicate_succ']
    · simp [k1, k2]

lemma filterMap_sep (l : List BSym) :
    l.filterMap (fun a => if a = .sep then some BSym.one else none) =
      List.replicate (l.count .sep) .one := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.count_cons]
    cases a <;> simp [ih, List.replicate_succ]

lemma mm10 (t : List BSym) (s : St Key) :
    mmStore .pre g10 t [] s =
      Function.update (Function.update (Function.update (Function.update s .pre []) .R
        (t.reverse ++ s .R)) .m2 (t.reverse ++ s .m2)) .mc
        (List.replicate (t.count .sep) .one ++ s .mc) := by
  funext k; simp only [mmStore, Function.update_apply]
  cases k <;> simp [g10]
  · rw [filterMap_sep]; simp


lemma exec_push (k : Key) (a : BSym) (s : St Key) :
    (pushProg k a).Exec s (Function.update s k (a :: s k)) 1 := by
  have := StackProg.Exec.act (fun (_ : Key → Option BSym) j => if j = k then StackAct.push a
    else .keep) s
  have e : StackProg.applyAct (fun (_ : Key → Option BSym) j => if j = k then StackAct.push a
      else .keep) s = Function.update s k (a :: s k) := by
    funext j; by_cases h : j = k
    · subst h; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, h]
  rw [e] at this; exact this

lemma exec_pop (k : Key) (s : St Key) :
    (popProg k).Exec s (Function.update s k (s k).tail) 1 := by
  have := StackProg.Exec.act (fun (_ : Key → Option BSym) j => if j = k then StackAct.pop
    else (.keep : StackAct BSym)) s
  have e : StackProg.applyAct (fun (_ : Key → Option BSym) j => if j = k then StackAct.pop
      else (.keep : StackAct BSym)) s = Function.update s k (s k).tail := by
    funext j; by_cases h : j = k
    · subst h; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, h]
  rw [e] at this; exact this

lemma enc_rev_split (D : List Bool) : ∃ j, (enc D).reverse =
    List.replicate j BSym.zero ++ (enc (Nat.bits (bval D))).reverse := by
  obtain ⟨j, hj⟩ := exists_canon_split D
  refine ⟨j, ?_⟩
  conv_lhs => rw [hj]
  simp [enc, toB, List.map_replicate]

lemma head_rev_bits (D : ℕ) (X : List BSym) (hX : X.head? ≠ some BSym.zero) :
    ((enc (Nat.bits D)).reverse ++ X).head? ≠ some BSym.zero := by
  rcases Nat.eq_zero_or_pos D with h0 | hpos
  · subst h0; simpa [enc] using hX
  · have hc := (canon_bits_bval D).1
    have hne : Nat.bits D ≠ [] := by
      intro h; have := (canon_bits_bval D).2; rw [h] at this; simp [bval] at this; omega
    obtain ⟨l, b, hl⟩ := List.eq_nil_or_concat (Nat.bits D) |>.resolve_left hne
    have hb : b = true := by
      have : Canon (l ++ [b]) := by rw [← List.concat_eq_append, ← hl]; exact hc
      clear hl hc
      induction l with
      | nil => exact this.1 rfl
      | cons a l ih => exact ih this.2
    rw [hl, hb]; simp [enc, toB]

lemma run_PH (c : Cfg) (D : List Bool) (L : ℕ) (hL : 1 ≤ L) (htmp : c.tmp = (enc D).reverse)
    (hcnt : c.cnt.length = L) (hc1 : c.c1 = []) (hsc : c.sc = []) (hd2 : c.d2 = [])
    (htBL : c.tB.length ≤ L) (hout : c.out = []) :
    ∃ t n, n ≤ 40 * L + 3 * c.R.length + 12 * D.length + 100 ∧ PH.Exec c.st t n ∧
      t .out = c.R.reverse ++ outP L ++ outQA L D ++ outQB L c.tB := by
  -- 1. transfer tmp → d2
  have e1 := exec_transfer .tmp (fun j => decide (j = .d2)) c.tmp c.st rfl
  rw [transfer1 _ _ (by decide), st_set, st_set] at e1
  set a1 := (c.set .tmp []).set .d2 ((c.st .tmp).reverse ++ c.st .d2) with ha1
  -- 2. copy cnt → c1
  have e2 := exec_copy (K := Key) (A := BSym) .cnt .c1 .sc (by decide) (by decide) (by decide) a1.st
    (by simp [ha1, Cfg.set, hsc])
  rw [st_set] at e2
  set a2 := a1.set .c1 (a1.st .cnt ++ a1.st .c1) with ha2
  -- 3. constLoop zero
  have e3 := exec_mapMove (fun _ => true) .c1 (fun _ j => if j = .R then some BSym.zero else none)
    [] trivial a2.c1 a2.st (by simp) (by simp)
  rw [mmC _ _ (by decide), st_set, st_set] at e3
  set a3 := (a2.set .c1 []).set .R (List.replicate a2.c1.length BSym.zero ++ a2.st .R) with ha3
  -- 4. push one, sep
  have e4 := exec_push .R BSym.one a3.st
  rw [st_set] at e4
  set a4 := a3.set .R (BSym.one :: a3.st .R) with ha4
  have e5 := exec_push .R BSym.sep a4.st
  rw [st_set] at e5
  set a5 := a4.set .R (BSym.sep :: a4.st .R) with ha5
  -- 6. copy cnt → c1 ; constLoop one
  have e6 := exec_copy (K := Key) (A := BSym) .cnt .c1 .sc (by decide) (by decide) (by decide) a5.st
    (by simp [ha5, ha4, ha3, ha2, ha1, Cfg.set, hsc])
  rw [st_set] at e6
  set a6 := a5.set .c1 (a5.st .cnt ++ a5.st .c1) with ha6
  have e7 := exec_mapMove (fun _ => true) .c1 (fun _ j => if j = .R then some BSym.one else none)
    [] trivial a6.c1 a6.st (by simp) (by simp)
  rw [mmC _ _ (by decide), st_set, st_set] at e7
  set a7 := (a6.set .c1 []).set .R (List.replicate a6.c1.length BSym.one ++ a6.st .R) with ha7
  -- 8. transfer d2 → R
  have e8 := exec_transfer .d2 (fun j => decide (j = .R)) a7.d2 a7.st rfl
  rw [transfer1 _ _ (by decide), st_set, st_set] at e8
  set a8 := (a7.set .d2 []).set .R ((a7.st .d2).reverse ++ a7.st .R) with ha8
  -- 9. strip
  obtain ⟨j, hj⟩ := enc_rev_split D
  have hR8 : a8.R = List.replicate j BSym.zero ++ ((enc (Nat.bits (bval D))).reverse ++
      (List.replicate L BSym.one ++ (BSym.sep :: BSym.one :: (List.replicate L BSym.zero ++ c.R)))) := by
    simp [ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, htmp, hd2, hc1, hcnt, hj]
  have hstop : stopAt (fun a => decide (a = BSym.zero)) ((enc (Nat.bits (bval D))).reverse ++
      (List.replicate L BSym.one ++ (BSym.sep :: BSym.one :: (List.replicate L BSym.zero ++ c.R)))) := by
    have hX : (List.replicate L BSym.one ++ (BSym.sep :: BSym.one ::
        (List.replicate L BSym.zero ++ c.R))).head? ≠ some BSym.zero := by
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      simp [List.replicate_succ]
    have := head_rev_bits (bval D) _ hX
    unfold stopAt
    revert this
    cases ((enc (Nat.bits (bval D))).reverse ++ (List.replicate L BSym.one ++
      (BSym.sep :: BSym.one :: (List.replicate L BSym.zero ++ c.R)))) with
    | nil => intro; trivial
    | cons a r => intro h; simp at h ⊢; exact h
  have e9 := exec_mapMove (fun a => decide (a = BSym.zero)) .R (fun _ _ => none) _ hstop
    (List.replicate j BSym.zero) a8.st (by rw [st_R, hR8]) (by simp)
  rw [mm0, st_set] at e9
  set a9 := a8.set .R ((enc (Nat.bits (bval D))).reverse ++
      (List.replicate L BSym.one ++ (BSym.sep :: BSym.one :: (List.replicate L BSym.zero ++ c.R))))
    with ha9
  have e10 := exec_push .R BSym.sep a9.st
  rw [st_set] at e10
  set a10 := a9.set .R (BSym.sep :: a9.st .R) with ha10
  -- 11. copy cnt → c1 ; pad
  have e11 := exec_copy (K := Key) (A := BSym) .cnt .c1 .sc (by decide) (by decide) (by decide)
    a10.st (by simp [ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hsc])
  rw [st_set] at e11
  set a11 := a10.set .c1 (a10.st .cnt ++ a10.st .c1) with ha11
  have hc111 : a11.c1 = c.cnt := by
    simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set]
  have htB11 : a11.tB = c.tB := by
    simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set]
  have e12 := exec_padLoop (K := Key) .c1 .tB .R (by decide) (by decide) (by decide) a11.c1 a11.tB
    a11.st rfl rfl (by rw [hc111, htB11, hcnt]; exact htBL)
  rw [st_set, st_set, st_set] at e12
  set a12 := ((a11.set .c1 []).set .tB []).set .R ((a11.tB ++ List.replicate (a11.c1.length -
    a11.tB.length) BSym.zero).reverse ++ a11.st .R) with ha12
  have e13 := exec_push .R BSym.one a12.st
  rw [st_set] at e13
  set a13 := a12.set .R (BSym.one :: a12.st .R) with ha13
  have e14 := exec_push .R BSym.sep a13.st
  rw [st_set] at e14
  set a14 := a13.set .R (BSym.sep :: a13.st .R) with ha14
  have e15 := exec_transfer .R (fun j => decide (j = .out)) a14.R a14.st rfl
  rw [transfer1 _ _ (by decide), st_set, st_set] at e15
  set a15 := (a14.set .R []).set .out ((a14.st .R).reverse ++ a14.st .out) with ha15
  have hall := StackProg.Exec.seq e1 <| StackProg.Exec.seq e2 <| StackProg.Exec.seq e3 <|
    StackProg.Exec.seq e4 <| StackProg.Exec.seq e5 <| StackProg.Exec.seq e6 <|
    StackProg.Exec.seq e7 <| StackProg.Exec.seq e8 <| StackProg.Exec.seq e9 <|
    StackProg.Exec.seq e10 <| StackProg.Exec.seq e11 <| StackProg.Exec.seq e12 <|
    StackProg.Exec.seq e13 <| StackProg.Exec.seq e14 e15
  refine ⟨a15.st, _, ?_, hall, ?_⟩
  · have hpad : c.tB.length + (L - c.tB.length) = L := by omega
    have hR14 : a14.R.length ≤ c.R.length + 3 * L + (Nat.bits (bval D)).length + 10 := by
      simp [ha14, ha13, ha12, ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set,
        hcnt, hc1, enc]
      omega
    have hbl : (Nat.bits (bval D)).length ≤ D.length := by
      have := bits_length_le_of_lt (bval_lt D); exact this
    have hjD : j ≤ D.length := by
      have := congrArg List.length hj; simp [enc] at this; omega
    simp only [st_cnt, st_R, List.length_replicate, List.length_append, List.length_reverse]
    simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hcnt, hc1, hd2, htmp,
      enc]
    omega
  · simp only [st_out]
    simp [ha15, ha14, ha13, ha12, ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set,
      hcnt, hc1, hout, outP, outQA, outQB, enc, toB, List.map_replicate]


/-! ## small actions -/

lemma act_eq {f : (Key → Option BSym) → Key → StackAct BSym} {s t : St Key}
    (h : StackProg.applyAct f s = t) : (StackProg.act f).Exec s t 1 := by
  rw [← h]; exact StackProg.Exec.act f s

lemma exec_borrowChk (c : Cfg) :
    borrowChk.Exec c.st (if c.car = [] then c else c.set .bad (.one :: c.bad)).st 1 := by
  apply act_eq
  funext j
  by_cases h : c.car = []
  · rw [if_pos h]; cases j <;> simp [StackProg.applyAct, StackAct.apply, h]
  · rw [if_neg h]
    have : (c.car.head?).isSome = true := by cases hc : c.car <;> simp_all
    cases j <;> simp [StackProg.applyAct, StackAct.apply, this, Cfg.set, Cfg.st]

lemma exec_zcheck (c : Cfg) :
    zcheck.Exec c.st (if c.z = [] then c else (c.set .bad (.one :: c.bad)).set .z c.z.tail).st 1 := by
  apply act_eq
  funext j
  by_cases h : c.z = []
  · rw [if_pos h]; cases j <;> simp [StackProg.applyAct, StackAct.apply, h]
  · rw [if_neg h]
    have : (c.z.head?).isSome = true := by cases hc : c.z <;> simp_all
    cases j <;> simp [StackProg.applyAct, StackAct.apply, this, Cfg.set, Cfg.st]

lemma exec_chkNE (s : St Key) (k : Key) (hk : k ≠ .bad) :
    (chkNE k).Exec s (if s k = [] then Function.update s .bad (.one :: s .bad) else s) 1 := by
  apply act_eq
  funext j
  by_cases h : s k = []
  · rw [if_pos h]
    by_cases hj : j = .bad
    · subst hj; simp [StackProg.applyAct, StackAct.apply, h]
    · simp [StackProg.applyAct, StackAct.apply, h, hj]
  · rw [if_neg h]
    have : (s k).head?.isSome = true := by cases hc : s k <;> simp_all
    simp [StackProg.applyAct, StackAct.apply, this]

lemma exec_chkSep (s : St Key) (k : Key) (hk : k ≠ .bad) :
    (chkSep k).Exec s (if (s k).head? = some .sep then Function.update s k (s k).tail
      else Function.update s .bad (.one :: s .bad)) 1 := by
  apply act_eq
  funext j
  by_cases h : (s k).head? = some .sep
  · rw [if_pos h]
    by_cases hj : j = k
    · subst hj; simp [StackProg.applyAct, StackAct.apply, h]
    · simp [StackProg.applyAct, StackAct.apply, h, hj]
  · rw [if_neg h]
    by_cases hj : j = .bad
    · subst hj; simp [StackProg.applyAct, StackAct.apply, h]
    · simp [StackProg.applyAct, StackAct.apply, h, hj]

lemma zF_cases (t : List BSym) (z : List BSym) (hz : z = [] ∨ z = [.one]) :
    zF t z = [] ∨ zF t z = [.one] := by
  induction t generalizing z with
  | nil => simpa [zF] using hz
  | cons a t ih =>
    apply ih
    rcases hz with rfl | rfl <;> cases a <;> simp [zStep]

lemma canonTok_iff' (t : List BSym) :
    canonTok t = true ↔ t.countP (fun a => !isDigS a) = 0 ∧ zF t [] = [] := by
  simp only [canonTok, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, List.countP_eq_zero]
  simp

/-! ## level 6: subtraction then output -/

lemma run_prog6 (c : Cfg) (xb wd : List Bool) (L : ℕ) (hL : 1 ≤ L) (hacc : c.acc = enc xb)
    (htW : c.tW = enc wd) (htmp : c.tmp = []) (hcar : c.car = []) (hbad : c.bad = [])
    (hcnt : c.cnt.length = L) (hc1 : c.c1 = []) (hsc : c.sc = []) (hd2 : c.d2 = [])
    (htBL : c.tB.length ≤ L) (hout : c.out = []) :
    ∃ t n, n ≤ 40 * L + 3 * c.R.length + 15 * (xb.length + wd.length) + 200 ∧
      prog6.Exec c.st t n ∧
      t .out = (if (subB xb wd false).2 = true then [] else
        c.R.reverse ++ outP L ++ outQA L (subB xb wd false).1 ++ outQB L c.tB) := by
  have e1 := exec_subLoop (K := Key) .acc .tW .tmp .car (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) _ xb wd false c.st le_rfl hacc htW (by simp [hcar, carS])
  rw [st_set, st_set, st_set, st_set] at e1
  set D := (subB xb wd false).1 with hD
  set a1 := (((c.set .acc []).set .tW []).set .tmp ((enc D).reverse ++ c.st .tmp)).set .car
    (carS (subB xb wd false).2) with ha1
  have e2 := exec_borrowChk a1
  have hDl : D.length ≤ xb.length + wd.length := by
    rw [hD, length_subB]; omega
  by_cases hbr : (subB xb wd false).2 = true
  · have hc : a1.car ≠ [] := by simp [ha1, Cfg.set, hbr, carS]
    rw [if_neg hc] at e2
    have := guard_bad (q := PH) (StackProg.Exec.seq e1 e2) (by simp [Cfg.set])
    refine ⟨_, _, ?_, this, ?_⟩
    · omega
    · rw [if_pos hbr]; simp [ha1, Cfg.set, hout]
  · have hc : a1.car = [] := by simp [ha1, Cfg.set, hbr, carS]
    rw [if_pos hc] at e2
    obtain ⟨t, n, hn, e3, ho⟩ := run_PH a1 D L hL (by simp [ha1, Cfg.set, htmp])
      (by simp [ha1, Cfg.set, hcnt]) (by simp [ha1, Cfg.set, hc1]) (by simp [ha1, Cfg.set, hsc])
      (by simp [ha1, Cfg.set, hd2]) (by simp [ha1, Cfg.set, htBL]) (by simp [ha1, Cfg.set, hout])
    have := guard_ok (StackProg.Exec.seq e1 e2) (by simp [ha1, Cfg.set, hbad]) e3
    refine ⟨t, _, ?_, this, ?_⟩
    · have hR : a1.R = c.R := by simp [ha1, Cfg.set]
      rw [hR] at hn; omega
    · rw [if_neg hbr, ho]; simp [ha1, Cfg.set]


lemma exec_zcheck' (s : St Key) :
    zcheck.Exec s (if s .z = [] then s else
      Function.update (Function.update s .bad (.one :: s .bad)) .z (s .z).tail) 1 := by
  apply act_eq
  funext j
  by_cases h : s .z = []
  · rw [if_pos h]; simp [StackProg.applyAct, StackAct.apply, h]
  · rw [if_neg h]
    have : (s .z).head?.isSome = true := by cases hc : s .z <;> simp_all
    by_cases h1 : j = .bad
    · subst h1; simp [StackProg.applyAct, StackAct.apply, this]
    by_cases h2 : j = .z
    · subst h2; simp [StackProg.applyAct, StackAct.apply, this]
    simp [StackProg.applyAct, StackAct.apply, this, h1, h2]

lemma scan_z (s : St Key) (src : Key) (h1 : src ≠ .bad) (h2 : src ≠ .z) (h3 : src ≠ .out)
    (t : List BSym)
    (hs : s src = t) (hz : s .z = []) :
    ∃ s', (StackProg.seq (scanLoop src .bad .z) zcheck).Exec s s' (3 * t.length + 3) ∧
      (canonTok t = true → s' = Function.update s src []) ∧ (canonTok t = false → s' .bad ≠ []) ∧
      s' .out = s .out := by
  have e1 := exec_scanLoop src .bad .z h1 h2 (by decide) t s hs
  set s1 := Function.update (Function.update (Function.update s src []) .z (zF t (s .z))) .bad
    (List.replicate (t.countP (fun a => !isDigS a)) .one ++ s .bad) with hs1
  have e2 := exec_zcheck' s1
  refine ⟨_, StackProg.Exec.seq e1 e2, ?_, ?_, ?_⟩
  · intro hc
    obtain ⟨hc1, hc2⟩ := (canonTok_iff' t).1 hc
    have hz1 : s1 .z = [] := by simp [hs1, hz, hc2]
    rw [if_pos hz1]
    funext k; simp only [hs1, Function.update_apply]
    by_cases k1 : k = .bad
    · subst k1; simp [h1.symm, hc1]
    by_cases k2 : k = .z
    · subst k2; simp [h2.symm, hz, hc2]
    simp [k1, k2]
  · intro hc
    have hn : ¬ (t.countP (fun a => !isDigS a) = 0 ∧ zF t [] = []) := by
      rw [← canonTok_iff']; simp [hc]
    by_cases hz1 : s1 .z = []
    · rw [if_pos hz1]
      have hzF : zF t [] = [] := by simpa [hs1, hz] using hz1
      have hcp : t.countP (fun a => !isDigS a) ≠ 0 := fun h => hn ⟨h, hzF⟩
      have : List.replicate (t.countP (fun a => !isDigS a)) BSym.one ++ s .bad ≠ [] := by
        intro h
        have hl := congrArg List.length h
        rw [List.length_append, List.length_replicate, List.length_nil] at hl
        exact hcp (by omega)
      simpa [hs1] using this
    · rw [if_neg hz1]; simp
  · by_cases hz1 : s1 .z = []
    · rw [if_pos hz1]; simp [hs1, Function.update_apply, Ne.symm h3]
    · rw [if_neg hz1]; simp [hs1, Function.update_apply, Ne.symm h3]


lemma canon_dig (t : List BSym) (h : canonTok t = true) : ∀ a ∈ t, isDigS a = true := by
  simp only [canonTok, Bool.and_eq_true, List.all_eq_true] at h; exact h.1

/-! ## level 5: the threshold `W` -/

lemma run_prog5 (c : Cfg) (xb : List Bool) (L : ℕ) (hL : 1 ≤ L) (hacc : c.acc = enc xb)
    (hz : c.z = []) (hcW : c.cW = []) (htmp : c.tmp = []) (hcar : c.car = []) (hbad : c.bad = [])
    (hcnt : c.cnt.length = L) (hc1 : c.c1 = []) (hsc : c.sc = []) (hd2 : c.d2 = [])
    (htBL : c.tB.length ≤ L) (hout : c.out = []) (htWL : c.tW.length ≤ L) :
    ∃ t n, n ≤ 70 * L + 3 * c.R.length + 15 * xb.length + 300 ∧ prog5.Exec c.st t n ∧
      t .out = (match wdig c.tW with
        | none => []
        | some wd => if (subB xb wd false).2 = true then [] else
            c.R.reverse ++ outP L ++ outQA L (subB xb wd false).1 ++ outQB L c.tB) := by
  by_cases hm : c.tW.head? = some .minus
  · obtain ⟨rest, hrest⟩ : ∃ rest, c.tW = .minus :: rest := by
      rcases h : c.tW with _ | ⟨a, r⟩
      · rw [h] at hm; simp at hm
      · rw [h] at hm; simp at hm; exact ⟨r, by rw [hm]⟩
    have htest : (fun h : Key → Option BSym => decide (h .tW = some .minus))
        (fun k => (c.st k).head?) = true := by simp [hrest]
    have e1 := exec_pop .tW c.st
    rw [st_set] at e1
    set a1 := c.set .tW (c.st .tW).tail with ha1
    have ha1t : a1.tW = rest := by simp [ha1, Cfg.set, hrest]
    have e2 := exec_chkNE a1.st .tW (by decide)
    by_cases hr : rest = []
    · rw [if_pos (by simp [ha1t, hr]), st_set] at e2
      set a2 := a1.set .bad (.one :: a1.st .bad) with ha2
      obtain ⟨s', e3, hs'1, -, hs'o⟩ := scan_z a2.st .tW (by decide) (by decide) (by decide) []
        (by simp [ha2, Cfg.set, ha1t, hr]) (by simp [ha2, ha1, Cfg.set, hz])
      have hs' := hs'1 (by decide)
      have hex := StackProg.Exec.branchTrue (test := fun h => decide (h .tW = some .minus)) (q := .seq (copyProg .tW .cW .sc)
        (.seq (scanLoop .cW .bad .z) zcheck)) htest (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3))
      have hg := guard_bad (q := prog6) hex (by rw [hs']; simp [ha2, Cfg.set])
      refine ⟨_, _, ?_, hg, ?_⟩
      · first | omega | simp | (simp; omega)
      · have hw : wdig c.tW = none := by simp [wdig, hrest, hr]
        rw [hw, hs'o]; simp [ha2, ha1, Cfg.set, hout]
    · rw [if_neg (by simp [ha1t, hr])] at e2
      obtain ⟨s', e3, hs'1, hs'2, hs'o⟩ := scan_z a1.st .tW (by decide) (by decide) (by decide) rest
        (by simp [ha1t]) (by simp [ha1, Cfg.set, hz])
      have hex := StackProg.Exec.branchTrue (test := fun h => decide (h .tW = some .minus)) (q := .seq (copyProg .tW .cW .sc)
        (.seq (scanLoop .cW .bad .z) zcheck)) htest (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3))
      have hrL : rest.length + 1 ≤ L := by rw [hrest] at htWL; simpa using htWL
      by_cases hc : canonTok rest = true
      · have hs' := hs'1 hc
        rw [hs', st_set] at hex
        set a3 := a1.set .tW [] with ha3
        obtain ⟨t, n, hn, e4, ho⟩ := run_prog6 a3 xb [] L hL (by simp [ha3, ha1, Cfg.set, hacc])
          (by simp [ha3, Cfg.set, enc]) (by simp [ha3, ha1, Cfg.set, htmp])
          (by simp [ha3, ha1, Cfg.set, hcar]) (by simp [ha3, ha1, Cfg.set, hbad])
          (by simp [ha3, ha1, Cfg.set, hcnt]) (by simp [ha3, ha1, Cfg.set, hc1])
          (by simp [ha3, ha1, Cfg.set, hsc]) (by simp [ha3, ha1, Cfg.set, hd2])
          (by simp [ha3, ha1, Cfg.set, htBL]) (by simp [ha3, ha1, Cfg.set, hout])
        have hg := guard_ok hex (by simp [ha3, ha1, Cfg.set, hbad]) e4
        refine ⟨t, _, ?_, hg, ?_⟩
        · have hR : a3.R = c.R := by simp [ha3, ha1, Cfg.set]
          rw [hR] at hn; simp at hn; omega
        · have hw : wdig c.tW = some [] := by simp [wdig, hrest, hr, hc]
          rw [hw, ho]; simp [ha3, ha1, Cfg.set]
      · have hc' : canonTok rest = false := by simpa using hc
        have hg := guard_bad (q := prog6) hex (hs'2 hc')
        refine ⟨_, _, ?_, hg, ?_⟩
        · omega
        · have hw : wdig c.tW = none := by simp [wdig, hrest, hr, hc]
          rw [hw, hs'o]; simp [ha1, Cfg.set, hout]
  · have htest : (fun h : Key → Option BSym => decide (h .tW = some .minus))
        (fun k => (c.st k).head?) = false := by simp [hm]
    have e1 := exec_copy (K := Key) (A := BSym) .tW .cW .sc (by decide) (by decide) (by decide) c.st
      (by simp [hsc])
    rw [st_set] at e1
    set a1 := c.set .cW (c.st .tW ++ c.st .cW) with ha1
    obtain ⟨s', e2, hs'1, hs'2, hs'o⟩ := scan_z a1.st .cW (by decide) (by decide) (by decide) c.tW
      (by simp [ha1, Cfg.set, hcW]) (by simp [ha1, Cfg.set, hz])
    have hex := StackProg.Exec.branchFalse (test := fun h => decide (h .tW = some .minus)) (p := .seq (popProg .tW) (.seq (chkNE .tW)
      (.seq (scanLoop .tW .bad .z) zcheck))) htest (StackProg.Exec.seq e1 e2)
    by_cases hc : canonTok c.tW = true
    · have hs' := hs'1 hc
      rw [hs', st_set] at hex
      set a3 := a1.set .cW [] with ha3
      have henc : c.tW = enc (c.tW.map isOne) := (enc_of_dig c.tW (canon_dig _ hc)).symm
      obtain ⟨t, n, hn, e4, ho⟩ := run_prog6 a3 xb (c.tW.map isOne) L hL
        (by simp [ha3, ha1, Cfg.set, hacc]) (by simp only [ha3, ha1, Cfg.set]; exact henc)
        (by simp [ha3, ha1, Cfg.set, htmp])
        (by simp [ha3, ha1, Cfg.set, hcar]) (by simp [ha3, ha1, Cfg.set, hbad])
        (by simp [ha3, ha1, Cfg.set, hcnt]) (by simp [ha3, ha1, Cfg.set, hc1])
        (by simp [ha3, ha1, Cfg.set, hsc]) (by simp [ha3, ha1, Cfg.set, hd2])
        (by simp [ha3, ha1, Cfg.set, htBL]) (by simp [ha3, ha1, Cfg.set, hout])
      have hg := guard_ok hex (by simp [ha3, ha1, Cfg.set, hbad]) e4
      refine ⟨t, _, ?_, hg, ?_⟩
      · have hR : a3.R = c.R := by simp [ha3, ha1, Cfg.set]
        rw [hR] at hn; simp at hn ⊢; omega
      · have hw : wdig c.tW = some (c.tW.map isOne) := by simp [wdig, hm, hc]
        rw [hw, ho]; simp [ha3, ha1, Cfg.set]
    · have hc' : canonTok c.tW = false := by simpa using hc
      have hg := guard_bad (q := prog6) hex (hs'2 hc')
      refine ⟨_, _, ?_, hg, ?_⟩
      · simp [ha1, Cfg.set, hcW]; omega
      · have hw : wdig c.tW = none := by simp [wdig, hm, hc]
        rw [hw, hs'o]; simp [ha1, Cfg.set, hout]


lemma exec_moveOne (s : St Key) (src dst : Key) (h : src ≠ dst) (a : BSym) (r : List BSym)
    (hs : s src = a :: r) :
    (moveOne src dst).Exec s (Function.update (Function.update s src r) dst (a :: s dst)) 1 := by
  apply act_eq
  funext j
  by_cases h1 : j = src
  · subst h1; simp [StackProg.applyAct, StackAct.apply, hs, h]
  by_cases h2 : j = dst
  · subst h2; simp [StackProg.applyAct, StackAct.apply, hs, h1]
  simp [StackProg.applyAct, StackAct.apply, h1, h2]

lemma dropToks_len : ∀ (k : ℕ) (l : List BSym), (dropToks k l).length ≤ l.length
  | 0, l => le_rfl
  | k + 1, l => by
    simp only [dropToks]
    refine le_trans (dropToks_len k _) ?_
    have := List.length_dropWhile_le ne l
    have := @List.length_tail _ (l.dropWhile ne)
    omega

/-! ## level 4: the prefix, the middle tokens, the sum, and `b` -/

lemma run_prog4 (c : Cfg) (v5 : List BSym) (L : ℕ) (hL : 1 ≤ L) (hrv : c.rv = .sep :: v5)
    (hz : c.z = []) (hcW : c.cW = []) (hcB : c.cB = []) (hpre : c.pre = []) (hR : c.R = [])
    (hm2 : c.m2 = []) (hm3 : c.m3 = []) (hmc : c.mc = []) (hacc : c.acc = [])
    (htmp : c.tmp = []) (hcar : c.car = []) (hbad : c.bad = [])
    (hcnt : c.cnt.length = L) (hc1 : c.c1 = []) (hsc : c.sc = []) (hd2 : c.d2 = [])
    (htBL : c.tB.length ≤ L) (hout : c.out = []) (htWL : c.tW.length ≤ L)
    (hv5L : v5.length + 1 ≤ L) :
    ∃ t n, n ≤ 40 * (L + 1) ^ 2 + 1000 ∧ prog4.Exec c.st t n ∧
      t .out = Fbody L c.tW c.tB (v5.reverse ++ [.sep]) := by
  set z1 := v5.reverse ++ [BSym.sep] with hz1
  -- 1. transfer rv → pre
  have e1 := exec_transfer .rv (fun j => decide (j = .pre)) c.rv c.st rfl
  rw [transfer1 _ _ (by decide), st_set, st_set] at e1
  set a1 := (c.set .rv []).set .pre ((c.st .rv).reverse ++ c.st .pre) with ha1
  have ha1p : a1.pre = z1 := by simp [ha1, Cfg.set, hrv, hpre, hz1]
  -- 2. moveTok pre → R
  obtain ⟨t1, rd1, hz1s, ht1, hstop1, -, htw1, hdw1⟩ := split_tok z1
  have e2 := exec_mapMove ne .pre (fun a j => if j = .R then some a else none) rd1 hstop1 t1 a1.st
    (by rw [st_pre, ha1p, hz1s]) ht1
  rw [mm1 _ _ (by decide), st_set, st_set] at e2
  set a2 := (a1.set .pre rd1).set .R (t1.reverse ++ a1.st .R) with ha2
  -- rd1 = sep :: M
  have hrd1 : rd1 ≠ [] := by
    intro h0; rw [← hdw1, List.dropWhile_eq_nil_iff] at h0
    have := h0 BSym.sep (by simp [hz1]); simp at this
  obtain ⟨a, M, hrdM⟩ := List.exists_cons_of_ne_nil hrd1
  have ha : a = BSym.sep := by
    unfold stopAt at hstop1; rw [hrdM] at hstop1; simp at hstop1; cases a <;> simp_all [ne]
  subst ha
  have hM : M = (z1.dropWhile ne).tail := by rw [hdw1, hrdM]; rfl
  -- 3. moveOne pre → R
  have e3 := exec_moveOne a2.st .pre .R (by decide) BSym.sep M (by simp [ha2, Cfg.set, hrdM])
  rw [st_set, st_set] at e3
  set a3 := (a2.set .pre M).set .R (BSym.sep :: a2.st .R) with ha3
  -- 4. pushes
  have e4 := exec_push .R BSym.one a3.st
  rw [st_set] at e4
  set a4 := a3.set .R (BSym.one :: a3.st .R) with ha4
  have e5 := exec_push .R BSym.sep a4.st
  rw [st_set] at e5
  set a5 := a4.set .R (BSym.sep :: a4.st .R) with ha5
  -- 6. copy the middle to R, m2, counting separators
  have e6 := exec_mapMove (fun _ => true) .pre g10 [] trivial M a5.st
    (by simp [ha5, ha4, ha3, Cfg.set]) (by simp)
  rw [mm10, st_set, st_set, st_set, st_set] at e6
  set a6 := (((a5.set .pre []).set .R (M.reverse ++ a5.st .R)).set .m2 (M.reverse ++ a5.st .m2)).set
    .mc (List.replicate (M.count .sep) BSym.one ++ a5.st .mc) with ha6
  -- 7. transfer m2 → m3
  have e7 := exec_transfer .m2 (fun j => decide (j = .m3)) a6.m2 a6.st rfl
  rw [transfer1 _ _ (by decide), st_set, st_set] at e7
  set a7 := (a6.set .m2 []).set .m3 ((a6.st .m2).reverse ++ a6.st .m3) with ha7
  -- 8. skip
  obtain ⟨n8, hn8, e8⟩ := exec_skipLoop (K := Key) .m3 .mc (by decide) (M.count .sep) M a7.st
    (by simp [ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hmc])
    (by simp [ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hm2, hm3])
  rw [st_set, st_set] at e8
  set dl := dropToks ((M.count .sep + 1) / 2) M with hdl
  set a8 := (a7.set .mc []).set .m3 dl with ha8
  -- 9. sum
  have hML : M.length + 1 ≤ L := by
    have := congrArg List.length hz1s
    rw [hrdM] at this; simp [hz1] at this; omega
  have hdlL : dl.length ≤ L := by
    have : dl.length ≤ M.length := dropToks_len _ _
    omega
  obtain ⟨n9, hn9, e9⟩ := exec_sumLoop (K := Key) .m3 .acc .tmp .car (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (2 * L) dl.length dl [] a8.st le_rfl
    (by simp; omega) (by simp [ha8, Cfg.set])
    (by simp [ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hacc, enc])
    (by simp [ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, htmp])
    (by simp [ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hcar])
  rw [st_set, st_set] at e9
  set a9 := (a8.set .m3 []).set .acc (enc (sumAcc [] dl)) with ha9
  have hxb : sumAcc [] dl = accOf z1 := by rw [accOf, ← hM]
  -- 10. copy tB → cB
  have e10 := exec_copy (K := Key) (A := BSym) .tB .cB .sc (by decide) (by decide) (by decide) a9.st
    (by simp [ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hsc])
  rw [st_set] at e10
  set a10 := a9.set .cB (a9.st .tB ++ a9.st .cB) with ha10
  obtain ⟨s', e11, hs'1, hs'2, hs'o⟩ := scan_z a10.st .cB (by decide) (by decide) (by decide) c.tB
    (by simp [ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hcB])
    (by simp [ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hz])
  have hPE := StackProg.Exec.seq e1 <| StackProg.Exec.seq e2 <| StackProg.Exec.seq e3 <|
    StackProg.Exec.seq e4 <| StackProg.Exec.seq e5 <| StackProg.Exec.seq e6 <|
    StackProg.Exec.seq e7 <| StackProg.Exec.seq e8 <| StackProg.Exec.seq e9 <|
    StackProg.Exec.seq e10 e11
  have hcnt' : M.count .sep ≤ L := le_trans (List.count_le_length) (by omega)
  have hb8 : n8 ≤ (3 * L + 8) * L + 1 := by
    calc n8 ≤ (3 * M.length + 8) * M.count .sep + 1 := hn8
      _ ≤ (3 * L + 8) * L + 1 := by gcongr <;> omega
  have hb9 : n9 ≤ L * (6 * (2 * L) + 13) + 1 := by
    calc n9 ≤ dl.length * (6 * (2 * L) + 13) + 1 := hn9
      _ ≤ L * (6 * (2 * L) + 13) + 1 := by gcongr
  have hsq : (3 * L + 8) * L + 1 + (L * (6 * (2 * L) + 13) + 1) ≤ 15 * (L + 1) ^ 2 := by nlinarith
  have f1 : a6.m2.length = M.length := by simp [ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hm2]
  have f2 : (a9.st .tB).length = c.tB.length := by
    simp [ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set]
  have ht1L : t1.length ≤ L := by
    have := congrArg List.length hz1s; simp [hz1] at this; omega
  have hrvL : c.rv.length = v5.length + 1 := by simp [hrv]
  by_cases hc : canonTok c.tB = true
  · have hs' := hs'1 hc
    rw [hs', st_set] at hPE
    set a11 := a10.set .cB [] with ha11
    have hxbL : (accOf z1).length ≤ 2 * L := by
      have := len_sumAcc dl.length [] dl le_rfl; rw [hxb] at this; simp at this; omega
    obtain ⟨t, n, hn, e12, ho⟩ := run_prog5 a11 (accOf z1) L hL
      (by simp [ha11, ha10, ha9, Cfg.set, hxb])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hz])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hcW])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, htmp])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hcar])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hbad])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hcnt])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hc1])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hsc])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hd2])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, htBL])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hout])
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, htWL])
    have hg := guard_ok hPE
      (by simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hbad]) e12
    have hR11 : a11.R = M.reverse ++ (BSym.sep :: BSym.one :: BSym.sep :: t1.reverse) := by
      simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set, hR]
    refine ⟨t, _, ?_, hg, ?_⟩
    · rw [hR11] at hn
      simp only [List.length_append, List.length_reverse, List.length_cons] at hn
      rw [f1, f2, hrvL]
      nlinarith
    · rw [ho, hR11]
      have htB11 : a11.tB = c.tB := by
        simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set]
      have htW11 : a11.tW = c.tW := by
        simp [ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set]
      rw [htB11, htW11, Fbody, if_pos hc, ← htw1, ← hM]
      rcases wdig c.tW with _ | wd
      · rfl
      · simp only
        split_ifs <;> simp
  · have hc' : canonTok c.tB = false := by simpa using hc
    have hg := guard_bad (q := prog5) hPE (hs'2 hc')
    refine ⟨_, _, ?_, hg, ?_⟩
    · rw [f1, f2, hrvL]
      have h89 : n8 + n9 ≤ 15 * (L + 1) ^ 2 := le_trans (Nat.add_le_add hb8 hb9) (by omega)
      have hQ : L ≤ (L + 1) ^ 2 := by nlinarith
      generalize (L + 1) ^ 2 = Q at h89 hQ ⊢
      omega
    · rw [hs'o, Fbody, if_neg hc, st_out]
      have : a10.out = c.out := by
        simp only [ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, Cfg.set]
      rw [this, hout]


/-! ## levels 3, 2, 1 and the whole machine -/

lemma run_prog3 (c : Cfg) (v3 : List BSym) (L : ℕ) (hL : 1 ≤ L) (hrv : c.rv = v3)
    (hz : c.z = []) (hcW : c.cW = []) (hcB : c.cB = []) (hpre : c.pre = []) (hR : c.R = [])
    (hm2 : c.m2 = []) (hm3 : c.m3 = []) (hmc : c.mc = []) (hacc : c.acc = [])
    (htmp : c.tmp = []) (hcar : c.car = []) (hbad : c.bad = [])
    (hcnt : c.cnt.length = L) (hc1 : c.c1 = []) (hsc : c.sc = []) (hd2 : c.d2 = [])
    (htB : c.tB = []) (hout : c.out = []) (htWL : c.tW.length ≤ L) (hv3L : v3.length ≤ L) :
    ∃ t n, n ≤ 43 * (L + 1) ^ 2 + 1100 ∧ prog3.Exec c.st t n ∧
      t .out = (if v3.dropWhile ne = [] then [] else
        Fbody L c.tW (v3.takeWhile ne).reverse (v3.dropWhile ne).reverse) := by
  obtain ⟨tok, rd, hv3, htok, hstop, -, htw, hdw⟩ := split_tok v3
  have e1 := exec_mapMove ne .rv (fun a j => if j = .tB then some a else none) rd hstop tok c.st
    (by rw [st_rv, hrv, hv3]) htok
  rw [mm1 _ _ (by decide), st_set, st_set] at e1
  set a1 := (c.set .rv rd).set .tB (tok.reverse ++ c.st .tB) with ha1
  have e2 := exec_chkNE a1.st .rv (by decide)
  have hlen : v3.length = tok.length + rd.length := by rw [hv3]; simp
  by_cases hr : rd = []
  · rw [if_pos (by simp [ha1, Cfg.set, hr]), st_set] at e2
    have hg := guard_bad (q := prog4) (StackProg.Exec.seq e1 e2) (by simp [Cfg.set])
    refine ⟨_, _, ?_, hg, ?_⟩
    · have : 3 * tok.length ≤ 3 * L := by omega
      nlinarith
    · rw [if_pos (by rw [hdw, hr])]; simp [ha1, Cfg.set, hout]
  · rw [if_neg (by simp [ha1, Cfg.set, hr])] at e2
    obtain ⟨a, v5, hrd⟩ := List.exists_cons_of_ne_nil hr
    have ha : a = BSym.sep := by
      unfold stopAt at hstop; rw [hrd] at hstop; simp at hstop; cases a <;> simp_all [ne]
    subst ha
    obtain ⟨t, n, hn, e3, ho⟩ := run_prog4 a1 v5 L hL (by simp [ha1, Cfg.set, hrd])
      (by simp [ha1, Cfg.set, hz]) (by simp [ha1, Cfg.set, hcW]) (by simp [ha1, Cfg.set, hcB])
      (by simp [ha1, Cfg.set, hpre]) (by simp [ha1, Cfg.set, hR]) (by simp [ha1, Cfg.set, hm2])
      (by simp [ha1, Cfg.set, hm3]) (by simp [ha1, Cfg.set, hmc]) (by simp [ha1, Cfg.set, hacc])
      (by simp [ha1, Cfg.set, htmp]) (by simp [ha1, Cfg.set, hcar]) (by simp [ha1, Cfg.set, hbad])
      (by simp [ha1, Cfg.set, hcnt]) (by simp [ha1, Cfg.set, hc1]) (by simp [ha1, Cfg.set, hsc])
      (by simp [ha1, Cfg.set, hd2]) (by simp [ha1, Cfg.set, htB]; omega)
      (by simp [ha1, Cfg.set, hout]) (by simp [ha1, Cfg.set, htWL])
      (by rw [hrd] at hlen; simp at hlen; omega)
    have hg := guard_ok (StackProg.Exec.seq e1 e2) (by simp [ha1, Cfg.set, hbad]) e3
    refine ⟨t, _, ?_, hg, ?_⟩
    · have : 3 * tok.length ≤ 3 * L := by omega
      have hQ : L ≤ (L + 1) ^ 2 := by nlinarith
      omega
    · rw [ho, if_neg (by rw [hdw]; exact hr), htw, hdw, hrd]
      simp [ha1, Cfg.set, htB]

lemma run_prog2 (c : Cfg) (v1 : List BSym) (L : ℕ) (hL : 1 ≤ L) (hrv : c.rv = v1)
    (hz : c.z = []) (hcW : c.cW = []) (hcB : c.cB = []) (hpre : c.pre = []) (hR : c.R = [])
    (hm2 : c.m2 = []) (hm3 : c.m3 = []) (hmc : c.mc = []) (hacc : c.acc = [])
    (htmp : c.tmp = []) (hcar : c.car = []) (hbad : c.bad = [])
    (hcnt : c.cnt.length = L) (hc1 : c.c1 = []) (hsc : c.sc = []) (hd2 : c.d2 = [])
    (htB : c.tB = []) (htW : c.tW = []) (hout : c.out = []) (hv1L : v1.length ≤ L) :
    ∃ t n, n ≤ 46 * (L + 1) ^ 2 + 1200 ∧ prog2.Exec c.st t n ∧
      t .out = (match v1.dropWhile ne with
        | .sep :: v3 =>
          if v3.dropWhile ne = [] then [] else
            Fbody L (v1.takeWhile ne).reverse (v3.takeWhile ne).reverse (v3.dropWhile ne).reverse
        | _ => []) := by
  obtain ⟨tok, rd, hv1, htok, hstop, -, htw, hdw⟩ := split_tok v1
  have e1 := exec_mapMove ne .rv (fun a j => if j = .tW then some a else none) rd hstop tok c.st
    (by rw [st_rv, hrv, hv1]) htok
  rw [mm1 _ _ (by decide), st_set, st_set] at e1
  set a1 := (c.set .rv rd).set .tW (tok.reverse ++ c.st .tW) with ha1
  have e2 := exec_chkSep a1.st .rv (by decide)
  have hlen : v1.length = tok.length + rd.length := by rw [hv1]; simp
  by_cases hr : rd.head? = some BSym.sep
  · obtain ⟨v3, hrd⟩ : ∃ v3, rd = BSym.sep :: v3 := by
      rcases rd with _ | ⟨a, v3⟩
      · simp at hr
      · simp at hr; exact ⟨v3, by rw [hr]⟩
    rw [if_pos (by simp [ha1, Cfg.set, hrd]), st_set] at e2
    set a2 := a1.set .rv (a1.st .rv).tail with ha2
    obtain ⟨t, n, hn, e3, ho⟩ := run_prog3 a2 v3 L hL (by simp [ha2, ha1, Cfg.set, hrd])
      (by simp [ha2, ha1, Cfg.set, hz]) (by simp [ha2, ha1, Cfg.set, hcW])
      (by simp [ha2, ha1, Cfg.set, hcB])
      (by simp [ha2, ha1, Cfg.set, hpre]) (by simp [ha2, ha1, Cfg.set, hR])
      (by simp [ha2, ha1, Cfg.set, hm2])
      (by simp [ha2, ha1, Cfg.set, hm3]) (by simp [ha2, ha1, Cfg.set, hmc])
      (by simp [ha2, ha1, Cfg.set, hacc])
      (by simp [ha2, ha1, Cfg.set, htmp]) (by simp [ha2, ha1, Cfg.set, hcar])
      (by simp [ha2, ha1, Cfg.set, hbad])
      (by simp [ha2, ha1, Cfg.set, hcnt]) (by simp [ha2, ha1, Cfg.set, hc1])
      (by simp [ha2, ha1, Cfg.set, hsc])
      (by simp [ha2, ha1, Cfg.set, hd2]) (by simp [ha2, ha1, Cfg.set, htB])
      (by simp [ha2, ha1, Cfg.set, hout]) (by simp [ha2, ha1, Cfg.set, htW]; omega)
      (by rw [hrd] at hlen; simp at hlen; omega)
    have hg := guard_ok (StackProg.Exec.seq e1 e2) (by simp [ha2, ha1, Cfg.set, hbad]) e3
    refine ⟨t, _, ?_, hg, ?_⟩
    · have hQ : L ≤ (L + 1) ^ 2 := by nlinarith
      omega
    · rw [ho, hdw, hrd, htw]
      simp [ha2, ha1, Cfg.set, htW]
  · rw [if_neg (by simpa [ha1, Cfg.set] using hr), st_set] at e2
    have hg := guard_bad (q := prog3) (StackProg.Exec.seq e1 e2) (by simp [Cfg.set])
    refine ⟨_, _, ?_, hg, ?_⟩
    · nlinarith
    · rw [hdw]
      have : (match rd with
          | BSym.sep :: v3 =>
            if v3.dropWhile ne = [] then [] else
              Fbody L (v1.takeWhile ne).reverse (v3.takeWhile ne).reverse (v3.dropWhile ne).reverse
          | _ => []) = [] := by
        rcases rd with _ | ⟨a, v3⟩
        · rfl
        · cases a <;> first | rfl | (exfalso; simp at hr)
      rw [this]; simp [ha1, Cfg.set, hout]

def initCfg (x : List BSym) : Cfg := { inp := x }

lemma initCfg_st (x : List BSym) : (initCfg x).st = fun j => if j = .inp then x else [] := by
  funext j; cases j <;> rfl

lemma run_main (x : List BSym) :
    ∃ t n, n ≤ 49 * (x.length + 1) ^ 2 + 1300 ∧
      mainProg.Exec (initCfg x).st t n ∧ t .out = F x := by
  set L := x.length with hL
  have e1 := exec_transfer .inp (fun j => decide (j = .rv ∨ j = .cnt)) x (initCfg x).st rfl
  rw [transfer2 _ _ _ (by decide) (by decide) (by decide), st_set, st_set, st_set] at e1
  set c1 := (((initCfg x).set .inp []).set .rv (((initCfg x).st .inp).reverse ++
    (initCfg x).st .rv)).set .cnt (((initCfg x).st .inp).reverse ++ (initCfg x).st .cnt) with hc1
  have hc1rv : c1.rv = x.reverse := by simp [hc1, Cfg.set, initCfg]
  have e2 := exec_chkSep c1.st .rv (by decide)
  have hQ : L ≤ (L + 1) ^ 2 := by nlinarith
  by_cases hr : x.reverse.head? = some BSym.sep
  · obtain ⟨v1, hv1⟩ : ∃ v1, x.reverse = BSym.sep :: v1 := by
      rcases h : x.reverse with _ | ⟨a, v1⟩
      · rw [h] at hr; simp at hr
      · rw [h] at hr; simp at hr; exact ⟨v1, by rw [hr]⟩
    rw [if_pos (by simp [hc1rv, hr]), st_set] at e2
    set c2 := c1.set .rv (c1.st .rv).tail with hc2
    have hxL : v1.length + 1 = L := by
      have := congrArg List.length hv1; simp at this; omega
    obtain ⟨t, n, hn, e3, ho⟩ := run_prog2 c2 v1 L (by omega)
      (by simp [hc2, hc1rv, hv1, Cfg.set]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg, hL])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by simp [hc2, hc1, Cfg.set, initCfg]) (by simp [hc2, hc1, Cfg.set, initCfg])
      (by omega)
    have hg := guard_ok (q := prog2) e2 (by simp [hc2, hc1, Cfg.set, initCfg]) e3
    refine ⟨t, _, ?_, StackProg.Exec.seq e1 hg, ?_⟩
    · simp [initCfg]; omega
    · rw [ho]; unfold F; rw [hv1]
      all_goals
        simp only [hL]
        generalize List.dropWhile ne v1 = d
        rcases d with _ | ⟨a, v3⟩
        · rfl
        · cases a <;> rfl
  · rw [if_neg (by simpa [hc1rv] using hr), st_set] at e2
    have hg := guard_bad (q := prog2) e2 (by simp [Cfg.set])
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 hg, ?_⟩
    · simp [initCfg]; omega
    · have hF : F x = [] := by
        unfold F
        rcases h : x.reverse with _ | ⟨a, v1⟩
        · rfl
        · rw [h] at hr; cases a <;> first | rfl | (exfalso; simp at hr)
      rw [hF]; simp [hc1, Cfg.set, initCfg]

end KS
end KS_Mach


set_option autoImplicit false

namespace KS
open CookPvsNP ProjSchedTW.Complexity

lemma absorb (L : ℕ) : 49 * (L + 1) ^ 2 + 1300 ≤ L ^ 2000 + 2000 := by
  rcases L with _ | _ | L
  · norm_num
  · norm_num
  · have key : 49 * (L + 1 + 1 + 1) ^ 2 + 1300 ≤ (L + 2) ^ 14 := by
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
    calc 49 * (L + 1 + 1 + 1) ^ 2 + 1300 ≤ (L + 2) ^ 14 := key
      _ ≤ (L + 2) ^ 2000 := h3
      _ ≤ (L + 1 + 1) ^ 2000 + 2000 := Nat.le_add_right _ _

theorem F_exec (w : List BSym) : ∃ s n, n ≤ w.length ^ 2000 + 2000 ∧
    mainProg.Exec (fun j => if j = Key.inp then w else []) s n ∧ s Key.out = F w := by
  obtain ⟨t, n, hn, e, ho⟩ := run_main w
  rw [initCfg_st] at e
  exact ⟨t, n, le_trans hn (absorb _), e, ho⟩

theorem F_polytime : PolyTimeComputable F :=
  stack_program_polytime mainProg Key.inp Key.out F 2000 F_exec

end KS

open TwoAgentSched.Knapsack CookPvsNP ProjSchedTW.Complexity in
theorem solution :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ (n : ℕ) (u w : Fin n → ℕ) (b W : ℤ),
            0 < ∑ i, w i * u i ∧
            (construction u w).RecYes ((QA u w W : ℤ) : ℝ) ((QB u w b : ℤ) : ℝ) ∧
            x = knapsackCode u w b W) ∨
          (∃ (n : ℕ) (u w : Fin n → ℕ) (b W : ℤ),
            ∑ i, w i * u i = 0 ∧ KnapsackYes u w b W ∧ x = knapsackCode u w b W)) ↔
          f x ∈ targetLang := by
  refine ⟨KS.F, KS.F_polytime, fun x => ?_⟩
  rw [← KS.F_correct]
  constructor
  · rintro (⟨n, u, w, b, W, hpos, hrec, rfl⟩ | ⟨n, u, w, b, W, -, hK, rfl⟩)
    · exact ⟨n, u, w, b, W, (theorem_5_2_equivalence u w b W hpos).2 hrec, rfl⟩
    · exact ⟨n, u, w, b, W, hK, rfl⟩
  · rintro ⟨n, u, w, b, W, hK, rfl⟩
    rcases Nat.eq_zero_or_pos (∑ i, w i * u i) with h0 | hpos
    · exact Or.inr ⟨n, u, w, b, W, h0, hK, rfl⟩
    · exact Or.inl ⟨n, u, w, b, W, hpos, (theorem_5_2_equivalence u w b W hpos).1 hK, rfl⟩
