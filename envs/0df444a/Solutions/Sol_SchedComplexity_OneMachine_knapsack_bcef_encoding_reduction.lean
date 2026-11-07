-- Prove2me | solution 1 for SchedComplexity.OneMachine.knapsack_bcef_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:23:39.592894+00:00
-- url     : https://prove2.me/submissions/1710c14a-f6f3-438b-999c-05ddc80a04ae

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Problems
import Definitions.Def_SchedComplexity_OneMachine_Constructions
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_program_polytime

set_option linter.all false


set_option autoImplicit false

namespace OMK

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

end OMK


set_option autoImplicit false

namespace OMK
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

end OMK


set_option autoImplicit false

namespace OMK
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

end OMK


set_option autoImplicit false

namespace OMK
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

end OMK




set_option autoImplicit false

namespace OMK
open CookPvsNP ProjSchedTW.Complexity

/-! ## Arithmetic complements -/

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

lemma sumAcc_bits (c : ℕ) (l : List ℕ) : sumAcc (Nat.bits c) (encNats l) = Nat.bits (c + l.sum) := by
  induction l generalizing c with
  | nil => simp [encNats, sumAcc_nil]
  | cons k l ih =>
    rw [encNats_cons, sumAcc_cons_tok _ _ _ (tokOf_ne k), tokOf, map_isOne_enc, ← bits_add, ih]
    simp [Nat.add_assoc]

lemma canon_append_true (l : List Bool) : Canon (l ++ [true]) := by
  induction l with
  | nil => simp [Canon]
  | cons b l ih => exact ⟨fun h => by simp at h, ih⟩

lemma encNats_inj {a b : List ℕ} (h : encNats a = encNats b) : a = b := by
  rw [encNats_eq_joinT, encNats_eq_joinT] at h
  have h2 := joinT_inj _ _ (by simp only [List.mem_map]; rintro t ⟨k, -, rfl⟩; exact tokOf_ne k)
    (by simp only [List.mem_map]; rintro t ⟨k, -, rfl⟩; exact tokOf_ne k) h
  exact List.map_injective_iff.2 (fun x y hxy => tokOf_inj hxy) h2

lemma encNats_ne_nil {l : List ℕ} (h : l ≠ []) : encNats l ≠ [] := by
  obtain ⟨k, l', rfl⟩ := List.exists_cons_of_ne_nil h
  rw [encNats_cons]; simp

lemma tokOf_zero : tokOf 0 = [] := by simp [tokOf, enc]

lemma tokOf_ne_nil {k : ℕ} (hk : 0 < k) : tokOf k ≠ [] := by
  intro h
  have : Nat.bits k = [] := by simpa [tokOf, enc] using h
  have := congrArg bval this
  rw [bval_bits] at this; simp [bval] at this; omega

/-! ## Validation automaton -/

/-- state `(o, z, bad)`: last symbol was `one`, last symbol was `zero`, an error occurred -/
def vstep : Bool × Bool × Bool → BSym → Bool × Bool × Bool
  | (_, _, b), .one => (true, false, b)
  | (_, _, b), .zero => (false, true, b)
  | (o, _, b), .sep => (false, false, b || !o)
  | (o, z, _), .minus => (o, z, true)

def vrun (w : List BSym) : Bool × Bool × Bool := w.foldl vstep (false, true, false)

def PosCode (w : List BSym) (l : List ℕ) : Prop := l ≠ [] ∧ (∀ v ∈ l, 0 < v) ∧ w = encNats l

lemma bad_mono (l : List BSym) : ∀ s : Bool × Bool × Bool, s.2.2 = true →
    (l.foldl vstep s).2.2 = true := by
  induction l with
  | nil => intro s h; exact h
  | cons a l ih =>
    intro s h
    apply ih
    obtain ⟨o, z, b⟩ := s
    simp at h; subst h
    cases a <;> simp [vstep]

lemma digits_fold (d : List Bool) : ∀ (o z b : Bool),
    ((enc d).foldl vstep (o, z, b)).2.2 = b := by
  induction d with
  | nil => intro o z b; rfl
  | cons x d ih =>
    intro o z b
    cases x
    · exact ih _ _ _
    · exact ih _ _ _

lemma canon_last {d : List Bool} {x : Bool} (h : Canon (d ++ [x])) : x = true := by
  induction d with
  | nil => exact h.1 rfl
  | cons b d ih => exact ih h.2

lemma tok_split (k : ℕ) (hk : 0 < k) : ∃ d : List Bool, tokOf k = enc d ++ [.one] := by
  have hc := (canon_bits_bval k).1
  have hne : Nat.bits k ≠ [] := by
    intro h; have := congrArg bval h; rw [bval_bits] at this; simp [bval] at this; omega
  have hd := (List.dropLast_append_getLast hne).symm
  refine ⟨(Nat.bits k).dropLast, ?_⟩
  rw [hd] at hc
  have hx := canon_last hc
  rw [tokOf, hd, hx]; simp [enc, toB]

lemma tok_fold (k : ℕ) (hk : 0 < k) (o z : Bool) :
    (tokOf k ++ [BSym.sep]).foldl vstep (o, z, false) = (false, false, false) := by
  obtain ⟨d, hd⟩ := tok_split k hk
  rw [hd, List.foldl_append, List.foldl_append]
  have hb := digits_fold d o z false
  rcases h : (enc d).foldl vstep (o, z, false) with ⟨o', z', b'⟩
  rw [h] at hb; simp at hb; subst hb
  simp [vstep]

lemma vrun_encNats (l : List ℕ) (hl : ∀ v ∈ l, 0 < v) (o z : Bool) :
    (encNats l).foldl vstep (o, z, false) =
      if l = [] then (o, z, false) else (false, false, false) := by
  induction l generalizing o z with
  | nil => simp [encNats]
  | cons k l ih =>
    rw [encNats_cons, show tokOf k ++ BSym.sep :: encNats l = (tokOf k ++ [.sep]) ++ encNats l
      by simp, List.foldl_append, tok_fold k (hl k (by simp)), ih (fun v hv => hl v (by simp [hv]))]
    split_ifs <;> simp_all

lemma vrun_of_pos {w : List BSym} {l : List ℕ} (h : PosCode w l) : vrun w = (false, false, false) := by
  obtain ⟨hne, hpos, rfl⟩ := h
  rw [vrun, vrun_encNats l hpos, if_neg hne]

lemma sepfree_fold_dig (t : List BSym) (ht : ∀ a ∈ t, ne a = true) (s : Bool × Bool × Bool)
    (hb : (t.foldl vstep s).2.2 = false) : ∀ a ∈ t, isDigS a = true := by
  induction t generalizing s with
  | nil => simp
  | cons a t ih =>
    intro x hx
    have ha := ht a (by simp)
    rw [List.foldl_cons] at hb
    rcases List.mem_cons.1 hx with rfl | hx
    · cases x
      · rfl
      · rfl
      · obtain ⟨o, z, b⟩ := s
        have := bad_mono t (vstep (o, z, b) .minus) (by simp [vstep])
        rw [this] at hb; exact absurd hb (by simp)
      · simp at ha
    · exact ih (fun b hb => ht b (by simp [hb])) _ hb x hx

lemma tok_of_fold (t : List BSym) (ht : ∀ a ∈ t, ne a = true) (s : Bool × Bool × Bool)
    (hs : s.1 = false) (h1 : (t.foldl vstep s).1 = true) (hb : (t.foldl vstep s).2.2 = false) :
    ∃ k, 0 < k ∧ t = tokOf k := by
  have hdig := sepfree_fold_dig t ht s hb
  have hne : t ≠ [] := by rintro rfl; simp [hs] at h1
  obtain ⟨t', x, hd⟩ : ∃ t' x, t = t' ++ [x] := ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  subst hd
  have hx : x = .one := by
    rw [List.foldl_append] at h1 hb
    have hxd := hdig x (by simp)
    rcases t'.foldl vstep s with ⟨o, z, b⟩
    cases x <;> simp_all [vstep, isDigS]
  subst hx
  have henc := enc_of_dig _ hdig
  have hdl : (t' ++ [BSym.one]).map isOne = t'.map isOne ++ [true] := by simp [isOne]
  have hcan : Canon ((t' ++ [BSym.one]).map isOne) := by rw [hdl]; exact canon_append_true _
  refine ⟨bval ((t' ++ [BSym.one]).map isOne), bval_pos hcan (by simp), ?_⟩
  rw [tokOf, bits_bval hcan, henc]

lemma fold_rest (r : List BSym) (hr : ∀ a ∈ r, ne a = true) (s : Bool × Bool × Bool)
    (h : r.foldl vstep s = (false, false, false)) : r = [] := by
  by_contra hne
  have hd := (List.dropLast_append_getLast hne).symm
  rw [hd, List.foldl_append] at h
  have hx := hr _ (List.getLast_mem hne)
  revert h hx
  generalize r.getLast hne = x
  rcases r.dropLast.foldl vstep s with ⟨o, z, b⟩
  intro h hx
  cases x <;> simp [vstep] at h hx

lemma pos_of_fold : ∀ (ts : List (List BSym)) (r : List BSym), (∀ t ∈ ts, ∀ a ∈ t, ne a = true) →
    (∀ a ∈ r, ne a = true) → ∀ s : Bool × Bool × Bool, s.1 = false →
    (joinT ts ++ r).foldl vstep s = (false, false, false) →
    r = [] ∧ ∃ l : List ℕ, (∀ v ∈ l, 0 < v) ∧ ts = l.map tokOf
  | [], r, _, hr, s, _, h => ⟨fold_rest r hr s (by simpa [joinT] using h), [], by simp, rfl⟩
  | t :: ts, r, hts, hr, s, hs, h => by
    rw [joinT_cons, List.append_assoc, List.foldl_append, List.cons_append, List.foldl_cons] at h
    set u := t.foldl vstep s with hu
    have hbad : (vstep u .sep).2.2 = false := by
      by_contra hc
      have := bad_mono (joinT ts ++ r) _ (by simpa using hc)
      rw [h] at this; simp at this
    obtain ⟨o, z, b⟩ := u
    simp only [vstep, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hbad
    obtain ⟨k, hk, htk⟩ := tok_of_fold t (hts t (by simp)) s hs (by rw [← hu]; exact hbad.2)
      (by rw [← hu]; exact hbad.1)
    obtain ⟨hr0, l, hl, hts'⟩ := pos_of_fold ts r (fun t' ht' => hts t' (by simp [ht'])) hr _
      (by simp [vstep]) h
    refine ⟨hr0, k :: l, ?_, by simp [htk, hts']⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact hk
    · exact hl v hv

lemma vrun_iff (w : List BSym) : vrun w = (false, false, false) ↔ ∃ l, PosCode w l := by
  refine ⟨fun h => ?_, fun ⟨l, hl⟩ => vrun_of_pos hl⟩
  obtain ⟨ts, r, hw, hts, hr⟩ := exists_joinT w.length w le_rfl
  rw [vrun, hw] at h
  obtain ⟨rfl, l, hl, rfl⟩ := pos_of_fold ts r hts hr _ rfl h
  refine ⟨l, ?_, hl, by rw [hw, List.append_nil, encNats_eq_joinT]⟩
  rintro rfl
  simp [joinT] at h


end OMK


set_option linter.all false



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace OMK
open CookPvsNP ProjSchedTW.Complexity

section lib
variable {K : Type} [DecidableEq K]

/-! ## Bounded executions -/

def ExecLe (p : StackProg K BSym) (s t : K → List BSym) (B : ℕ) : Prop := ∃ n ≤ B, p.Exec s t n

lemma ExecLe.of {p : StackProg K BSym} {s t : K → List BSym} {n B : ℕ} (h : p.Exec s t n)
    (hn : n ≤ B) : ExecLe p s t B := ⟨n, hn, h⟩

lemma ExecLe.mono {p : StackProg K BSym} {s t : K → List BSym} {B B' : ℕ} (h : ExecLe p s t B)
    (hB : B ≤ B') : ExecLe p s t B' := by
  obtain ⟨n, hn, he⟩ := h; exact ⟨n, le_trans hn hB, he⟩

lemma ExecLe.seq {p q : StackProg K BSym} {s t u : K → List BSym} {B1 B2 : ℕ}
    (h1 : ExecLe p s t B1) (h2 : ExecLe q t u B2) : ExecLe (p.seq q) s u (B1 + B2 + 1) := by
  obtain ⟨n, hn, e1⟩ := h1; obtain ⟨m, hm, e2⟩ := h2
  exact ⟨n + 1 + m, by omega, StackProg.Exec.seq e1 e2⟩

lemma ExecLe.brT {test : (K → Option BSym) → Bool} {p q : StackProg K BSym} {s t : K → List BSym}
    {B : ℕ} (ht : test (fun k => (s k).head?) = true) (h : ExecLe p s t B) :
    ExecLe (.branch test p q) s t (B + 1) := by
  obtain ⟨n, hn, e⟩ := h; exact ⟨1 + n, by omega, StackProg.Exec.branchTrue ht e⟩

lemma ExecLe.brF {test : (K → Option BSym) → Bool} {p q : StackProg K BSym} {s t : K → List BSym}
    {B : ℕ} (ht : test (fun k => (s k).head?) = false) (h : ExecLe q s t B) :
    ExecLe (.branch test p q) s t (B + 1) := by
  obtain ⟨n, hn, e⟩ := h; exact ⟨1 + n, by omega, StackProg.Exec.branchFalse ht e⟩

lemma ExecLe.congr {p : StackProg K BSym} {s t t' : K → List BSym} {B : ℕ} (h : ExecLe p s t B)
    (e : t = t') : ExecLe p s t' B := e ▸ h

/-! ## Basic programs -/

def skipP : StackProg K BSym := .act (fun _ _ => .keep)

lemma exec_actE (f : (K → Option BSym) → K → StackAct BSym) (s t : K → List BSym)
    (e : StackProg.applyAct f s = t) : ExecLe (.act f) s t 1 :=
  ExecLe.of (e ▸ StackProg.Exec.act f s) le_rfl

lemma exec_skip (s : K → List BSym) : ExecLe (skipP : StackProg K BSym) s s 1 :=
  exec_actE _ s s (by funext k; simp [StackProg.applyAct, StackAct.apply])

lemma exec_pushE (k : K) (a : BSym) (s : K → List BSym) :
    ExecLe (pushProg k a) s (Function.update s k (a :: s k)) 1 :=
  exec_actE _ _ _ (by
    funext j; by_cases h : j = k
    · subst h; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, h])

lemma exec_popE (k : K) (s : K → List BSym) :
    ExecLe (popProg k) s (Function.update s k (s k).tail) 1 :=
  exec_actE _ _ _ (by
    funext j; by_cases h : j = k
    · subst h; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, h])

/-- push the symbols of `l` in order (so the stack gets `l.reverse ++ _`) -/
def pushSeq (k : K) : List BSym → StackProg K BSym
  | [] => skipP
  | a :: l => .seq (pushProg k a) (pushSeq k l)

lemma exec_pushSeq (k : K) : ∀ (l : List BSym) (s : K → List BSym),
    ExecLe (pushSeq k l) s (Function.update s k (l.reverse ++ s k)) (2 * l.length + 1)
  | [], s => by
    simp only [pushSeq, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact exec_skip s
  | a :: l, s => by
    have e := (exec_pushE k a s).seq (exec_pushSeq k l _)
    refine (e.congr ?_).mono (by simp; omega)
    funext j; by_cases h : j = k
    · subst h; simp
    · simp [h]

lemma exec_copyE (src dst scr : K) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (s : K → List BSym) (hs : s scr = []) :
    ExecLe (copyProg src dst scr) s (Function.update s dst (s src ++ s dst))
      (6 * (s src).length + 3) :=
  ExecLe.of (exec_copy src dst scr h1 h2 h3 s hs) le_rfl

def tr1 (src dst : K) : StackProg K BSym := transferProg src (fun k => decide (k = dst))

lemma exec_tr1 (src dst : K) (h : src ≠ dst) (s : K → List BSym) :
    ExecLe (tr1 src dst) s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst))
      (3 * (s src).length + 1) := by
  refine ExecLe.of ((exec_transfer src _ (s src) s rfl)) ?_ |>.congr ?_
  · exact le_rfl
  · funext k; simp only [transferStore, Function.update_apply]
    by_cases k1 : k = src
    · subst k1; simp [h]
    · by_cases k2 : k = dst
      · subst k2; simp [Ne.symm h]
      · simp [k1, k2]

def clr (src : K) : StackProg K BSym := transferProg src (fun _ => false)

lemma exec_clr (src : K) (s : K → List BSym) :
    ExecLe (clr src) s (Function.update s src []) (3 * (s src).length + 1) := by
  refine ExecLe.of ((exec_transfer src _ (s src) s rfl)) le_rfl |>.congr ?_
  funext k; simp only [transferStore, Function.update_apply]
  by_cases k1 : k = src <;> simp [k1]

/-- move the leading sep-free token of `src` onto `dst` (reversed) -/
def moveTok (src dst : K) : StackProg K BSym :=
  mapMove ne src (fun a k => if k = dst then some a else none)

lemma exec_moveTok (src dst : K) (h : src ≠ dst) (t r : List BSym) (s : K → List BSym)
    (hs : s src = t ++ r) (ht : ∀ a ∈ t, ne a = true) (hr : stopAt ne r) :
    ExecLe (moveTok src dst) s (Function.update (Function.update s src r) dst (t.reverse ++ s dst))
      (3 * t.length + 1) := by
  refine ExecLe.of (exec_mapMove ne src _ r hr t s hs ht) le_rfl |>.congr ?_
  funext k; simp only [mmStore, Function.update_apply]
  by_cases k1 : k = src
  · subst k1; simp [h]
  · by_cases k2 : k = dst
    · subst k2; simp [k1]
    · simp [k1, k2]

/-- move the leading token to two stacks -/
def moveTok2 (src d1 d2 : K) : StackProg K BSym :=
  mapMove ne src (fun a k => if k = d1 ∨ k = d2 then some a else none)

lemma exec_moveTok2 (src d1 d2 : K) (h1 : src ≠ d1) (h2 : src ≠ d2) (t r : List BSym)
    (s : K → List BSym) (hs : s src = t ++ r) (ht : ∀ a ∈ t, ne a = true) (hr : stopAt ne r) :
    ExecLe (moveTok2 src d1 d2) s (fun k => if k = src then r else
      if k = d1 ∨ k = d2 then t.reverse ++ s k else s k) (3 * t.length + 1) := by
  refine ExecLe.of (exec_mapMove ne src _ r hr t s hs ht) le_rfl |>.congr ?_
  funext k; simp only [mmStore]
  by_cases k1 : k = src
  · simp [k1]
  · by_cases k2 : k = d1 ∨ k = d2
    · simp [k1, k2]
    · simp [k1, k2]

lemma filterMap_rep (l : List BSym) :
    l.filterMap (fun a => if a = .sep then some BSym.one else none) =
      List.replicate (l.count .sep) .one := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.count_cons]
    cases a <;> simp [ih, List.replicate_succ]

/-- count the seps of `src` (consumed) in unary onto `dst` -/
def countP (src dst : K) : StackProg K BSym :=
  mapMove (fun _ => true) src (fun a k => if k = dst ∧ a = .sep then some .one else none)

lemma exec_countP (src dst : K) (h : src ≠ dst) (s : K → List BSym) :
    ExecLe (countP src dst) s (Function.update (Function.update s src [])
      dst (List.replicate ((s src).count .sep) .one ++ s dst)) (3 * (s src).length + 1) := by
  refine ExecLe.of (exec_mapMove (fun _ => true) src _ [] trivial (s src) s (by simp)
    (by simp)) le_rfl |>.congr ?_
  funext k; simp only [mmStore, Function.update_apply]
  by_cases k1 : k = src
  · subst k1; simp [h]
  · by_cases k2 : k = dst
    · subst k2; simp only [k1, if_false, if_true, true_and]
      congr 1
      rw [filterMap_rep, List.count_reverse]
    · simp [k1, k2]

/-- pop a run of `zero`s -/
def stripZ (src : K) : StackProg K BSym :=
  mapMove (fun a => decide (a = .zero)) src (fun _ _ => none)

lemma exec_stripZ (src : K) (j : ℕ) (r : List BSym) (s : K → List BSym)
    (hs : s src = List.replicate j .zero ++ r) (hr : r.head? ≠ some .zero) :
    ExecLe (stripZ src) s (Function.update s src r) (3 * j + 1) := by
  have hr' : stopAt (fun a => decide (a = BSym.zero)) r := by
    unfold stopAt; rcases r with _ | ⟨a, r⟩
    · trivial
    · simpa using hr
  refine ExecLe.of (exec_mapMove _ src _ r hr' _ s hs (by simp)) (by simp) |>.congr ?_
  funext k; simp only [mmStore, Function.update_apply]
  by_cases k1 : k = src <;> simp [k1]

/-! ## The validation automaton loop -/

def fl (b : Bool) : List BSym := if b then [.one] else []

def setFl (cur new : Bool) : StackAct BSym :=
  if new then (if cur then .keep else .push .one) else (if cur then .pop else .keep)

lemma setFl_apply (c n : Bool) : (setFl c n).apply (fl c) = fl n := by
  cases c <;> cases n <;> rfl

lemma fl_head (b : Bool) : (fl b).head?.isSome = b := by cases b <;> rfl

def autAct (src f1 f2 f3 : K) (h : K → Option BSym) (k : K) : StackAct BSym :=
  let cur : Bool × Bool × Bool := ((h f1).isSome, (h f2).isSome, (h f3).isSome)
  let nxt := match h src with | some a => vstep cur a | none => cur
  if k = src then .pop else if k = f1 then setFl cur.1 nxt.1
  else if k = f2 then setFl cur.2.1 nxt.2.1 else if k = f3 then setFl cur.2.2 nxt.2.2 else .keep

def autLoop (src f1 f2 f3 : K) : StackProg K BSym :=
  .loop (fun h => (h src).isSome) (.act (autAct src f1 f2 f3))

lemma exec_autLoop (src f1 f2 f3 : K) (h1 : src ≠ f1) (h2 : src ≠ f2) (h3 : src ≠ f3)
    (h4 : f1 ≠ f2) (h5 : f1 ≠ f3) (h6 : f2 ≠ f3) :
    ∀ (w : List BSym) (st : Bool × Bool × Bool) (s : K → List BSym), s src = w →
      s f1 = fl st.1 → s f2 = fl st.2.1 → s f3 = fl st.2.2 →
      ExecLe (autLoop src f1 f2 f3) s
        (fun k => if k = src then [] else if k = f1 then fl (w.foldl vstep st).1
          else if k = f2 then fl (w.foldl vstep st).2.1
          else if k = f3 then fl (w.foldl vstep st).2.2 else s k) (3 * w.length + 1) := by
  intro w
  induction w with
  | nil =>
    intro st s hs e1 e2 e3
    refine ExecLe.of (StackProg.Exec.loopFalse (by simp [hs])) le_rfl |>.congr ?_
    funext k
    by_cases k1 : k = src
    · subst k1; simp [hs]
    by_cases k2 : k = f1
    · subst k2; simp [k1, e1]
    by_cases k3 : k = f2
    · subst k3; simp [k1, k2, e2]
    by_cases k4 : k = f3
    · subst k4; simp [k1, k2, k3, e3]
    simp [k1, k2, k3, k4]
  | cons a w ih =>
    intro st s hs e1 e2 e3
    set s1 := StackProg.applyAct (autAct src f1 f2 f3) s with hs1
    have hcur : (((s f1).head?.isSome, (s f2).head?.isSome, (s f3).head?.isSome) :
        Bool × Bool × Bool) = st := by
      rw [e1, e2, e3, fl_head, fl_head, fl_head]
    have v0 : s1 src = w := by simp [hs1, StackProg.applyAct, autAct, StackAct.apply, hs]
    have v1 : s1 f1 = fl (vstep st a).1 := by
      simp only [hs1, StackProg.applyAct, autAct, Ne.symm h1, if_false, if_true, hs,
        List.head?_cons]
      rw [hcur, e1, fl_head]; exact setFl_apply _ _
    have v2 : s1 f2 = fl (vstep st a).2.1 := by
      simp only [hs1, StackProg.applyAct, autAct, Ne.symm h2, Ne.symm h4, if_false, if_true, hs,
        List.head?_cons]
      rw [hcur, e2, fl_head]; exact setFl_apply _ _
    have v3 : s1 f3 = fl (vstep st a).2.2 := by
      simp only [hs1, StackProg.applyAct, autAct, Ne.symm h3, Ne.symm h5, Ne.symm h6, if_false,
        if_true, hs, List.head?_cons]
      rw [hcur, e3, fl_head]; exact setFl_apply _ _
    have vo : ∀ k, k ≠ src → k ≠ f1 → k ≠ f2 → k ≠ f3 → s1 k = s k := by
      intro k k1 k2 k3 k4; simp [hs1, StackProg.applyAct, autAct, k1, k2, k3, k4, StackAct.apply]
    obtain ⟨n, hn, e⟩ := ih (vstep st a) s1 v0 v1 v2 v3
    refine ⟨1 + 1 + 1 + n, by simp; omega, ?_⟩
    have hpost : (fun k => if k = src then [] else if k = f1 then fl (w.foldl vstep (vstep st a)).1
          else if k = f2 then fl (w.foldl vstep (vstep st a)).2.1
          else if k = f3 then fl (w.foldl vstep (vstep st a)).2.2 else s1 k) =
        (fun k => if k = src then [] else if k = f1 then fl ((a :: w).foldl vstep st).1
          else if k = f2 then fl ((a :: w).foldl vstep st).2.1
          else if k = f3 then fl ((a :: w).foldl vstep st).2.2 else s k) := by
      funext k
      simp only [List.foldl_cons]
      by_cases k1 : k = src; · simp [k1]
      by_cases k2 : k = f1; · simp [k1, k2]
      by_cases k3 : k = f2; · simp [k1, k2, k3]
      by_cases k4 : k = f3; · simp [k1, k2, k3, k4]
      simp [k1, k2, k3, k4, vo k k1 k2 k3 k4]
    rw [← hpost]
    exact StackProg.Exec.loopTrue (by simp [hs]) (StackProg.Exec.act _ s) e

/-! ## Summation into an accumulator -/

lemma exec_sumE (m3 acc tmp car : K) (h1 : m3 ≠ acc) (h2 : m3 ≠ tmp) (h3 : m3 ≠ car)
    (h4 : acc ≠ tmp) (h5 : acc ≠ car) (h6 : tmp ≠ car) (l : List ℕ) (v : ℕ) (s : K → List BSym)
    (hm : s m3 = encNats l) (ha : s acc = tokOf v) (ht : s tmp = []) (hc : s car = []) :
    ExecLe (sumLoop m3 acc tmp car) s
      (Function.update (Function.update s m3 []) acc (tokOf (v + l.sum)))
      ((encNats l).length * (6 * ((Nat.bits v).length + 2 * (encNats l).length) + 13) + 1) := by
  obtain ⟨n, hn, e⟩ := exec_sumLoop m3 acc tmp car h1 h2 h3 h4 h5 h6
    ((Nat.bits v).length + 2 * (encNats l).length) _ (encNats l) (Nat.bits v) s le_rfl le_rfl hm
    ha ht hc
  refine ⟨n, hn, ?_⟩
  rw [sumAcc_bits] at e; exact e

lemma encNats_rep_one (c : ℕ) : encNats (List.replicate c 1) =
    (List.replicate c [BSym.one, BSym.sep]).flatten := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.replicate_succ, encNats_cons, ih, tokOf_one]; simp

lemma encNats_rep (c k : ℕ) : encNats (List.replicate c k) =
    (List.replicate c (tokOf k ++ [BSym.sep])).flatten := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.replicate_succ, encNats_cons, ih]; simp

/-- `dst += |cnt|` for a unary counter `cnt` (consumed); uses `r 0` (empty source),
`r 1` (empty buffer), `r 2 = cnt`, `r 3` (empty scratch) -/
def addOnes (r : Fin 4 ↪ K) (dst tmp car : K) : StackProg K BSym :=
  .seq (pushProg (r 0) .sep) (.seq (pushProg (r 0) .one) (.seq (repeatCopyProg r)
    (.seq (sumLoop (r 1) dst tmp car) (clr (r 0)))))

lemma exec_addOnes (r : Fin 4 ↪ K) (dst tmp car : K)
    (d0 : r 0 ≠ dst) (d1 : r 1 ≠ dst) (d2 : r 2 ≠ dst) (d3 : r 3 ≠ dst)
    (t0 : r 0 ≠ tmp) (t1 : r 1 ≠ tmp) (t2 : r 2 ≠ tmp) (t3 : r 3 ≠ tmp)
    (c0 : r 0 ≠ car) (c1 : r 1 ≠ car) (c2 : r 2 ≠ car) (c3 : r 3 ≠ car)
    (dt : dst ≠ tmp) (dc : dst ≠ car) (tc : tmp ≠ car)
    (c v : ℕ) (s : K → List BSym) (h0 : s (r 0) = []) (h1 : s (r 1) = [])
    (h2 : s (r 2) = List.replicate c .one) (h3 : s (r 3) = []) (hd : s dst = tokOf v)
    (ht : s tmp = []) (hc : s car = []) :
    ExecLe (addOnes r dst tmp car) s (Function.update (Function.update s (r 2) []) dst (tokOf (v + c)))
      (2 * c * (6 * ((Nat.bits v).length + 4 * c) + 13) + 19 * c + 16) := by
  have r01 : r 0 ≠ r 1 := fun h => by simpa using r.injective h
  have r02 : r 0 ≠ r 2 := fun h => by simpa using r.injective h
  have r03 : r 0 ≠ r 3 := fun h => by simpa using r.injective h
  have r12 : r 1 ≠ r 2 := fun h => by simpa using r.injective h
  have r13 : r 1 ≠ r 3 := fun h => by simpa using r.injective h
  have r23 : r 2 ≠ r 3 := fun h => by simpa using r.injective h
  have e1 := exec_pushE (r 0) .sep s
  set s1 := Function.update s (r 0) (BSym.sep :: s (r 0))
  have e2 := exec_pushE (r 0) .one s1
  set s2 := Function.update s1 (r 0) (BSym.one :: s1 (r 0))
  have hs2 : s2 (r 0) = [.one, .sep] := by simp [s2, s1, h0]
  have e3 := ExecLe.of (stack_repeat_copy r s2 (by simp [s2, s1, Ne.symm r03, h3])) le_rfl
  set s3 := Function.update (Function.update s2 (r 2) []) (r 1)
    ((List.replicate (s2 (r 2)).length (s2 (r 0))).flatten ++ s2 (r 1))
  have hM : s3 (r 1) = encNats (List.replicate c 1) := by
    simp [s3, s2, s1, Ne.symm r01, Ne.symm r12, h1, h2, encNats_rep_one, Ne.symm r02, h0]
  have e4 := exec_sumE (r 1) dst tmp car d1 t1 c1 dt dc tc _ v s3 hM
    (by simp [s3, s2, s1, Ne.symm d0, Ne.symm d1, Ne.symm d2, hd])
    (by simp [s3, s2, s1, Ne.symm t0, Ne.symm t1, Ne.symm t2, ht])
    (by simp [s3, s2, s1, Ne.symm c0, Ne.symm c1, Ne.symm c2, hc])
  set s4 := Function.update (Function.update s3 (r 1) []) dst
    (tokOf (v + (List.replicate c 1).sum))
  have e5 := exec_clr (r 0) s4
  have e := e1.seq (e2.seq (e3.seq (e4.seq e5)))
  refine (e.congr ?_).mono ?_
  · funext k
    simp only [s4, s3, s2, s1, Function.update_apply, List.sum_replicate, smul_eq_mul, mul_one]
    by_cases k0 : k = r 0; · subst k0; simp [d0, Ne.symm d0, r02, h0]
    by_cases k1 : k = r 1; · subst k1; simp [k0, Ne.symm d1, r12, h1]
    by_cases k2 : k = r 2; · subst k2; simp [k0, k1, Ne.symm d2]
    by_cases kd : k = dst; · subst kd; simp [k0, k1, k2]
    simp [k0, k1, k2, kd]
  · have hl2 : (s2 (r 2)).length = c := by simp [s2, s1, Ne.symm r02, h2]
    have hl4 : (s4 (r 0)).length = 2 := by
      simp [s4, s3, s2, s1, d0, r01, r02, h0]
    rw [hl4, hs2, hl2]
    simp only [List.length_cons, List.length_nil]
    have : (encNats (List.replicate c 1)).length = 2 * c := by
      rw [encNats_rep_one]; simp; ring
    rw [this]; ring_nf; omega

/-! ## Loops over the tokens of a code -/

def tokLoop (inp : K) (body : StackProg K BSym) : StackProg K BSym :=
  .loop (fun h => (h inp).isSome) body

lemma exec_tokLoop (inp R : K) (hiR : inp ≠ R) (body : StackProg K BSym)
    (Pre : (K → List BSym) → Prop) (F : ℕ → List BSym) (Bd : ℕ) (Q : ℕ → Prop)
    (hPre : ∀ s rest x, Pre s → Pre (Function.update (Function.update s inp rest) R x))
    (hb : ∀ k rest s, Q k → s inp = tokOf k ++ .sep :: rest → Pre s →
      ExecLe body s (Function.update (Function.update s inp rest) R (F k ++ s R)) Bd) :
    ∀ (l : List ℕ) (s : K → List BSym), (∀ v ∈ l, Q v) → s inp = encNats l → Pre s →
      ExecLe (tokLoop inp body) s
        (Function.update (Function.update s inp []) R ((l.reverse.map F).flatten ++ s R))
        (l.length * (Bd + 2) + 1)
  | [], s, _, hs, _ => by
    have hs' : s inp = [] := by simpa [encNats] using hs
    refine ExecLe.of (StackProg.Exec.loopFalse (by simp [hs'])) (by simp) |>.congr ?_
    funext j; by_cases h1 : j = R
    · subst h1; simp [Ne.symm hiR]
    · by_cases h2 : j = inp
      · subst h2; simp [hs', h1]
      · simp [h1, h2]
  | k :: l, s, hl, hs, hp => by
    rw [encNats_cons] at hs
    obtain ⟨n, hn, e⟩ := hb k (encNats l) s (hl k (by simp)) hs hp
    set s1 := Function.update (Function.update s inp (encNats l)) R (F k ++ s R)
    obtain ⟨m, hm, e'⟩ := exec_tokLoop inp R hiR body Pre F Bd Q hPre hb l s1
      (fun v hv => hl v (by simp [hv])) (by simp [s1, hiR]) (hPre _ _ _ hp)
    refine ⟨1 + n + 1 + m, ?_, ?_⟩
    · simp only [List.length_cons]; nlinarith
    · have hpost : Function.update (Function.update s1 inp []) R
          ((l.reverse.map F).flatten ++ s1 R) = Function.update (Function.update s inp []) R
          (((k :: l).reverse.map F).flatten ++ s R) := by
        funext j; by_cases h1 : j = R
        · subst h1; simp [s1]
        · by_cases h2 : j = inp
          · subst h2; simp [s1, h1]
          · simp [s1, h1, h2]
      rw [← hpost]
      exact StackProg.Exec.loopTrue (by simp [hs]) e e'

end lib

end OMK


set_option linter.all false

set_option autoImplicit false

namespace OMK
open CookPvsNP ProjSchedTW.Complexity

inductive Key
  | inp | W | sc | o | z | bad | T | B | A | X | Y | tmp | car | D | R | out | M | C | V | S | N
  | Q | K1 | U | P | Z | Mb | M1 | M2
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .W, .sc, .o, .z, .bad, .T, .B, .A, .X, .Y, .tmp, .car, .D, .R, .out, .M, .C, .V,
    .S, .N, .Q, .K1, .U, .P, .Z, .Mb, .M1, .M2}
  complete := by intro x; cases x <;> simp

abbrev Store := Key → List BSym

def initS (w : List BSym) : Store := fun k => if k = .inp then w else []

/-! ## Validation prefix -/

def valP : StackProg Key BSym :=
  .seq (copyProg .inp .W .sc) (.seq (pushProg .z .one) (autLoop .W .o .z .bad))

def vtest (h : Key → Option BSym) : Bool := (h .o).isNone && (h .z).isNone && (h .bad).isNone

def wrap (main : StackProg Key BSym) : StackProg Key BSym := .seq valP (.branch vtest main skipP)

def valStore (w : List BSym) : Store := fun k =>
  if k = .inp then w else if k = .o then fl (vrun w).1 else if k = .z then fl (vrun w).2.1
  else if k = .bad then fl (vrun w).2.2 else []

lemma exec_valP (w : List BSym) : ExecLe valP (initS w) (valStore w) (9 * w.length + 7) := by
  have e1 := exec_copyE Key.inp Key.W Key.sc (by decide) (by decide) (by decide) (initS w) rfl
  have e2 := exec_pushE Key.z BSym.one
    (Function.update (initS w) Key.W (initS w Key.inp ++ initS w Key.W))
  have e3 := exec_autLoop Key.W Key.o Key.z Key.bad (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) w (false, true, false)
    (Function.update (Function.update (initS w) Key.W (initS w Key.inp ++ initS w Key.W)) Key.z
      (BSym.one :: (Function.update (initS w) Key.W (initS w Key.inp ++ initS w Key.W)) Key.z))
    (by simp [initS]) (by simp [initS, fl]) (by simp [initS, fl]) (by simp [initS, fl])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono (by simp [initS]; omega)
  funext k; cases k <;> simp [valStore, initS, vrun]

lemma valStore_valid {w : List BSym} (h : vrun w = (false, false, false)) : valStore w = initS w := by
  funext k; cases k <;> simp [valStore, initS, h, fl]

lemma exec_wrap_invalid (main : StackProg Key BSym) (w : List BSym)
    (h : vrun w ≠ (false, false, false)) :
    ExecLe (wrap main) (initS w) (valStore w) (9 * w.length + 10) := by
  have e := (exec_valP w).seq (ExecLe.brF (p := main) (test := vtest) ?_ (exec_skip (valStore w)))
  · exact e.mono (by omega)
  · rcases hv : vrun w with ⟨o, z, b⟩
    rw [hv] at h
    simp only [vtest, valStore, fl]
    cases o <;> cases z <;> cases b <;> simp_all

lemma exec_wrap_valid (main : StackProg Key BSym) (w : List BSym) (t : Store) (B : ℕ)
    (h : vrun w = (false, false, false)) (hm : ExecLe main (initS w) t B) :
    ExecLe (wrap main) (initS w) t (9 * w.length + B + 9) := by
  have e := (exec_valP w).seq (ExecLe.brT (p := main) (q := skipP) (test := vtest) ?_
    (by rw [valStore_valid h]; exact hm))
  · exact e.mono (by omega)
  · simp [vtest, valStore, h, fl]

/-! ## Loop helpers -/

lemma ExecLe.loopT {test : (Key → Option BSym) → Bool} {p : StackProg Key BSym}
    {s t u : Store} {B1 B2 : ℕ} (ht : test (fun k => (s k).head?) = true)
    (h1 : ExecLe p s t B1) (h2 : ExecLe (.loop test p) t u B2) :
    ExecLe (.loop test p) s u (B1 + B2 + 2) := by
  obtain ⟨n, hn, e1⟩ := h1; obtain ⟨m, hm, e2⟩ := h2
  exact ⟨1 + n + 1 + m, by omega, StackProg.Exec.loopTrue ht e1 e2⟩

lemma ExecLe.loopF {test : (Key → Option BSym) → Bool} {p : StackProg Key BSym}
    {s : Store} (ht : test (fun k => (s k).head?) = false) :
    ExecLe (.loop test p) s s 1 := ⟨1, le_rfl, StackProg.Exec.loopFalse ht⟩

lemma len_bits_le_of_le {x y L : ℕ} (h : x ≤ y) (hy : y < 2 ^ L) : (Nat.bits x).length ≤ L :=
  bits_length_le_of_lt (lt_of_le_of_lt h hy)

lemma encNats_single (z : ℕ) : encNats [z] = tokOf z ++ [.sep] := by
  simp [encNats, encNat_eq]

lemma tokOf_double {x : ℕ} (hx : 0 < x) : tokOf (2 * x) = .zero :: tokOf x := by
  have : Nat.bits (2 * x) = false :: Nat.bits x := by
    have h := Nat.bits_append_bit x false (fun h => by omega)
    simpa [Nat.bit] using h
  simp [tokOf, this, enc, toB]

/-! ## Binary multiplication by shift-and-add -/

/-- `V += Z` (Z kept) -/
def addZ : StackProg Key BSym :=
  .seq (pushProg .Y .sep) (.seq (copyProg .Z .Y .sc) (sumLoop .Y .V .tmp .car))

def bitBody : StackProg Key BSym :=
  .seq (.branch (fun h => decide (h .Mb = some .one)) addZ skipP)
    (.seq (pushProg .Z .zero) (popProg .Mb))

def bitLoop : StackProg Key BSym := .loop (fun h => (h .Mb).isSome) bitBody

lemma exec_addZ (z q Lb : ℕ) (s : Store) (hZ : s .Z = tokOf z) (hV : s .V = tokOf q)
    (hY : s .Y = []) (ht : s .tmp = []) (hc : s .car = []) (hsc : s .sc = [])
    (hz : z < 2 ^ Lb) (hq : q < 2 ^ Lb) :
    ExecLe addZ s (Function.update s .V (tokOf (q + z))) (30 * (Lb + 2) ^ 2) := by
  have hzl : (tokOf z).length ≤ Lb := by simpa [tokOf, enc] using bits_length_le_of_lt hz
  have hql : (Nat.bits q).length ≤ Lb := bits_length_le_of_lt hq
  have e1 := exec_pushE Key.Y BSym.sep s
  set s1 := Function.update s Key.Y (BSym.sep :: s Key.Y)
  have e2 := exec_copyE Key.Z Key.Y Key.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, hsc])
  set s2 := Function.update s1 Key.Y (s1 Key.Z ++ s1 Key.Y)
  have e3 := exec_sumE Key.Y Key.V Key.tmp Key.car (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) [z] q s2 (by simp [s2, s1, hZ, hY, encNats_single])
    (by simp [s2, s1, hV]) (by simp [s2, s1, ht]) (by simp [s2, s1, hc])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · funext k; cases k <;> simp [s2, s1, hY]
  · simp only [s1, Function.update_self, Function.update_of_ne (show Key.Z ≠ Key.Y by decide),
      hZ, encNats_single, List.length_append, List.length_cons, List.length_nil]
    nlinarith

lemma exec_bitLoop (Lb : ℕ) : ∀ (d : List Bool) (z q : ℕ) (s : Store), 0 < z →
    s .Mb = enc d → s .Z = tokOf z → s .V = tokOf q → s .Y = [] → s .tmp = [] → s .car = [] →
    s .sc = [] → q + z * bval d < 2 ^ Lb → z * 2 ^ d.length < 2 ^ Lb →
    ExecLe bitLoop s (Function.update (Function.update (Function.update s .Mb [])
      .Z (tokOf (z * 2 ^ d.length))) .V (tokOf (q + z * bval d)))
      (d.length * (40 * (Lb + 2) ^ 2) + 1)
  | [], z, q, s, _, hMb, hZ, hV, _, _, _, _, _, _ => by
    unfold bitLoop
    simp only [List.length_nil, zero_mul, zero_add]
    refine (ExecLe.loopF (test := fun h => (h Key.Mb).isSome) (p := bitBody) (s := s)
      (by simp [hMb, enc])).congr ?_
    funext k; cases k <;> simp [hMb, hZ, hV, enc, bval]
  | b :: d, z, q, s, hz0, hMb, hZ, hV, hY, ht, hc, hsc, h1, h2 => by
    have hbv : bval (b :: d) = (if b then 1 else 0) + 2 * bval d := by
      cases b <;> simp [bval, Nat.bit] <;> ring
    set q' := q + (if b then z else 0) with hq'
    have hz2 : z * 2 ^ (b :: d).length = 2 * z * 2 ^ d.length := by simp [pow_succ]; ring
    have hq2 : q + z * bval (b :: d) = q' + 2 * z * bval d := by rw [hbv, hq']; split_ifs <;> ring
    -- the branch
    have eB : ExecLe (.branch (fun h => decide (h .Mb = some .one)) addZ skipP) s
        (Function.update s .V (tokOf q')) (30 * (Lb + 2) ^ 2 + 1) := by
      cases b
      · refine ((ExecLe.brF (by simp [hMb, enc, toB]) (exec_skip s)).congr ?_).mono
          (by have : 0 < (Lb + 2) ^ 2 := by positivity
              omega)
        funext k; cases k <;> simp [hq', hV]
      · have hzl : z < 2 ^ Lb := by
          have : z ≤ z * 2 ^ (true :: d).length := Nat.le_mul_of_pos_right _ (by positivity)
          omega
        have hql : q < 2 ^ Lb := by omega
        exact (ExecLe.brT (by simp [hMb, enc, toB]) (exec_addZ z q Lb s hZ hV hY ht hc hsc hzl hql))
    set s1 := Function.update s Key.V (tokOf q')
    have e2 := exec_pushE Key.Z BSym.zero s1
    set s2 := Function.update s1 Key.Z (BSym.zero :: s1 Key.Z)
    have e3 := exec_popE Key.Mb s2
    set s3 := Function.update s2 Key.Mb (s2 Key.Mb).tail
    have eBody : ExecLe bitBody s s3 (30 * (Lb + 2) ^ 2 + 5) :=
      (eB.seq (e2.seq e3)).mono (by generalize (Lb + 2) ^ 2 = X; omega)
    have ih := exec_bitLoop Lb d (2 * z) q' s3 (by omega)
      (by simp [s3, s2, s1, hMb, enc]) (by simp [s3, s2, s1, hZ, tokOf_double hz0])
      (by simp [s3, s2, s1]) (by simp [s3, s2, s1, hY]) (by simp [s3, s2, s1, ht])
      (by simp [s3, s2, s1, hc]) (by simp [s3, s2, s1, hsc]) (by rw [← hq2]; exact h1)
      (by rw [← hz2]; exact h2)
    unfold bitLoop at ih ⊢
    refine ((ExecLe.loopT (by simp [hMb, enc]) eBody ih).congr ?_).mono ?_
    · have hz3 : 2 * z * 2 ^ d.length = z * 2 ^ (d.length + 1) := by ring
      funext k; cases k <;> simp [s3, s2, s1, hz3, hq2]
    · simp only [List.length_cons, Nat.succ_mul]
      have hX : 4 ≤ (Lb + 2) ^ 2 := by
        have := Nat.pow_le_pow_left (show 2 ≤ Lb + 2 by omega) 2; simpa using this
      generalize (Lb + 2) ^ 2 = X at *
      generalize d.length * (40 * X) = Y
      omega

/-! ## One step of the quadratic sum: `P += x`, `V += x * P` -/

def qBody : StackProg Key BSym :=
  .seq (moveTok2 .W .M1 .M2) (.seq (popProg .W) (.seq (pushProg .X .sep) (.seq (tr1 .M1 .X)
    (.seq (sumLoop .X .P .tmp .car) (.seq (copyProg .P .Z .sc) (.seq (tr1 .M2 .Mb)
    (.seq bitLoop (clr .Z))))))))

lemma tok_stop (rest : List BSym) : stopAt ne (BSym.sep :: rest) := by simp [stopAt]

lemma bits_len_le {x L : ℕ} (h : x < 2 ^ L) : (tokOf x).length ≤ L := by
  simpa [tokOf, enc] using bits_length_le_of_lt h

lemma exec_qBody (Lb x p q : ℕ) (rest : List BSym) (s : Store) (hx0 : 0 < x)
    (hW : s .W = tokOf x ++ .sep :: rest) (hP : s .P = tokOf p) (hV : s .V = tokOf q)
    (hM1 : s .M1 = []) (hM2 : s .M2 = []) (hX : s .X = []) (hZ : s .Z = []) (hMb : s .Mb = [])
    (hY : s .Y = []) (ht : s .tmp = []) (hc : s .car = []) (hsc : s .sc = [])
    (hq : q + (p + x) * x < 2 ^ Lb) (hz : (p + x) * 2 ^ (Nat.bits x).length < 2 ^ Lb) :
    ExecLe qBody s (Function.update (Function.update (Function.update s .W rest) .P
      (tokOf (p + x))) .V (tokOf (q + (p + x) * x))) (60 * (Lb + 2) ^ 3) := by
  have hpx : p + x ≤ (p + x) * 2 ^ (Nat.bits x).length := Nat.le_mul_of_pos_right _ (by positivity)
  have hxl : (tokOf x).length ≤ Lb := bits_len_le (by omega)
  have hpl : (Nat.bits p).length ≤ Lb := bits_length_le_of_lt (by omega)
  have hpxl : (tokOf (p + x)).length ≤ Lb := bits_len_le (by omega)
  have hzl : (tokOf ((p + x) * 2 ^ (Nat.bits x).length)).length ≤ Lb := bits_len_le hz
  have e1 := exec_moveTok2 Key.W Key.M1 Key.M2 (by decide) (by decide) (tokOf x) (.sep :: rest) s
    hW (tokOf_ne x) (tok_stop rest)
  set s1 : Store := fun k => if k = Key.W then BSym.sep :: rest else
      if k = Key.M1 ∨ k = Key.M2 then (tokOf x).reverse ++ s k else s k
  have e2 := exec_popE Key.W s1
  set s2 := Function.update s1 Key.W (s1 Key.W).tail
  have e3 := exec_pushE Key.X BSym.sep s2
  set s3 := Function.update s2 Key.X (BSym.sep :: s2 Key.X)
  have e4 := exec_tr1 Key.M1 Key.X (by decide) s3
  set s4 := Function.update (Function.update s3 Key.M1 []) Key.X ((s3 Key.M1).reverse ++ s3 Key.X)
  have e5 := exec_sumE Key.X Key.P Key.tmp Key.car (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) [x] p s4 (by simp [s4, s3, s2, s1, hX, hM1, encNats_single])
    (by simp [s4, s3, s2, s1, hP]) (by simp [s4, s3, s2, s1, ht]) (by simp [s4, s3, s2, s1, hc])
  set s5 := Function.update (Function.update s4 Key.X []) Key.P (tokOf (p + [x].sum))
  have e6 := exec_copyE Key.P Key.Z Key.sc (by decide) (by decide) (by decide) s5
    (by simp [s5, s4, s3, s2, s1, hsc])
  set s6 := Function.update s5 Key.Z (s5 Key.P ++ s5 Key.Z)
  have e7 := exec_tr1 Key.M2 Key.Mb (by decide) s6
  set s7 := Function.update (Function.update s6 Key.M2 []) Key.Mb ((s6 Key.M2).reverse ++ s6 Key.Mb)
  have e8 := exec_bitLoop Lb (Nat.bits x) (p + x) q s7 (by omega)
    (by simp [s7, s6, s5, s4, s3, s2, s1, hM2, hMb, tokOf])
    (by simp [s7, s6, s5, s4, s3, s2, s1, hZ])
    (by simp [s7, s6, s5, s4, s3, s2, s1, hV]) (by simp [s7, s6, s5, s4, s3, s2, s1, hY])
    (by simp [s7, s6, s5, s4, s3, s2, s1, ht]) (by simp [s7, s6, s5, s4, s3, s2, s1, hc])
    (by simp [s7, s6, s5, s4, s3, s2, s1, hsc]) (by rw [bval_bits]; exact hq) hz
  set s8 := Function.update (Function.update (Function.update s7 Key.Mb []) Key.Z
    (tokOf ((p + x) * 2 ^ (Nat.bits x).length))) Key.V (tokOf (q + (p + x) * bval (Nat.bits x)))
  have e9 := exec_clr Key.Z s8
  have e := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
  refine (e.congr ?_).mono ?_
  · funext k; cases k <;> simp [s8, s7, s6, s5, s4, s3, s2, s1, hM1, hM2, hX, hZ, hMb, bval_bits]
  · have hs3 : (s3 Key.M1).length = (tokOf x).length := by simp [s3, s2, s1, hM1]
    have hs5 : (s5 Key.P).length = (tokOf (p + x)).length := by simp [s5]
    have hs6 : (s6 Key.M2).length = (tokOf x).length := by simp [s6, s5, s4, s3, s2, s1, hM2]
    have hs8 : (s8 Key.Z).length = (tokOf ((p + x) * 2 ^ (Nat.bits x).length)).length := by
      simp [s8]
    rw [hs3, hs5, hs6, hs8]
    have hbx : (Nat.bits x).length = (tokOf x).length := by simp [tokOf, enc]
    rw [hbx]; rw [hbx] at hzl
    simp only [encNats_single, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    have h1 : ((tokOf x).length + 1) * (6 * ((Nat.bits p).length + 2 * ((tokOf x).length + 1)) + 13)
        ≤ (Lb + 1) * (18 * Lb + 25) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (tokOf x).length * (40 * (Lb + 2) ^ 2) ≤ Lb * (40 * (Lb + 2) ^ 2) :=
      Nat.mul_le_mul_right _ hxl
    have h3 : Lb * (40 * (Lb + 2) ^ 2) + (Lb + 1) * (18 * Lb + 25) + 20 * Lb + 30 ≤
        60 * (Lb + 2) ^ 3 := by nlinarith
    omega

lemma len_tok_le_code {l : List ℕ} {k : ℕ} (hk : k ∈ l) : (tokOf k).length ≤ (encNats l).length := by
  induction l with
  | nil => simp at hk
  | cons x l ih =>
    rw [encNats_cons]
    rcases List.mem_cons.1 hk with rfl | hk
    · simp
    · have := ih hk; simp; omega

lemma len_code_ge (l : List ℕ) : l.length ≤ (encNats l).length := by
  induction l with
  | nil => simp [encNats]
  | cons x l ih => rw [encNats_cons]; simp; omega

lemma len_encNats_le (l' : List ℕ) (B : ℕ) (h : ∀ v ∈ l', (tokOf v).length ≤ B) :
    (encNats l').length ≤ l'.length * (B + 1) := by
  induction l' with
  | nil => simp [encNats]
  | cons x l ih =>
    rw [encNats_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    simp; nlinarith

/-! ## The quadratic sum `∑_{j ≤ k} a_j a_k` -/

def qvAux : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, x :: l => (p + x) * x + qvAux (p + x) l

lemma qvAux_append (p : ℕ) : ∀ (l1 l2 : List ℕ),
    qvAux p (l1 ++ l2) = qvAux p l1 + qvAux (p + l1.sum) l2
  | [], l2 => by simp [qvAux]
  | x :: l1, l2 => by
    simp only [List.cons_append, qvAux, List.sum_cons]
    rw [qvAux_append (p + x) l1 l2, Nat.add_assoc p x]; ring

lemma qvAux_le (p : ℕ) : ∀ l : List ℕ, qvAux p l + p ^ 2 ≤ (p + l.sum) ^ 2
  | [] => by simp [qvAux]
  | x :: l => by
    have ih := qvAux_le (p + x) l
    simp only [qvAux, List.sum_cons]
    rw [← Nat.add_assoc]
    nlinarith

/-! ## Loops over tokens with an invariant -/

lemma exec_tokLoopG (inp : Key) (body : StackProg Key BSym) (Inv : List ℕ → Store → Prop)
    (Bd : ℕ) (a : List ℕ)
    (hb : ∀ pre k rest (s : Store), pre ++ [k] <+: a → s inp = tokOf k ++ .sep :: rest →
      Inv pre s → ∃ s', s' inp = rest ∧ Inv (pre ++ [k]) s' ∧ ExecLe body s s' Bd) :
    ∀ (l pre : List ℕ) (s : Store), pre ++ l = a → s inp = encNats l → Inv pre s →
      ∃ s', s' inp = [] ∧ Inv a s' ∧ ExecLe (tokLoop inp body) s s' (l.length * (Bd + 2) + 1)
  | [], pre, s, hpre, hs, hI => by
    have hpa : pre = a := by simpa using hpre
    subst hpa
    refine ⟨s, by simpa [encNats] using hs, hI, ?_⟩
    have hs' : s inp = [] := by simpa [encNats] using hs
    exact (ExecLe.loopF (test := fun h => (h inp).isSome) (p := body) (s := s)
      (by simp [hs'])).mono (by simp)
  | k :: l, pre, s, hpre, hs, hI => by
    rw [encNats_cons] at hs
    obtain ⟨s1, hs1, hI1, e1⟩ := hb pre k (encNats l) s ⟨l, by simpa using hpre⟩ hs hI
    obtain ⟨s2, hs2, hI2, e2⟩ := exec_tokLoopG inp body Inv Bd a hb l (pre ++ [k]) s1
      (by simpa using hpre) hs1 hI1
    refine ⟨s2, hs2, hI2, ?_⟩
    unfold tokLoop at e2 ⊢
    refine (ExecLe.loopT (by simp [hs]) e1 e2).mono ?_
    simp only [List.length_cons]; ring_nf; omega

/-! ## The quadratic phase: `V := D + ∑_{j ≤ k} a_j a_k` -/

def qPhase : StackProg Key BSym :=
  .seq (copyProg .D .V .sc) (.seq (copyProg .inp .W .sc) (.seq (tokLoop .W qBody) (clr .P)))

lemma exec_qPhase (a : List ℕ) (vD Lb : ℕ) (s : Store) (hpos : ∀ v ∈ a, 0 < v)
    (hinp : s .inp = encNats a) (hD : s .D = tokOf vD) (hV : s .V = []) (hW : s .W = [])
    (hP : s .P = []) (hM1 : s .M1 = []) (hM2 : s .M2 = []) (hX : s .X = []) (hZ : s .Z = [])
    (hMb : s .Mb = []) (hY : s .Y = []) (ht : s .tmp = []) (hc : s .car = []) (hsc : s .sc = [])
    (hb1 : vD + qvAux 0 a < 2 ^ Lb) (hb2 : a.sum * 2 ^ (encNats a).length < 2 ^ Lb) :
    ExecLe qPhase s (Function.update s .V (tokOf (vD + qvAux 0 a)))
      (6 * (tokOf vD).length + 6 * (encNats a).length + (a.length * (60 * (Lb + 2) ^ 3 + 2) + 1)
        + 3 * (tokOf a.sum).length + 10) := by
  have e1 := exec_copyE Key.D Key.V Key.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s Key.V (s Key.D ++ s Key.V)
  have e2 := exec_copyE Key.inp Key.W Key.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, hsc])
  set s2 := Function.update s1 Key.W (s1 Key.inp ++ s1 Key.W)
  let Inv : List ℕ → Store → Prop := fun pre t =>
    (∀ k, k ≠ Key.W → k ≠ Key.P → k ≠ Key.V → t k = s k) ∧ t .P = tokOf pre.sum ∧
      t .V = tokOf (vD + qvAux 0 pre)
  have hI0 : Inv [] s2 := by
    refine ⟨fun k h1 h2 h3 => ?_, by simp [s2, s1, hP, tokOf_zero], by simp [s2, s1, hD, hV, qvAux]⟩
    simp [s2, s1, h1, h3]
  obtain ⟨t, htW, ⟨htI, htP, htV⟩, e3⟩ := exec_tokLoopG Key.W qBody Inv (60 * (Lb + 2) ^ 3) a
    (by
      intro pre k rest u hpref hu ⟨hI1, hI2, hI3⟩
      obtain ⟨post, hpost⟩ := hpref
      have hk : k ∈ a := by rw [← hpost]; simp
      have hsumle : pre.sum + k ≤ a.sum := by
        rw [← hpost]; simp [List.sum_append]
      have hqle : qvAux 0 (pre ++ [k]) ≤ qvAux 0 a := by
        rw [← hpost, qvAux_append 0 (pre ++ [k]) post]; omega
      have hqk : qvAux 0 (pre ++ [k]) = qvAux 0 pre + (pre.sum + k) * k := by
        rw [qvAux_append]; simp [qvAux]
      have hkl : (Nat.bits k).length ≤ (encNats a).length := by
        have := len_tok_le_code hk; simpa [tokOf, enc] using this
      have hz : (pre.sum + k) * 2 ^ (Nat.bits k).length < 2 ^ Lb := by
        have : (pre.sum + k) * 2 ^ (Nat.bits k).length ≤ a.sum * 2 ^ (encNats a).length :=
          Nat.mul_le_mul hsumle (Nat.pow_le_pow_right (by norm_num) hkl)
        omega
      refine ⟨_, by simp, ⟨?_, ?_, ?_⟩, exec_qBody Lb k pre.sum (vD + qvAux 0 pre) rest u
        (hpos k hk) hu hI2 hI3 (by rw [hI1 _ (by decide) (by decide) (by decide), hM1])
        (by rw [hI1 _ (by decide) (by decide) (by decide), hM2])
        (by rw [hI1 _ (by decide) (by decide) (by decide), hX])
        (by rw [hI1 _ (by decide) (by decide) (by decide), hZ])
        (by rw [hI1 _ (by decide) (by decide) (by decide), hMb])
        (by rw [hI1 _ (by decide) (by decide) (by decide), hY])
        (by rw [hI1 _ (by decide) (by decide) (by decide), ht])
        (by rw [hI1 _ (by decide) (by decide) (by decide), hc])
        (by rw [hI1 _ (by decide) (by decide) (by decide), hsc]) (by omega) hz⟩
      · intro j h1 h2 h3; simp [h1, h2, h3, hI1 j h1 h2 h3]
      · simp [List.sum_append]
      · simp [hqk]; ring_nf)
    a [] s2 (by simp) (by simp [s2, s1, hinp, hW]) hI0
  have e4 := exec_clr Key.P t
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · funext k
    by_cases k1 : k = Key.W; · subst k1; simp [htW, hW]
    by_cases k2 : k = Key.P; · subst k2; simp [hP]
    by_cases k3 : k = Key.V; · subst k3; simp [htV]
    simp [k1, k2, k3, htI k k1 k2 k3]
  · simp [s1, s2, hD, hV, hinp, hW, htP]; omega

end OMK


set_option linter.all false
set_option autoImplicit false

namespace OMK
open CookPvsNP ProjSchedTW.Complexity

/-! ## Output scripts -/

def baseStore (a : List ℕ) (b t vA vD vU vV : ℕ) (R' : List BSym) : Store := fun k =>
  match k with
  | .inp => encNats a | .B => tokOf b | .T => List.replicate t .one | .A => tokOf vA
  | .D => tokOf vD | .U => tokOf vU | .V => tokOf vV | .R => R' | _ => []

def rO : Fin 4 ↪ Key := ⟨![.Q, .M, .C, .sc], by decide⟩

def loadN : Option Key → StackProg Key BSym
  | none => skipP
  | some k => copyProg k .N .sc

def baseVal (b vA vD vU vV : ℕ) : Option Key → ℕ
  | some .A => vA
  | some .B => b
  | some .D => vD
  | some .U => vU
  | some .V => vV
  | _ => 0

def BaseOK : Option Key → Prop
  | none => True
  | some k => k = .A ∨ k = .B ∨ k = .D ∨ k = .U ∨ k = .V

def cntP (k : Key) (α : Bool) (c : ℕ) : StackProg Key BSym :=
  .seq (if α then copyProg .T k .sc else skipP) (pushSeq k (List.replicate c .one))

def numP (base : Option Key) (α : Bool) (c : ℕ) (dbl : Bool) : StackProg Key BSym :=
  .seq (loadN base) (.seq (cntP .C α c) (.seq (addOnes rO .N .tmp .car)
    (.seq (if dbl then pushProg .R .zero else skipP) (.seq (tr1 .N .R) (pushProg .R .sep)))))


lemma len_tokOf_add (x y L : ℕ) (hx : (tokOf x).length ≤ L) (hy : y ≤ L + 2) :
    (tokOf (x + y)).length ≤ L + 2 := by
  have h1 : x < 2 ^ L := by
    have := lt_two_pow_bits x
    have h2 : 2 ^ (Nat.bits x).length ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by simpa [tokOf, enc] using hx)
    omega
  have h3 : L + 1 < 3 * 2 ^ L := by
    have := Nat.lt_two_pow_self (n := L)
    omega
  have : x + y < 2 ^ (L + 2) := by rw [pow_add]; omega
  simpa [tokOf, enc] using bits_length_le_of_lt this

lemma exec_cntP (k : Key) (hk : k ≠ .T) (hk2 : k ≠ .sc) (α : Bool) (c t : ℕ) (s : Store)
    (h0 : s k = []) (hsc : s .sc = []) (hT : s .T = List.replicate t .one) :
    ExecLe (cntP k α c) s (Function.update s k (List.replicate ((if α then t else 0) + c) .one))
      (6 * t + 2 * c + 6) := by
  cases α
  · have e := (exec_skip s).seq (exec_pushSeq k (List.replicate c .one) s)
    refine (e.congr ?_).mono (by simp; omega)
    simp [h0]
  · have e := (exec_copyE Key.T k Key.sc (Ne.symm hk) (by decide) hk2 s hsc).seq
      (exec_pushSeq k (List.replicate c .one) _)
    refine (e.congr ?_).mono (by simp [hT]; omega)
    funext j; by_cases hj : j = k
    · subst hj; simp only [Function.update_self, h0, List.append_nil, List.reverse_replicate]
      rw [List.replicate_add]; simp [hT, List.replicate_append_replicate, Nat.add_comm]
    · simp [hj]

structure LenOK (a : List ℕ) (b t vA vD vU vV L : ℕ) : Prop where
  ha : (encNats a).length ≤ L
  hb : (tokOf b).length ≤ L
  hA : (tokOf vA).length ≤ L
  hD : (tokOf vD).length ≤ L
  hU : (tokOf vU).length ≤ L
  hV : (tokOf vV).length ≤ L
  ht : t ≤ L

lemma baseVal_len {a : List ℕ} {b t vA vD vU vV L : ℕ} (h : LenOK a b t vA vD vU vV L) (base : Option Key)
    (hb : BaseOK base) : (tokOf (baseVal b vA vD vU vV base)).length ≤ L := by
  rcases base with _ | k
  · simp [baseVal, tokOf_zero]
  · rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact h.hA
    · exact h.hb
    · exact h.hD
    · exact h.hU
    · exact h.hV

lemma exec_loadN (a : List ℕ) (b t vA vD vU vV : ℕ) (R' : List BSym) (base : Option Key)
    (hb : BaseOK base) :
    ExecLe (loadN base) (baseStore a b t vA vD vU vV R')
      (Function.update (baseStore a b t vA vD vU vV R') .N (tokOf (baseVal b vA vD vU vV base)))
      (6 * (tokOf (baseVal b vA vD vU vV base)).length + 3) := by
  rcases base with _ | k
  · refine ((exec_skip _).congr ?_).mono (by omega)
    funext j; cases j <;> simp [baseStore, baseVal, tokOf_zero]
  · rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals
      refine ((exec_copyE _ Key.N Key.sc (by decide) (by decide) (by decide) _ rfl).congr ?_).mono
        (by simp [baseStore, baseVal])
      funext j; cases j <;> simp [baseStore, baseVal]

lemma exec_num (a : List ℕ) (b t vA vD vU vV L : ℕ) (R' : List BSym) (hL : LenOK a b t vA vD vU vV L)
    (base : Option Key) (hb : BaseOK base) (α : Bool) (c : ℕ) (hc : c ≤ 2) (dbl : Bool)
    (hpos : dbl = true → 0 < baseVal b vA vD vU vV base + ((if α then t else 0) + c)) :
    ExecLe (numP base α c dbl) (baseStore a b t vA vD vU vV R')
      (baseStore a b t vA vD vU vV ((encNat (if dbl then 2 * (baseVal b vA vD vU vV base +
        ((if α then t else 0) + c)) else baseVal b vA vD vU vV base + ((if α then t else 0) + c))).reverse
        ++ R')) (100 * (L + 3) ^ 2) := by
  set v0 := baseVal b vA vD vU vV base
  set c' := (if α then t else 0) + c
  have hc' : c' ≤ L + 2 := by simp only [c']; split_ifs <;> have := hL.ht <;> omega
  have hv0 := baseVal_len hL base hb
  have e1 := exec_loadN a b t vA vD vU vV R' base hb
  set s1 := Function.update (baseStore a b t vA vD vU vV R') Key.N (tokOf v0)
  have e2 := exec_cntP Key.C (by decide) (by decide) α c t s1 (by simp [s1, baseStore])
    (by simp [s1, baseStore]) (by simp [s1, baseStore])
  set s2 := Function.update s1 Key.C (List.replicate c' .one)
  have e3 := exec_addOnes rO Key.N Key.tmp Key.car (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) c' v0 s2 (by simp [rO, s2, s1, baseStore])
    (by simp [rO, s2, s1, baseStore]) (by simp [rO, s2, s1, baseStore])
    (by simp [rO, s2, s1, baseStore]) (by simp [s2, s1, baseStore])
    (by simp [s2, s1, baseStore]) (by simp [s2, s1, baseStore])
  set s3 := Function.update (Function.update s2 (rO 2) []) Key.N (tokOf (v0 + c'))
  have hlen3 : (tokOf (v0 + c')).length ≤ L + 2 := len_tokOf_add _ _ _ hv0 hc'
  cases dbl
  · have e4 := exec_skip s3
    have e5 := exec_tr1 Key.N Key.R (by decide) s3
    have e6 := exec_pushE Key.R BSym.sep
      (Function.update (Function.update s3 Key.N []) Key.R ((s3 Key.N).reverse ++ s3 Key.R))
    have e := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
    refine (e.congr ?_).mono ?_
    · funext j; cases j <;> simp [s3, s2, s1, rO, baseStore, encNat_eq]
    · have hN : (s3 Key.N).length ≤ L + 2 := by simpa [s3] using hlen3
      have hb2 : (Nat.bits v0).length ≤ L := by simpa [tokOf, enc] using hv0
      have : 2 * c' * (6 * ((Nat.bits v0).length + 4 * c') + 13) ≤
          2 * (L + 2) * (6 * (L + 4 * (L + 2)) + 13) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hc') (by omega)
      have ht := hL.ht
      nlinarith
  · have e4 := exec_pushE Key.R BSym.zero s3
    set s4 := Function.update s3 Key.R (BSym.zero :: s3 Key.R)
    have e5 := exec_tr1 Key.N Key.R (by decide) s4
    have e6 := exec_pushE Key.R BSym.sep
      (Function.update (Function.update s4 Key.N []) Key.R ((s4 Key.N).reverse ++ s4 Key.R))
    have e := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
    refine (e.congr ?_).mono ?_
    · have hp := hpos rfl
      funext j; cases j <;> simp [s4, s3, s2, s1, rO, baseStore, encNat_eq, tokOf_double hp]
    · have hN : (s4 Key.N).length ≤ L + 2 := by simpa [s4, s3] using hlen3
      have hb2 : (Nat.bits v0).length ≤ L := by simpa [tokOf, enc] using hv0
      have : 2 * c' * (6 * ((Nat.bits v0).length + 4 * c') + 13) ≤
          2 * (L + 2) * (6 * (L + 4 * (L + 2)) + 13) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hc') (by omega)
      have ht := hL.ht
      nlinarith

/-! ### constants, lines and grids of zeros -/

lemma exec_consts (a : List ℕ) (b t vA vD vU vV : ℕ) (R' : List BSym) (cs : List ℕ) :
    ExecLe (pushSeq Key.R (encNats cs)) (baseStore a b t vA vD vU vV R')
      (baseStore a b t vA vD vU vV ((encNats cs).reverse ++ R')) (2 * (encNats cs).length + 1) := by
  refine (exec_pushSeq Key.R (encNats cs) _).congr ?_
  funext j; cases j <;> simp [baseStore]

lemma encNats_rep_zero (n : ℕ) : encNats (List.replicate n 0) = List.replicate n .sep := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, encNats_cons, ih, tokOf_zero]; simp [List.replicate_succ]

lemma flatten_rep_sep (n m : ℕ) :
    (List.replicate n (List.replicate m BSym.sep)).flatten = List.replicate (n * m) .sep := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm,
      List.replicate_add]

/-! ### job loops -/

def jobsP (body : StackProg Key BSym) : StackProg Key BSym :=
  .seq (copyProg .inp .W .sc) (tokLoop .W body)

lemma encNats_flatten (L : List (List ℕ)) : encNats L.flatten = (L.map encNats).flatten := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [encNats_append, ih]

lemma exec_jobs (a : List ℕ) (b t vA vD vU vV : ℕ) (R' : List BSym) (hpos : ∀ v ∈ a, 0 < v)
    (body : StackProg Key BSym) (blk : ℕ → List ℕ) (Bd : ℕ)
    (hbody : ∀ k rest (s : Store), k ∈ a → s .W = tokOf k ++ .sep :: rest → s .S = [] → s .X = [] →
      s .sc = [] → s .U = tokOf vU → s .B = tokOf b → ExecLe body s (Function.update (Function.update s .W rest) .R
        ((encNats (blk k)).reverse ++ s .R)) Bd) :
    ExecLe (jobsP body) (baseStore a b t vA vD vU vV R')
      (baseStore a b t vA vD vU vV ((encNats ((a.map blk).flatten)).reverse ++ R'))
      (6 * (encNats a).length + 3 + (a.length * (Bd + 2) + 1) + 1) := by
  have e1 := exec_copyE Key.inp Key.W Key.sc (by decide) (by decide) (by decide)
    (baseStore a b t vA vD vU vV R') rfl
  set s1 := Function.update (baseStore a b t vA vD vU vV R') Key.W
    (baseStore a b t vA vD vU vV R' Key.inp ++ baseStore a b t vA vD vU vV R' Key.W)
  have e2 := exec_tokLoop Key.W Key.R (by decide) body
    (fun s => s .S = [] ∧ s .X = [] ∧ s .sc = [] ∧ s .U = tokOf vU ∧ s .B = tokOf b)
    (fun k => (encNats (blk k)).reverse) Bd (fun k => k ∈ a)
    (by intro s rest x ⟨h1, h2, h3, h4, h5⟩
        exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5]⟩)
    (fun k rest s hk hs hp => hbody k rest s hk hs hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2)
    a s1 (fun v hv => hv)
    (by simp [s1, baseStore]) ⟨by simp [s1, baseStore], by simp [s1, baseStore],
      by simp [s1, baseStore], by simp [s1, baseStore], by simp [s1, baseStore]⟩
  refine ((e1.seq e2).congr ?_).mono (by simp [baseStore])
  funext j; cases j <;> simp [s1, baseStore]
  simp [encNats_flatten, List.reverse_flatten, List.map_reverse, Function.comp_def]


/-! ### job bodies -/

/-- append the code of the number stored in `k` to `R` (reversed) -/
def emitK (k : Key) : StackProg Key BSym :=
  .seq (copyProg k .X .sc) (.seq (tr1 .X .R) (pushProg .R .sep))

lemma exec_emitK (k : Key) (h1 : k ≠ .X) (h2 : k ≠ .sc) (h3 : k ≠ .R) (v : ℕ) (s : Store)
    (hk : s k = tokOf v) (hX : s .X = []) (hsc : s .sc = []) :
    ExecLe (emitK k) s (Function.update s .R ((encNat v).reverse ++ s .R))
      (9 * (tokOf v).length + 8) := by
  have e1 := exec_copyE k Key.X Key.sc h1 h2 (by decide) s hsc
  set s1 := Function.update s Key.X (s k ++ s Key.X)
  have e2 := exec_tr1 Key.X Key.R (by decide) s1
  set s2 := Function.update (Function.update s1 Key.X []) Key.R ((s1 Key.X).reverse ++ s1 Key.R)
  have e3 := exec_pushE Key.R BSym.sep s2
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · funext j
    by_cases j1 : j = Key.R
    · subst j1; simp [s2, s1, hk, hX, encNat_eq, Ne.symm h3]
    by_cases j2 : j = Key.X
    · subst j2; simp [s2, s1, hX]
    · simp [s2, s1, j1, j2]
  · simp [s1, hk, hX]; omega

/-- move the leading token of `W` to `R` twice (as two numbers) -/
def dupTok : StackProg Key BSym :=
  .seq (moveTok2 .W .R .S) (.seq (popProg .W) (.seq (pushProg .R .sep) (.seq (tr1 .S .X)
    (.seq (tr1 .X .R) (pushProg .R .sep)))))

lemma exec_dupTok (k : ℕ) (rest : List BSym) (s : Store) (hs : s .W = tokOf k ++ .sep :: rest)
    (hS : s .S = []) (hX : s .X = []) :
    ExecLe dupTok s (Function.update (Function.update s .W rest) .R
      ((encNats [k, k]).reverse ++ s .R)) (9 * (tokOf k).length + 12) := by
  have e2 := exec_moveTok2 Key.W Key.R Key.S (by decide) (by decide) (tokOf k) (.sep :: rest) s
    hs (tokOf_ne k) (tok_stop rest)
  set s2 : Store := fun j => if j = Key.W then BSym.sep :: rest else
      if j = Key.R ∨ j = Key.S then (tokOf k).reverse ++ s j else s j
  have e3 := exec_popE Key.W s2
  set s3 := Function.update s2 Key.W (s2 Key.W).tail
  have e4 := exec_pushE Key.R BSym.sep s3
  set s4 := Function.update s3 Key.R (BSym.sep :: s3 Key.R)
  have e6 := exec_tr1 Key.S Key.X (by decide) s4
  set s6 := Function.update (Function.update s4 Key.S []) Key.X ((s4 Key.S).reverse ++ s4 Key.X)
  have e7 := exec_tr1 Key.X Key.R (by decide) s6
  set s7 := Function.update (Function.update s6 Key.X []) Key.R ((s6 Key.X).reverse ++ s6 Key.R)
  have e8 := exec_pushE Key.R BSym.sep s7
  refine ((e2.seq (e3.seq (e4.seq (e6.seq (e7.seq e8))))).congr ?_).mono ?_
  · funext j; cases j <;> simp [s7, s6, s4, s3, s2, encNats, encNat_eq, hS, hX]
  · simp [s6, s4, s3, s2, hS, hX]; omega

def bodyCF : StackProg Key BSym :=
  .seq (moveTok .W .R) (.seq (popProg .W) (.seq (pushProg .R .sep)
    (.seq (pushSeq .R (encNats [1, 0])) (emitK .U))))

def bodyE : StackProg Key BSym :=
  .seq dupTok (.seq (pushSeq .R (encNats [0])) (emitK .B))

def bodyB : StackProg Key BSym :=
  .seq dupTok (.seq (pushSeq .R (encNats [0])) (emitK .U))

def blkCF (vU x : ℕ) : List ℕ := [x, 1, 0, vU]
def blkE (b x : ℕ) : List ℕ := [x, x, 0, b]
def blkB (vU x : ℕ) : List ℕ := [x, x, 0, vU]

lemma exec_bodyCF (vU k : ℕ) (rest : List BSym) (s : Store) (hs : s .W = tokOf k ++ .sep :: rest)
    (hX : s .X = []) (hsc : s .sc = []) (hU : s .U = tokOf vU) :
    ExecLe bodyCF s (Function.update (Function.update s .W rest) .R
      ((encNats (blkCF vU k)).reverse ++ s .R)) (3 * (tokOf k).length + 9 * (tokOf vU).length + 30) := by
  have e1 := exec_moveTok Key.W Key.R (by decide) (tokOf k) (.sep :: rest) s hs
    (tokOf_ne k) (tok_stop rest)
  set s1 := Function.update (Function.update s Key.W (BSym.sep :: rest)) Key.R
    ((tokOf k).reverse ++ s Key.R)
  have e2 := exec_popE Key.W s1
  set s2 := Function.update s1 Key.W (s1 Key.W).tail
  have e3 := exec_pushE Key.R BSym.sep s2
  set s3 := Function.update s2 Key.R (BSym.sep :: s2 Key.R)
  have e4 := exec_pushSeq Key.R (encNats [1, 0]) s3
  set s4 := Function.update s3 Key.R ((encNats [1, 0]).reverse ++ s3 Key.R)
  have e5 := exec_emitK Key.U (by decide) (by decide) (by decide) vU s4 (by simp [s4, s3, s2, s1, hU])
    (by simp [s4, s3, s2, s1, hX]) (by simp [s4, s3, s2, s1, hsc])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr ?_).mono ?_
  · funext j; cases j <;> simp [s4, s3, s2, s1, blkCF, encNats, encNat_eq, tokOf_zero, tokOf_one]
  · simp [encNats, encNat_eq, tokOf_zero, tokOf_one]; omega

lemma exec_bodyE (b k : ℕ) (rest : List BSym) (s : Store) (hs : s .W = tokOf k ++ .sep :: rest)
    (hS : s .S = []) (hX : s .X = []) (hsc : s .sc = []) (hB : s .B = tokOf b) :
    ExecLe bodyE s (Function.update (Function.update s .W rest) .R
      ((encNats (blkE b k)).reverse ++ s .R)) (9 * (tokOf k).length + 9 * (tokOf b).length + 30) := by
  have e1 := exec_dupTok k rest s hs hS hX
  set s1 := Function.update (Function.update s Key.W rest) Key.R ((encNats [k, k]).reverse ++ s Key.R)
  have e2 := exec_pushSeq Key.R (encNats [0]) s1
  set s2 := Function.update s1 Key.R ((encNats [0]).reverse ++ s1 Key.R)
  have e3 := exec_emitK Key.B (by decide) (by decide) (by decide) b s2 (by simp [s2, s1, hB])
    (by simp [s2, s1, hX]) (by simp [s2, s1, hsc])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · funext j; cases j <;> simp [s2, s1, blkE, encNats, encNat_eq, tokOf_zero]
  · simp [encNats, encNat_eq, tokOf_zero]; omega

lemma exec_bodyB (vU k : ℕ) (rest : List BSym) (s : Store) (hs : s .W = tokOf k ++ .sep :: rest)
    (hS : s .S = []) (hX : s .X = []) (hsc : s .sc = []) (hU : s .U = tokOf vU) :
    ExecLe bodyB s (Function.update (Function.update s .W rest) .R
      ((encNats (blkB vU k)).reverse ++ s .R)) (9 * (tokOf k).length + 9 * (tokOf vU).length + 30) := by
  have e1 := exec_dupTok k rest s hs hS hX
  set s1 := Function.update (Function.update s Key.W rest) Key.R ((encNats [k, k]).reverse ++ s Key.R)
  have e2 := exec_pushSeq Key.R (encNats [0]) s1
  set s2 := Function.update s1 Key.R ((encNats [0]).reverse ++ s1 Key.R)
  have e3 := exec_emitK Key.U (by decide) (by decide) (by decide) vU s2 (by simp [s2, s1, hU])
    (by simp [s2, s1, hX]) (by simp [s2, s1, hsc])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · funext j; cases j <;> simp [s2, s1, blkB, encNats, encNat_eq, tokOf_zero]
  · simp [encNats, encNat_eq, tokOf_zero]; omega

lemma len_tokOf_le (k : ℕ) (l : List ℕ) (hk : k ≤ l.sum) : (tokOf k).length ≤ (encNats l).length := by
  have h1 := sum_lt_pow l
  have : k < 2 ^ (encNats l).length := by omega
  simpa [tokOf, enc] using bits_length_le_of_lt this

/-! ### scripts -/

inductive JK | CF | E | B

inductive Ins
  | consts (cs : List ℕ)
  | num (base : Option Key) (α : Bool) (c : ℕ) (dbl : Bool)
  | jobs (j : JK)

def JK.body : JK → StackProg Key BSym
  | .CF => bodyCF
  | .E => bodyE
  | .B => bodyB

def JK.blk (b vU : ℕ) : JK → ℕ → List ℕ
  | .CF => blkCF vU
  | .E => blkE b
  | .B => blkB vU

def Ins.prog : Ins → StackProg Key BSym
  | .consts cs => pushSeq .R (encNats cs)
  | .num base α c dbl => numP base α c dbl
  | .jobs j => jobsP j.body

def Ins.emit (a : List ℕ) (b t vA vD vU vV : ℕ) : Ins → List ℕ
  | .consts cs => cs
  | .num base α c dbl => [if dbl then 2 * (baseVal b vA vD vU vV base + ((if α then t else 0) + c))
      else baseVal b vA vD vU vV base + ((if α then t else 0) + c)]
  | .jobs j => (a.map (j.blk b vU)).flatten

def Ins.OK (b t vA vD vU vV : ℕ) : Ins → Prop
  | .consts cs => (encNats cs).length ≤ 30
  | .num base α c dbl => BaseOK base ∧ c ≤ 2 ∧
      (dbl = true → 0 < baseVal b vA vD vU vV base + ((if α then t else 0) + c))
  | .jobs _ => True

lemma exec_ins (a : List ℕ) (b t vA vD vU vV L : ℕ) (R' : List BSym)
    (hL : LenOK a b t vA vD vU vV L) (hpos : ∀ v ∈ a, 0 < v) (i : Ins) (hi : i.OK b t vA vD vU vV) :
    ExecLe i.prog (baseStore a b t vA vD vU vV R')
      (baseStore a b t vA vD vU vV ((encNats (i.emit a b t vA vD vU vV)).reverse ++ R'))
      (100 * (L + 3) ^ 2) := by
  cases i with
  | consts cs =>
    refine (exec_consts a b t vA vD vU vV R' cs).mono ?_
    have : (encNats cs).length ≤ 30 := hi
    have : 9 ≤ (L + 3) ^ 2 := by
      have := Nat.pow_le_pow_left (show 3 ≤ L + 3 by omega) 2
      simpa using this
    omega
  | num base α c dbl =>
    obtain ⟨h1, h2, h3⟩ := hi
    have e := exec_num a b t vA vD vU vV L R' hL base h1 α c h2 dbl h3
    refine e.congr ?_
    simp [Ins.emit, encNats]
  | jobs j =>
    have hlen : a.length ≤ L := le_trans (len_code_ge a) hL.ha
    have htok : ∀ k ∈ a, (tokOf k).length ≤ L := fun k hk => le_trans (len_tok_le_code hk) hL.ha
    have key : ExecLe (jobsP j.body) (baseStore a b t vA vD vU vV R')
        (baseStore a b t vA vD vU vV ((encNats ((a.map (j.blk b vU)).flatten)).reverse ++ R'))
        (6 * (encNats a).length + 3 + (a.length * (18 * L + 30 + 2) + 1) + 1) := by
      apply exec_jobs a b t vA vD vU vV R' hpos j.body (j.blk b vU)
      intro k rest s hk hs hS hX hsc hU hB
      have hkL := htok k hk
      have := hL.hU; have := hL.hb
      cases j with
      | CF => exact (exec_bodyCF vU k rest s hs hX hsc hU).mono (by omega)
      | E => exact (exec_bodyE b k rest s hs hS hX hsc hB).mono (by omega)
      | B => exact (exec_bodyB vU k rest s hs hS hX hsc hU).mono (by omega)
    refine key.mono ?_
    have := hL.ha
    have : a.length * (18 * L + 30 + 2) ≤ L * (18 * L + 32) := Nat.mul_le_mul_right _ hlen
    nlinarith

def script : List Ins → StackProg Key BSym
  | [] => skipP
  | i :: l => .seq i.prog (script l)

lemma exec_script (a : List ℕ) (b t vA vD vU vV L : ℕ) (hL : LenOK a b t vA vD vU vV L)
    (hpos : ∀ v ∈ a, 0 < v) : ∀ (l : List Ins) (R' : List BSym), (∀ i ∈ l, i.OK b t vA vD vU vV) →
    ExecLe (script l) (baseStore a b t vA vD vU vV R')
      (baseStore a b t vA vD vU vV ((encNats (l.flatMap (Ins.emit a b t vA vD vU vV))).reverse ++ R'))
      (l.length * (100 * (L + 3) ^ 2 + 1) + 1)
  | [], R', _ => by simpa [script, encNats] using exec_skip (baseStore a b t vA vD vU vV R')
  | i :: l, R', h => by
    have e1 := exec_ins a b t vA vD vU vV L R' hL hpos i (h i (by simp))
    have e2 := exec_script a b t vA vD vU vV L hL hpos l ((encNats (i.emit a b t vA vD vU vV)).reverse ++ R')
      (fun j hj => h j (by simp [hj]))
    refine ((e1.seq e2).congr ?_).mono (by simp; ring_nf; omega)
    simp [List.flatMap_cons, encNats_append]

/-! ## The common prefix of the output stages -/

def preO : StackProg Key BSym :=
  .seq (moveTok .inp .tmp) (.seq (popProg .inp) (.seq (tr1 .tmp .B) (.seq (copyProg .inp .W .sc)
    (.seq (countP .W .T) (.seq (copyProg .inp .W .sc) (.seq (sumLoop .W .A .tmp .car)
    (.seq (copyProg .A .X .sc) (.seq (copyProg .B .Y .sc) (subLoop .X .Y .tmp .car)))))))))

def subR (A b : ℕ) : List Bool × Bool := subB (Nat.bits A) (Nat.bits b) false

def P1 (a : List ℕ) (b : ℕ) : Store := fun k =>
  match k with
  | .inp => encNats a | .B => tokOf b | .T => List.replicate a.length .one | .A => tokOf a.sum
  | .tmp => (enc (subR a.sum b).1).reverse | .car => carS (subR a.sum b).2 | _ => []

lemma exec_preO (a : List ℕ) (b : ℕ) :
    ExecLe preO (initS (encNats (b :: a))) (P1 a b)
      (60 * ((encNats (b :: a)).length + 3) ^ 2) := by
  set L := (encNats (b :: a)).length
  have hw : encNats (b :: a) = tokOf b ++ .sep :: encNats a := encNats_cons b a
  have hLa : (encNats a).length ≤ L := by simp [L, hw]; omega
  have hLb : (tokOf b).length ≤ L := by simp [L, hw]
  have hLA : (tokOf a.sum).length ≤ L := le_trans (len_tokOf_le a.sum a le_rfl) hLa
  have e1 := exec_moveTok Key.inp Key.tmp (by decide) (tokOf b) (.sep :: encNats a)
    (initS (encNats (b :: a))) (by simp [initS, hw]) (tokOf_ne b) (tok_stop _)
  set s1 := Function.update (Function.update (initS (encNats (b :: a))) Key.inp
    (BSym.sep :: encNats a)) Key.tmp ((tokOf b).reverse ++ initS (encNats (b :: a)) Key.tmp)
  have e2 := exec_popE Key.inp s1
  set s2 := Function.update s1 Key.inp (s1 Key.inp).tail
  have e3 := exec_tr1 Key.tmp Key.B (by decide) s2
  set s3 := Function.update (Function.update s2 Key.tmp []) Key.B ((s2 Key.tmp).reverse ++ s2 Key.B)
  have e4 := exec_copyE Key.inp Key.W Key.sc (by decide) (by decide) (by decide) s3
    (by simp [s3, s2, s1, initS])
  set s4 := Function.update s3 Key.W (s3 Key.inp ++ s3 Key.W)
  have e5 := exec_countP Key.W Key.T (by decide) s4
  set s5 := Function.update (Function.update s4 Key.W []) Key.T
    (List.replicate ((s4 Key.W).count .sep) .one ++ s4 Key.T)
  have e6 := exec_copyE Key.inp Key.W Key.sc (by decide) (by decide) (by decide) s5
    (by simp [s5, s4, s3, s2, s1, initS])
  set s6 := Function.update s5 Key.W (s5 Key.inp ++ s5 Key.W)
  have e7 := exec_sumE Key.W Key.A Key.tmp Key.car (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a 0 s6 (by simp [s6, s5, s4, s3, s2, s1, initS])
    (by simp [s6, s5, s4, s3, s2, s1, initS, tokOf_zero]) (by simp [s6, s5, s4, s3, s2, s1, initS])
    (by simp [s6, s5, s4, s3, s2, s1, initS])
  set s7 := Function.update (Function.update s6 Key.W []) Key.A (tokOf (0 + a.sum))
  have e8 := exec_copyE Key.A Key.X Key.sc (by decide) (by decide) (by decide) s7
    (by simp [s7, s6, s5, s4, s3, s2, s1, initS])
  set s8 := Function.update s7 Key.X (s7 Key.A ++ s7 Key.X)
  have e9 := exec_copyE Key.B Key.Y Key.sc (by decide) (by decide) (by decide) s8
    (by simp [s8, s7, s6, s5, s4, s3, s2, s1, initS])
  set s9 := Function.update s8 Key.Y (s8 Key.B ++ s8 Key.Y)
  have e10 := ExecLe.of (exec_subLoop Key.X Key.Y Key.tmp Key.car (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) _ (Nat.bits a.sum) (Nat.bits b) false s9 le_rfl
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, initS, tokOf])
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, initS, tokOf])
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, initS, carS])) le_rfl
  have e := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq e10))))))))
  refine (e.congr ?_).mono ?_
  · funext j; cases j <;> simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, initS, P1, subR,
      count_sep_encNats, tokOf]
  · have hb2 : (Nat.bits b).length ≤ L := by simpa [tokOf, enc] using hLb
    have hA2 : (Nat.bits a.sum).length ≤ L := by simpa [tokOf, enc] using hLA
    simp [s8, s7, s6, s5, s4, s3, s2, s1, initS, tokOf, enc]
    simp [tokOf, enc] at hLb hLA
    have : (encNats a).length * (6 * (2 * (encNats a).length) + 13) ≤ L * (12 * L + 13) :=
      Nat.mul_le_mul hLa (by omega)
    have : max (Nat.bits a.sum).length (Nat.bits b).length ≤ L := max_le hA2 hb2
    nlinarith

/-! ## Emission lengths -/

lemma len_encNat (k : ℕ) : (encNat k).length = (tokOf k).length + 1 := by simp [encNat_eq]

lemma len_jobs (blk : ℕ → List ℕ) (C : ℕ)
    (hb : ∀ x, (encNats (blk x)).length ≤ 10 * (encNat x).length + C) :
    ∀ a : List ℕ, (encNats (a.map blk).flatten).length ≤ 10 * (encNats a).length + a.length * C
  | [] => by simp [encNats]
  | x :: a => by
    have h1 := hb x
    have h2 := len_jobs blk C hb a
    simp only [List.map_cons, List.flatten_cons, encNats_append, List.length_append]
    rw [show encNats (x :: a) = encNat x ++ encNats a by simp [encNats]]
    simp only [List.length_append, List.length_cons]; nlinarith

lemma len_emit (a : List ℕ) (b t vA vD vU vV L : ℕ) (hL : LenOK a b t vA vD vU vV L) (i : Ins)
    (hi : i.OK b t vA vD vU vV) : (encNats (i.emit a b t vA vD vU vV)).length ≤ 30 * (L + 3) ^ 2 := by
  have h9 : 9 ≤ (L + 3) ^ 2 := by
    have := Nat.pow_le_pow_left (show 3 ≤ L + 3 by omega) 2
    simpa using this
  have hsq : L + 3 ≤ (L + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
  cases i with
  | consts cs => have : (encNats cs).length ≤ 30 := hi; simp only [Ins.emit]; omega
  | num base α c dbl =>
    obtain ⟨h1, h2, h3⟩ := hi
    have hv0 := baseVal_len hL base h1
    have hc' : (if α then t else 0) + c ≤ L + 2 := by split_ifs <;> have := hL.ht <;> omega
    have hl := len_tokOf_add _ _ _ hv0 hc'
    simp only [Ins.emit]
    generalize baseVal b vA vD vU vV base + ((if α then t else 0) + c) = v0 at hl h3 ⊢
    cases dbl
    · simp [encNats, len_encNat]; omega
    · simp only [if_true]
      rw [show encNats [2 * v0] = encNat (2 * v0) by simp [encNats], len_encNat,
        tokOf_double (h3 rfl)]
      simp; omega
  | jobs j =>
    simp only [Ins.emit]
    have hc : ∀ x, (encNats (j.blk b vU x)).length ≤ 10 * (encNat x).length + (L + 10) := by
      intro x
      have := hL.hU; have := hL.hb
      cases j <;> simp [JK.blk, blkCF, blkE, blkB, encNats, len_encNat, tokOf_zero, tokOf_one] <;> omega
    have h1 := len_jobs (j.blk b vU) (L + 10) hc a
    have := hL.ha
    have hal : a.length ≤ L := le_trans (len_code_ge a) hL.ha
    have : a.length * (L + 10) ≤ L * (L + 10) := Nat.mul_le_mul_right _ hal
    nlinarith

lemma len_script (a : List ℕ) (b t vA vD vU vV L : ℕ) (hL : LenOK a b t vA vD vU vV L) :
    ∀ l : List Ins, (∀ i ∈ l, i.OK b t vA vD vU vV) →
      (encNats (l.flatMap (Ins.emit a b t vA vD vU vV))).length ≤ l.length * (30 * (L + 3) ^ 2)
  | [], _ => by simp [encNats]
  | i :: l, h => by
    have h1 := len_emit a b t vA vD vU vV L hL i (h i (by simp))
    have h2 := len_script a b t vA vD vU vV L hL l (fun j hj => h j (by simp [hj]))
    simp only [List.flatMap_cons, encNats_append, List.length_append, List.length_cons]
    nlinarith

/-! ## The output stage -/

lemma enc_rev_split (D : List Bool) : ∃ j, (enc D).reverse =
    List.replicate j BSym.zero ++ (enc (Nat.bits (bval D))).reverse := by
  obtain ⟨j, hj⟩ := exists_canon_split D
  refine ⟨j, ?_⟩
  conv_lhs => rw [hj]
  simp [enc, toB, List.map_replicate]

lemma head_rev_bits (D : ℕ) : ((enc (Nat.bits D)).reverse).head? ≠ some BSym.zero := by
  rcases Nat.eq_zero_or_pos D with h0 | hpos
  · subst h0; simp [enc]
  · obtain ⟨d, hd⟩ := tok_split D hpos
    rw [show enc (Nat.bits D) = tokOf D from rfl, hd]; simp

end OMK


set_option linter.all false
set_option autoImplicit false

namespace OMK
open CookPvsNP ProjSchedTW.Complexity

/-! ## The output stage -/

def uPhase : StackProg Key BSym :=
  .seq (copyProg .A .U .sc) (.seq (pushProg .C .one) (addOnes rO .U .tmp .car))

lemma exec_uPhase (a : List ℕ) (b t vA vD : ℕ) :
    ExecLe uPhase (baseStore a b t vA vD 0 0 []) (baseStore a b t vA vD (vA + 1) 0 [])
      (20 * (tokOf vA).length + 120) := by
  have e1 := exec_copyE Key.A Key.U Key.sc (by decide) (by decide) (by decide)
    (baseStore a b t vA vD 0 0 []) rfl
  set s1 := Function.update (baseStore a b t vA vD 0 0 []) Key.U
    (baseStore a b t vA vD 0 0 [] Key.A ++ baseStore a b t vA vD 0 0 [] Key.U)
  have e2 := exec_pushE Key.C BSym.one s1
  set s2 := Function.update s1 Key.C (BSym.one :: s1 Key.C)
  have e3 := exec_addOnes rO Key.U Key.tmp Key.car (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) 1 vA s2 (by simp [rO, s2, s1, baseStore])
    (by simp [rO, s2, s1, baseStore]) (by simp [rO, s2, s1, baseStore])
    (by simp [rO, s2, s1, baseStore]) (by simp [s2, s1, baseStore, tokOf_zero])
    (by simp [s2, s1, baseStore]) (by simp [s2, s1, baseStore])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · funext k; cases k <;> simp [s2, s1, rO, baseStore, tokOf_zero]
  · simp [baseStore, tokOf, enc]; omega

def trivCode : List ℕ := [1, 0, 1, 0, 0, 0]

def tailP (scr : List Ins) : StackProg Key BSym :=
  .branch (fun h => (h .car).isSome) skipP (.seq (stripZ .tmp)
    (.branch (fun h => (h .tmp).isSome)
      (.seq (tr1 .tmp .D) (.seq uPhase (.seq qPhase (.seq (script scr) (tr1 .R .out)))))
      (pushSeq .out (encNats trivCode).reverse)))

def outProg (scr : List Ins) : StackProg Key BSym := wrap (.seq preO (tailP scr))

/-- the values available to the scripts when `0 < b < A` -/
def qv (a : List ℕ) : ℕ := qvAux 0 a

lemma qv_le (a : List ℕ) : qv a ≤ a.sum ^ 2 := by
  have := qvAux_le 0 a; simp at this; exact this

lemma qv_bound (a : List ℕ) (b L : ℕ) (hA : a.sum < 2 ^ L) :
    a.sum - b + qv a < 2 ^ (2 * L + 2) := by
  have h1 := qv_le a
  have h2 : a.sum ^ 2 < (2 ^ L) ^ 2 := Nat.pow_lt_pow_left hA (by norm_num)
  have h3 : (2 : ℕ) ^ (2 * L + 2) = 4 * (2 ^ L) ^ 2 := by ring
  have h4 : a.sum ≤ a.sum ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

lemma exec_tail (scr : List Ins) (code : List ℕ → ℕ → ℕ → List ℕ)
    (hscr : ∀ (a : List ℕ) (b : ℕ), 0 < b → b < a.sum → (∀ v ∈ a, 0 < v) →
      (∀ i ∈ scr, i.OK b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a)) ∧
      scr.flatMap (Ins.emit a b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a)) =
        code a b a.length)
    (hlen : scr.length ≤ 10)
    (a : List ℕ) (b : ℕ) (hb : 0 < b) (hpos : ∀ v ∈ a, 0 < v) (L : ℕ)
    (hLa : (encNats a).length ≤ L) (hLb : (tokOf b).length ≤ L) :
    ∃ t : Store, ExecLe (tailP scr) (P1 a b) t (100000 * (L + 3) ^ 4) ∧
      t .out = (if b < a.sum then encNats (code a b a.length)
        else if b = a.sum then encNats trivCode else []) := by
  have hLA : (tokOf a.sum).length ≤ L := le_trans (len_tokOf_le a.sum a le_rfl) hLa
  have hX9 : 81 ≤ (L + 3) ^ 4 := by
    have := Nat.pow_le_pow_left (show 3 ≤ L + 3 by omega) 4; simpa using this
  have hXL : L + 3 ≤ (L + 3) ^ 4 := Nat.le_self_pow (by norm_num) _
  rcases Nat.lt_or_ge a.sum b with hlt | hge
  · -- borrow
    have hbor : (subR a.sum b).2 = true := by
      apply subB_borrow; rw [bval_bits, bval_bits]; exact hlt
    refine ⟨P1 a b, (ExecLe.brT (by simp [P1, hbor, carS]) (exec_skip _)).mono (by omega), ?_⟩
    simp [P1]; rw [if_neg (by omega), if_neg (by omega)]
  · obtain ⟨hnb, hval⟩ := subB_noborrow (Nat.bits a.sum) (Nat.bits b)
      (by rw [bval_bits, bval_bits]; exact hge)
    rw [bval_bits, bval_bits] at hval
    obtain ⟨j, hj⟩ := enc_rev_split (subR a.sum b).1
    rw [show bval (subR a.sum b).1 = a.sum - b from hval] at hj
    have hjL : j ≤ L := by
      have h1 := congrArg List.length hj
      simp only [List.length_reverse, List.length_append, List.length_replicate] at h1
      have h2 : (enc (subR a.sum b).1).length = max (Nat.bits a.sum).length (Nat.bits b).length := by
        simp [enc, subR, length_subB]
      simp [tokOf, enc] at hLA hLb
      omega
    have e1 := exec_stripZ Key.tmp j (enc (Nat.bits (a.sum - b))).reverse (P1 a b) (by simp [P1, hj])
      (head_rev_bits _)
    set s1 := Function.update (P1 a b) Key.tmp (enc (Nat.bits (a.sum - b))).reverse
    rcases Nat.eq_zero_or_pos (a.sum - b) with hz | hz
    · -- b = A
      have hbA : b = a.sum := by omega
      have e2 := exec_pushSeq Key.out (encNats trivCode).reverse s1
      refine ⟨_, (ExecLe.brF (by simp [P1, subR, hnb, carS])
        (e1.seq (ExecLe.brF (by simp [s1, hz, enc]) e2))).mono ?_, ?_⟩
      · simp [trivCode, encNats, encNat_eq, tokOf_zero, tokOf_one]; omega
      · simp [s1, P1]; rw [if_neg (by omega), if_pos hbA]
    · -- b < A
      have hbA : b < a.sum := by omega
      obtain ⟨hok, hem⟩ := hscr a b hb hbA hpos
      have e2 := exec_tr1 Key.tmp Key.D (by decide) s1
      have hbase : Function.update (Function.update s1 Key.tmp []) Key.D
          ((s1 Key.tmp).reverse ++ s1 Key.D) = baseStore a b a.length a.sum (a.sum - b) 0 0 [] := by
        funext k; cases k <;> simp [s1, P1, baseStore, hnb, subR, carS, tokOf, tokOf_zero, enc] <;>
          simp_all [subR]
      rw [hbase] at e2
      have hLD : (tokOf (a.sum - b)).length ≤ L := by
        refine le_trans ?_ hLA
        simp only [tokOf, enc, List.length_map]
        rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size (by omega)
      have hAp : a.sum < 2 ^ L := by
        have := sum_lt_pow a
        have : 2 ^ (encNats a).length ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hLa
        omega
      have eU := exec_uPhase a b a.length a.sum (a.sum - b)
      have eQ := exec_qPhase a (a.sum - b) (2 * L + 2)
        (baseStore a b a.length a.sum (a.sum - b) (a.sum + 1) 0 []) hpos rfl rfl
        (by simp [baseStore, tokOf_zero]) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (by simpa [qv] using qv_bound a b L hAp)
        (by
          have h1 : 2 ^ (encNats a).length ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hLa
          have h2 : a.sum * 2 ^ (encNats a).length < 2 ^ L * 2 ^ L :=
            Nat.mul_lt_mul_of_lt_of_le hAp h1 (by positivity)
          have h3 : (2 : ℕ) ^ (2 * L + 2) = 4 * (2 ^ L * 2 ^ L) := by ring
          omega)
      have hQs : Function.update (baseStore a b a.length a.sum (a.sum - b) (a.sum + 1) 0 []) Key.V
          (tokOf (a.sum - b + qvAux 0 a)) =
          baseStore a b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a) [] := by
        funext k; cases k <;> simp [baseStore, qv]
      rw [hQs] at eQ
      have hLU : (tokOf (a.sum + 1)).length ≤ 2 * L + 2 := bits_len_le (by
        have : 2 ^ L ≤ 2 ^ (2 * L + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ≤ 2 ^ (2 * L + 2) - 2 ^ L := by
          have h5 : (2 : ℕ) ^ (2 * L + 2) = 4 * 2 ^ (2 * L) := by ring
          have h6 : 2 ^ L ≤ 2 ^ (2 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h7 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
          omega
        omega)
      have hLV : (tokOf (a.sum - b + qv a)).length ≤ 2 * L + 2 := bits_len_le (qv_bound a b L hAp)
      have hLL : LenOK a b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a) (2 * L + 2) :=
        ⟨by omega, by omega, by omega, by omega, hLU, hLV,
          by have := le_trans (len_code_ge a) hLa; omega⟩
      have e3 := exec_script a b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a)
        (2 * L + 2) hLL hpos scr [] hok
      have e4 := exec_tr1 Key.R Key.out (by decide)
        (baseStore a b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a)
        ((encNats (scr.flatMap (Ins.emit a b a.length a.sum (a.sum - b) (a.sum + 1)
          (a.sum - b + qv a)))).reverse ++ []))
      have hR := len_script a b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a)
        (2 * L + 2) hLL scr hok
      refine ⟨_, (ExecLe.brF (by simp [P1, subR, hnb, carS])
        (e1.seq (ExecLe.brT (by
          simp only [s1, Function.update_self]
          have := head_rev_bits (a.sum - b)
          obtain ⟨d, hd⟩ := tok_split _ hz
          simp [show enc (Nat.bits (a.sum - b)) = tokOf (a.sum - b) from rfl, hd])
          (e2.seq (eU.seq (eQ.seq (e3.seq e4))))))).mono ?_, ?_⟩
      · simp only [baseStore, List.append_nil, List.length_reverse]
        have hw := hLA; have hx := hLD
        simp [s1, enc] at hLb ⊢
        simp [tokOf, enc] at hLD hLA
        have hal : a.length ≤ L := le_trans (len_code_ge a) hLa
        have hq3 : a.length * (60 * (2 * L + 2 + 2) ^ 3 + 2) ≤ 500 * (L + 3) ^ 4 := by
          have h1 : (2 * L + 2 + 2) ^ 3 ≤ 8 * (L + 3) ^ 3 := by
            have := Nat.pow_le_pow_left (show 2 * L + 2 + 2 ≤ 2 * (L + 3) by omega) 3
            calc (2 * L + 2 + 2) ^ 3 ≤ (2 * (L + 3)) ^ 3 := this
              _ = 8 * (L + 3) ^ 3 := by ring
          have h2 : 1 ≤ (L + 3) ^ 3 := Nat.one_le_pow _ _ (by omega)
          calc a.length * (60 * (2 * L + 2 + 2) ^ 3 + 2) ≤ (L + 3) * (500 * (L + 3) ^ 3) :=
                Nat.mul_le_mul (by omega) (by omega)
            _ = 500 * (L + 3) ^ 4 := by ring
        have hs2 : (2 * L + 2 + 3) ^ 2 ≤ 4 * (L + 3) ^ 4 := by
          have := Nat.pow_le_pow_left (show 2 * L + 2 + 3 ≤ 2 * (L + 3) by omega) 2
          have h3 : (L + 3) ^ 2 ≤ (L + 3) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          calc (2 * L + 2 + 3) ^ 2 ≤ (2 * (L + 3)) ^ 2 := this
            _ = 4 * (L + 3) ^ 2 := by ring
            _ ≤ 4 * (L + 3) ^ 4 := by omega
        have hsc1 : scr.length * (100 * (2 * L + 2 + 3) ^ 2 + 1) ≤ 10 * (400 * (L + 3) ^ 4 + 1) :=
          Nat.mul_le_mul hlen (by omega)
        have hsc2 : scr.length * (30 * (2 * L + 2 + 3) ^ 2) ≤ 10 * (120 * (L + 3) ^ 4) :=
          Nat.mul_le_mul hlen (by omega)
        omega
      · simp [baseStore, hem, hbA]

open Classical in
noncomputable def dec (w : List BSym) : Option (List ℕ) :=
  if h : ∃ l, PosCode w l then some h.choose else none

lemma dec_of {w : List BSym} {l : List ℕ} (h : PosCode w l) : dec w = some l := by
  have he : ∃ l, PosCode w l := ⟨l, h⟩
  rw [dec, dif_pos he]
  congr 1
  exact encNats_inj (he.choose_spec.2.2.symm.trans h.2.2)

lemma dec_none {w : List BSym} (h : ¬ ∃ l, PosCode w l) : dec w = none := by
  rw [dec, dif_neg h]


noncomputable def outSpec (code : List ℕ → ℕ → ℕ → List ℕ) (w : List BSym) : List BSym :=
  match dec w with
  | some (b :: a) => if b < a.sum then encNats (code a b a.length)
      else if b = a.sum then encNats trivCode else []
  | _ => []

lemma outSpec_none (code : List ℕ → ℕ → ℕ → List ℕ) {w : List BSym}
    (h : ¬ ∃ l, PosCode w l) : outSpec code w = [] := by
  rw [outSpec, dec_none h]

lemma outSpec_some (code : List ℕ → ℕ → ℕ → List ℕ) {w : List BSym} {a : List ℕ} {b : ℕ}
    (h : PosCode w (b :: a)) : outSpec code w = if b < a.sum then encNats (code a b a.length)
      else if b = a.sum then encNats trivCode else [] := by
  rw [outSpec, dec_of h]

lemma absorb4 (L : ℕ) : 200000 * (L + 3) ^ 4 ≤ L ^ 100000000 + 100000000 := by
  rcases Nat.lt_or_ge L 2 with h | h
  · interval_cases L <;> norm_num
  · have h1 : (L + 3) ^ 4 ≤ (3 * L) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 : (2 : ℕ) ^ 26 ≤ L ^ 26 := Nat.pow_le_pow_left h 26
    have h3 : L ^ 30 ≤ L ^ 100000000 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : (3 * L) ^ 4 = 81 * L ^ 4 := by ring
    have h5 : L ^ 30 = L ^ 4 * L ^ 26 := by ring
    have h6 : 200000 * (81 * L ^ 4) ≤ L ^ 4 * L ^ 26 := by
      have : 200000 * 81 ≤ L ^ 26 := le_trans (by norm_num) h2
      nlinarith [Nat.zero_le (L ^ 4)]
    omega

theorem out_poly (scr : List Ins) (code : List ℕ → ℕ → ℕ → List ℕ)
    (hscr : ∀ (a : List ℕ) (b : ℕ), 0 < b → b < a.sum → (∀ v ∈ a, 0 < v) →
      (∀ i ∈ scr, i.OK b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a)) ∧
      scr.flatMap (Ins.emit a b a.length a.sum (a.sum - b) (a.sum + 1) (a.sum - b + qv a)) =
        code a b a.length)
    (hlen : scr.length ≤ 10) :
    PolyTimeComputable (outSpec code) := by
  apply stack_program_polytime (outProg scr) Key.inp Key.out (outSpec code) 100000000
  intro w
  have hab := absorb4 w.length
  have hsq : w.length + 3 ≤ (w.length + 3) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hsq2 : (w.length + 3) ^ 2 ≤ (w.length + 3) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  by_cases hv : vrun w = (false, false, false)
  · obtain ⟨l, hl⟩ := (vrun_iff w).1 hv
    obtain ⟨b, a, rfl⟩ := List.exists_cons_of_ne_nil hl.1
    have hpa : ∀ v ∈ a, 0 < v := fun v hv => hl.2.1 v (by simp [hv])
    have hb : 0 < b := hl.2.1 b (by simp)
    have hw : w = tokOf b ++ .sep :: encNats a := by rw [hl.2.2, encNats_cons]
    have hLa : (encNats a).length ≤ w.length := by rw [hw]; simp; omega
    have hLb : (tokOf b).length ≤ w.length := by rw [hw]; simp
    obtain ⟨t, et, ht⟩ := exec_tail scr code hscr hlen a b hb hpa w.length hLa hLb
    have e0 := exec_preO a b
    rw [← hl.2.2] at e0
    obtain ⟨n, hn, e⟩ := exec_wrap_valid _ w t _ hv (e0.seq et)
    refine ⟨t, n, ?_, e, ?_⟩
    · omega
    · rw [ht, outSpec_some code hl]
  · obtain ⟨m', hm', e'⟩ := exec_wrap_invalid (.seq preO (tailP scr)) w hv
    refine ⟨valStore w, m', by omega, e', ?_⟩
    have hn : ¬ ∃ l, PosCode w l := fun h => hv ((vrun_iff w).2 h)
    simp [valStore, outSpec_none code hn]

end OMK


set_option linter.all false
set_option autoImplicit false

namespace OMK
open CookPvsNP ProjSchedTW.Complexity SchedComplexity.OneMachine Finset

/-! ## The quadratic sum agrees with the paper's double sum -/

lemma inner_eq {n : ℕ} (k : Fin n) (g : ℕ → ℕ) :
    ∑ j ∈ Iic k, g (j : ℕ) = ∑ j ∈ range ((k : ℕ) + 1), g j := by
  rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map]
  rfl

lemma sum_getD (l : List ℕ) : ∑ j ∈ range l.length, l.getD j 0 = l.sum := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [List.length_append, List.length_singleton, sum_range_succ, List.sum_append]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [List.getD_append _ _ _ _ (by simpa using hj)])]
    simpa using ih

lemma qv_eq (a : List ℕ) :
    qvAux 0 a = ∑ k ∈ range a.length, ∑ j ∈ range (k + 1), a.getD j 0 * a.getD k 0 := by
  induction a using List.reverseRecOn with
  | nil => simp [qvAux]
  | append_singleton l x ih =>
    rw [qvAux_append, ih, List.length_append, List.length_singleton, sum_range_succ]
    have h1 : ∀ k ∈ range l.length, ∑ j ∈ range (k + 1), (l ++ [x]).getD j 0 * (l ++ [x]).getD k 0
        = ∑ j ∈ range (k + 1), l.getD j 0 * l.getD k 0 := by
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      simp at hk hj
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hk]
    rw [Finset.sum_congr rfl h1, sum_range_succ]
    have h2 : ∑ j ∈ range l.length, (l ++ [x]).getD j 0 * (l ++ [x]).getD l.length 0 =
        l.sum * x := by
      rw [← sum_getD l, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj; simp at hj
      rw [List.getD_append _ _ _ _ hj]; simp
    rw [h2]
    simp [qvAux]; ring

lemma dsum (a : List ℕ) :
    (∑ k : Fin a.length, ∑ j ∈ Iic k, a.get j * a.get k) = qv a := by
  rw [qv, qv_eq]
  have : ∀ k : Fin a.length, ∑ j ∈ Iic k, a.get j * a.get k =
      ∑ j ∈ range ((k : ℕ) + 1), a.getD j 0 * a.getD k 0 := by
    intro k
    rw [← inner_eq k (fun j => a.getD j 0 * a.getD k 0)]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  rw [Finset.sum_congr rfl (fun k _ => this k)]
  exact Fin.sum_univ_eq_sum_range (fun k => ∑ j ∈ range (k + 1), a.getD j 0 * a.getD k 0) a.length

lemma yB_eq (a : List ℕ) (b : ℕ) (h : b ≤ a.sum) : yB a b = a.sum - b + qv a := by
  rw [yB, dsum]; omega

/-! ## Instance codes -/

lemma flatten_inj_len {α : Type} (n : ℕ) : ∀ (l l' : List (List α)), (∀ r ∈ l, r.length = n) →
    (∀ r ∈ l', r.length = n) → l.length = l'.length → l.flatten = l'.flatten → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | r :: l, r' :: l', h1, h2, hl, h => by
    simp only [List.flatten_cons] at h
    obtain ⟨e1, e2⟩ := List.append_inj h (by rw [h1 r (by simp), h2 r' (by simp)])
    rw [e1, flatten_inj_len n l l' (fun x hx => h1 x (by simp [hx]))
      (fun x hx => h2 x (by simp [hx])) (by simpa using hl) e2]

lemma ofFn_get_map (a : List ℕ) (g : ℕ → List ℕ) :
    List.ofFn (fun i : Fin a.length => g (a.get i)) = a.map g := by
  have : (fun i : Fin a.length => g (a.get i)) = g ∘ a.get := rfl
  rw [this, ← List.map_ofFn, List.ofFn_get]

lemma codeList_inj (I I' : Instance) (y y' : ℕ) (h : I.codeList y = I'.codeList y') :
    I = I' ∧ y = y' := by
  obtain ⟨n, p, w, r, d⟩ := I
  obtain ⟨n', p', w', r', d'⟩ := I'
  simp only [Instance.codeList, List.cons.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have hl : ∀ (f : Fin n → List ℕ), (List.ofFn f).flatten.length = (List.ofFn f).flatten.length := fun _ => rfl
  have h4 : ∀ (P W R D : Fin n → ℕ), ∀ r ∈ List.ofFn (fun j => [P j, W j, R j, D j]), r.length = 4 := by
    intro P W R D r hr
    simp only [List.mem_ofFn] at hr
    obtain ⟨j, rfl⟩ := hr; rfl
  have hlen : ((List.ofFn fun j => [p j, w j, r j, d j]).flatten).length =
      ((List.ofFn fun j => [p' j, w' j, r' j, d' j]).flatten).length := by
    rw [List.length_flatten, List.length_flatten]; simp [Function.comp_def]
  obtain ⟨e1, e2⟩ := List.append_inj h hlen
  have e3 := flatten_inj_len 4 _ _ (h4 p w r d) (h4 p' w' r' d') (by simp) e1
  rw [List.ofFn_inj] at e3
  simp only [List.cons.injEq] at e2
  refine ⟨?_, e2.1⟩
  have hp : p = p' := funext fun j => by have := congrFun e3 j; simp at this; exact this.1
  have hw : w = w' := funext fun j => by have := congrFun e3 j; simp at this; exact this.2.1
  have hr : r = r' := funext fun j => by have := congrFun e3 j; simp at this; exact this.2.2.1
  have hd : d = d' := funext fun j => by have := congrFun e3 j; simp at this; exact this.2.2.2
  subst hp hw hr hd; rfl

lemma code_ne_nil (I : Instance) (y : ℕ) : encNats (I.codeList y) ≠ [] :=
  encNats_ne_nil (by simp [Instance.codeList])

lemma mem_code {Lg : Set (List BSym)} {Pr : Instance → ℕ → Prop}
    (hLg : ∀ x, x ∈ Lg ↔ ∃ (I : Instance) (y : ℕ), x = encNats (I.codeList y) ∧ Pr I y)
    (I : Instance) (y : ℕ) : encNats (I.codeList y) ∈ Lg ↔ Pr I y := by
  rw [hLg]
  constructor
  · rintro ⟨I', y', h, hp⟩
    obtain ⟨rfl, rfl⟩ := codeList_inj _ _ _ _ (encNats_inj h)
    exact hp
  · intro hp; exact ⟨I, y, rfl, hp⟩

lemma nil_not_mem {Lg : Set (List BSym)} {Pr : Instance → ℕ → Prop}
    (hLg : ∀ x, x ∈ Lg ↔ ∃ (I : Instance) (y : ℕ), x = encNats (I.codeList y) ∧ Pr I y) :
    ([] : List BSym) ∉ Lg := by
  rw [hLg]; rintro ⟨I, y, h, -⟩; exact code_ne_nil I y h.symm

/-- the trivial yes-instance: one job with `p = 0`, `w = 1`, `r = d = 0`, threshold `0` -/
def trivI : Instance := ⟨1, fun _ => 0, fun _ => 1, fun _ => 0, fun _ => 0⟩

lemma trivI_code : trivI.codeList 0 = trivCode := by
  simp [trivI, Instance.codeList, trivCode]

lemma trivI_feas : trivI.IsFeasible (fun _ => 0) := by
  refine ⟨fun j => by simp [trivI], fun j k hjk => absurd (Subsingleton.elim (α := Fin 1) j k) hjk⟩

lemma ofFn_flatten_succ {t : ℕ} (f : Fin (t + 1) → List ℕ) :
    (List.ofFn f).flatten = (List.ofFn fun i : Fin t => f i.castSucc).flatten ++ f (Fin.last t) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]; simp

/-! ### the three output codes -/

def codeCF (a : List ℕ) (b t : ℕ) : List ℕ :=
  (t + 1) :: ((a.map (blkCF (a.sum + 1))).flatten ++ [1, 1, b, b + 1, 0])

def codeE (a : List ℕ) (b t : ℕ) : List ℕ :=
  t :: ((a.map (blkE b)).flatten ++ [a.sum - b])

def codeB (a : List ℕ) (b t : ℕ) : List ℕ :=
  (t + 1) :: ((a.map (blkB (a.sum + 1))).flatten ++ [1, 0, 0, b + 1, a.sum - b + qv a])

lemma codeCF_eq (a : List ℕ) (b : ℕ) : (instCF a b).codeList 0 = codeCF a b a.length := by
  have hj : (List.ofFn fun j : Fin (instCF a b).n => [(instCF a b).p j, (instCF a b).w j,
      (instCF a b).r j, (instCF a b).d j]).flatten
      = (a.map (blkCF (a.sum + 1))).flatten ++ [1, 1, b, b + 1] := by
    change (List.ofFn fun j : Fin (a.length + 1) => _).flatten = _
    rw [ofFn_flatten_succ, ← ofFn_get_map]
    congr 1
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)); simp [instCF, blkCF]
    · simp [instCF]
  simp only [Instance.codeList]
  rw [hj]; simp [codeCF, instCF]

lemma codeE_eq (a : List ℕ) (b : ℕ) : (instE a b).codeList (yE a b) = codeE a b a.length := by
  have hj : (List.ofFn fun j : Fin (instE a b).n => [(instE a b).p j, (instE a b).w j,
      (instE a b).r j, (instE a b).d j]).flatten = (a.map (blkE b)).flatten := by
    change (List.ofFn fun j : Fin a.length => _).flatten = _
    rw [← ofFn_get_map]; rfl
  simp only [Instance.codeList]
  rw [hj]; simp [codeE, instE, yE]

lemma codeB_eq (a : List ℕ) (b : ℕ) (hb : b ≤ a.sum) :
    (instB a b).codeList (yB a b) = codeB a b a.length := by
  have hj : (List.ofFn fun j : Fin (instB a b).n => [(instB a b).p j, (instB a b).w j,
      (instB a b).r j, (instB a b).d j]).flatten
      = (a.map (blkB (a.sum + 1))).flatten ++ [1, 0, 0, b + 1] := by
    change (List.ofFn fun j : Fin (a.length + 1) => _).flatten = _
    rw [ofFn_flatten_succ, ← ofFn_get_map]
    congr 1
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)); simp [instB, blkB]
    · simp [instB]
  simp only [Instance.codeList]
  rw [hj, yB_eq a b hb]; simp [codeB, instB]

/-! ### class membership of the constructed instances -/

lemma lastCases_lt {t : ℕ} (x : ℕ) (f : Fin t → ℕ) (j : Fin (t + 1)) (hj : (j : ℕ) + 1 < t + 1) :
    (Fin.lastCases x f j : ℕ) = f ⟨j, by omega⟩ := by
  obtain ⟨j', rfl⟩ : ∃ j' : Fin t, j = j'.castSucc := ⟨⟨j, by omega⟩, rfl⟩
  simp

lemma instCF_only (a : List ℕ) (b : ℕ) : (instCF a b).OnlyLastReleased :=
  ⟨by simp [instCF], fun j hj => by
    simp only [instCF] at hj ⊢; rw [lastCases_lt b _ j hj]⟩

lemma instCF_unit (a : List ℕ) (b : ℕ) : (instCF a b).UnitWeights := fun _ => rfl

/-! ### generic correctness of an output stage -/

lemma out_correct (Lg : Set (List BSym)) (code : List ℕ → ℕ → ℕ → List ℕ)
    (hT : encNats trivCode ∈ Lg) (hnil : ([] : List BSym) ∉ Lg) (P : List ℕ → ℕ → Prop)
    (hP : ∀ a b, (∀ v ∈ a, 0 < v) → 0 < b → b < a.sum → (encNats (code a b a.length) ∈ Lg ↔ P a b))
    (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧ P a b ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec code x ∈ Lg := by
  by_cases hx : ∃ l, PosCode x l
  · obtain ⟨l, hl⟩ := hx
    obtain ⟨b, a, rfl⟩ := List.exists_cons_of_ne_nil hl.1
    have hpa : ∀ v ∈ a, 0 < v := fun v hv => hl.2.1 v (by simp [hv])
    have hb : 0 < b := hl.2.1 b (by simp)
    have uniq : ∀ (a' : List ℕ) (b' : ℕ), x = encNats (b' :: a') → a' = a ∧ b' = b := by
      intro a' b' h; have := encNats_inj (h.symm.trans hl.2.2); simp at this; exact ⟨this.2, this.1⟩
    rw [outSpec_some code hl]
    rcases lt_trichotomy b a.sum with hlt | heq | hgt
    · rw [if_pos hlt, hP a b hpa hb hlt]
      constructor
      · rintro (⟨a', b', -, -, -, hp, hx'⟩ | ⟨a', b', -, -, he, hx'⟩)
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; exact hp
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
      · intro hp; exact Or.inl ⟨a, b, hpa, hb, hlt, hp, hl.2.2⟩
    · rw [if_neg (by omega), if_pos heq]
      exact iff_of_true (Or.inr ⟨a, b, hpa, hb, heq, hl.2.2⟩) hT
    · rw [if_neg (by omega), if_neg (by omega)]
      refine iff_of_false ?_ hnil
      rintro (⟨a', b', -, -, h1, -, hx'⟩ | ⟨a', b', -, -, h1, hx'⟩)
      · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
      · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
  · rw [outSpec_none code hx]
    refine iff_of_false ?_ hnil
    rintro (⟨a', b', h1, h2, -, -, hx'⟩ | ⟨a', b', h1, h2, -, hx'⟩)
    · exact hx ⟨b' :: a', by simp, by simpa using ⟨h2, h1⟩, hx'⟩
    · exact hx ⟨b' :: a', by simp, by simpa using ⟨h2, h1⟩, hx'⟩

/-! ### the four languages -/

lemma triv_mem_C : encNats trivCode ∈ langRnLmax := by
  rw [← trivI_code]
  exact ⟨trivI, 0, rfl, ⟨by simp [trivI], fun j hj => by simp [trivI] at hj⟩, fun _ => 0,
    trivI_feas, fun j => by simp [trivI, Instance.lateness, Instance.C]⟩

lemma triv_mem_F : encNats trivCode ∈ langRnUnitSumWU := by
  rw [← trivI_code]
  exact ⟨trivI, 0, rfl, ⟨by simp [trivI], fun j hj => by simp [trivI] at hj⟩, fun _ => rfl,
    fun _ => 0, trivI_feas, by simp [trivI, Instance.sumWU, Instance.U, Instance.C]⟩

lemma triv_mem_E : encNats trivCode ∈ langSumWU := by
  rw [← trivI_code]
  exact ⟨trivI, 0, rfl, by simp [trivI], fun _ => rfl,
    fun _ => 0, trivI_feas, by simp [trivI, Instance.sumWU, Instance.U, Instance.C]⟩

lemma triv_mem_B : encNats trivCode ∈ langLmaxSumWC := by
  rw [← trivI_code]
  exact ⟨trivI, 0, rfl, by simp [trivI], fun _ => rfl,
    fun _ => 0, trivI_feas, fun j => by simp [trivI, Instance.C],
    by simp [trivI, Instance.sumWC, Instance.C]⟩

/-! ### correctness of the four output stages -/

theorem correctC (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (∃ B, (instCF a b).IsFeasible B ∧ ∀ j, (instCF a b).lateness B j ≤ 0) ∧
        x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeCF x ∈ langRnLmax :=
  out_correct langRnLmax codeCF triv_mem_C (nil_not_mem (fun _ => Iff.rfl)) _ (fun a b _ _ _ => by
    rw [← codeCF_eq, mem_code (Lg := langRnLmax)
      (Pr := fun I y => I.OnlyLastReleased ∧ ∃ B, I.IsFeasible B ∧ ∀ j, I.lateness B j ≤ (y : ℤ))
      (fun _ => Iff.rfl)]
    simp [instCF_only]) x

theorem correctF (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (∃ B, (instCF a b).IsFeasible B ∧ (instCF a b).sumWU B ≤ 0) ∧
        x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeCF x ∈ langRnUnitSumWU :=
  out_correct langRnUnitSumWU codeCF triv_mem_F (nil_not_mem (fun _ => Iff.rfl)) _
    (fun a b _ _ _ => by
      rw [← codeCF_eq, mem_code (Lg := langRnUnitSumWU)
        (Pr := fun I y => I.OnlyLastReleased ∧ I.UnitWeights ∧ ∃ B, I.IsFeasible B ∧ I.sumWU B ≤ y)
        (fun _ => Iff.rfl)]
      simp [instCF_only, instCF_unit]) x

theorem correctE (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (∃ B, (instE a b).IsFeasible B ∧ (instE a b).sumWU B ≤ yE a b) ∧
        x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeE x ∈ langSumWU :=
  out_correct langSumWU codeE triv_mem_E (nil_not_mem (fun _ => Iff.rfl)) _
    (fun a b _ hb hlt => by
      rw [← codeE_eq, mem_code (Lg := langSumWU)
        (Pr := fun I y => 0 < I.n ∧ I.AllReleasedAtZero ∧ ∃ B, I.IsFeasible B ∧ I.sumWU B ≤ y)
        (fun _ => Iff.rfl)]
      have hn : 0 < a.length := by
        rcases a with _ | ⟨x, a⟩
        · simp at hlt
        · simp
      have hr : (instE a b).AllReleasedAtZero := fun _ => rfl
      simp only [hr, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩) x

theorem correctB (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (∃ B, (instB a b).IsFeasible B ∧ (∀ j, (instB a b).C B j ≤ (instB a b).d j) ∧
          (instB a b).sumWC B ≤ yB a b) ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeB x ∈ langLmaxSumWC :=
  out_correct langLmaxSumWC codeB triv_mem_B (nil_not_mem (fun _ => Iff.rfl)) _
    (fun a b _ hb hlt => by
      rw [← codeB_eq a b hlt.le, mem_code (Lg := langLmaxSumWC)
        (Pr := fun I y => 0 < I.n ∧ I.AllReleasedAtZero ∧
          ∃ B, I.IsFeasible B ∧ (∀ j, I.C B j ≤ I.d j) ∧ I.sumWC B ≤ y)
        (fun _ => Iff.rfl)]
      have hn : 0 < (instB a b).n := by simp [instB]
      have hr : (instB a b).AllReleasedAtZero := fun _ => rfl
      simp only [hn, hr, true_and]) x

/-! ### polynomial time -/

def scriptCF : List Ins :=
  [.num none true 1 false, .jobs .CF, .consts [1, 1], .num (some .B) false 0 false,
    .num (some .B) false 1 false, .consts [0]]

def scriptE : List Ins :=
  [.num none true 0 false, .jobs .E, .num (some .D) false 0 false]

def scriptB : List Ins :=
  [.num none true 1 false, .jobs .B, .consts [1, 0, 0], .num (some .B) false 1 false,
    .num (some .V) false 0 false]

lemma polyCF : PolyTimeComputable (outSpec codeCF) := by
  apply out_poly scriptCF codeCF _ (by decide)
  intro a b hb hbA hpos
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [scriptCF, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Ins.OK, BaseOK, encNats, encNat_eq, tokOf_zero, tokOf_one]
  · simp [scriptCF, Ins.emit, baseVal, JK.blk, codeCF]

lemma polyE : PolyTimeComputable (outSpec codeE) := by
  apply out_poly scriptE codeE _ (by decide)
  intro a b hb hbA hpos
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [scriptE, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [Ins.OK, BaseOK]
  · simp [scriptE, Ins.emit, baseVal, JK.blk, codeE]

lemma polyB : PolyTimeComputable (outSpec codeB) := by
  apply out_poly scriptB codeB _ (by decide)
  intro a b hb hbA hpos
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [scriptB, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      simp [Ins.OK, BaseOK, encNats, encNat_eq, tokOf_zero, tokOf_one]
  · simp [scriptB, Ins.emit, baseVal, JK.blk, codeB]

end OMK

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.OneMachine in
theorem solution :
    (∃ fB : List BSym → List BSym, PolyTimeComputable fB ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instB a b).IsFeasible B ∧ (∀ j, (instB a b).C B j ≤ (instB a b).d j) ∧
              (instB a b).sumWC B ≤ yB a b) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fB x ∈ langLmaxSumWC) ∧
    (∃ fC : List BSym → List BSym, PolyTimeComputable fC ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instCF a b).IsFeasible B ∧ ∀ j, (instCF a b).lateness B j ≤ 0) ∧
            x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fC x ∈ langRnLmax) ∧
    (∃ fE : List BSym → List BSym, PolyTimeComputable fE ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instE a b).IsFeasible B ∧ (instE a b).sumWU B ≤ yE a b) ∧
            x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fE x ∈ langSumWU) ∧
    (∃ fF : List BSym → List BSym, PolyTimeComputable fF ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instCF a b).IsFeasible B ∧ (instCF a b).sumWU B ≤ 0) ∧
            x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fF x ∈ langRnUnitSumWU) :=
  ⟨⟨OMK.outSpec OMK.codeB, OMK.polyB, OMK.correctB⟩,
    ⟨OMK.outSpec OMK.codeCF, OMK.polyCF, OMK.correctC⟩,
    ⟨OMK.outSpec OMK.codeE, OMK.polyE, OMK.correctE⟩,
    ⟨OMK.outSpec OMK.codeCF, OMK.polyCF, OMK.correctF⟩⟩

