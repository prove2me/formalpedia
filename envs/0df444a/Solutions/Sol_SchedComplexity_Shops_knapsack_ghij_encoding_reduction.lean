-- Prove2me | solution 1 for SchedComplexity.Shops.knapsack_ghij_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:16:27.03835+00:00
-- url     : https://prove2.me/submissions/e05f0600-1c6d-4b95-b6e4-d7d229f9bdd2

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Problems
import Definitions.Def_SchedComplexity_Shops_Constructions
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option linter.all false



set_option autoImplicit false

namespace GHIK

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

end GHIK


set_option autoImplicit false

namespace GHIK
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

end GHIK


set_option autoImplicit false

namespace GHIK
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

end GHIK


set_option autoImplicit false

namespace GHIK
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

end GHIK




set_option autoImplicit false

namespace GHIK
open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Shops

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

/-! ## Shop codes -/

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

def pairEnc (ops : List (ℕ × ℕ)) : List ℕ := (ops.map fun e => [e.1, e.2]).flatten

lemma pairEnc_len (ops : List (ℕ × ℕ)) : (pairEnc ops).length = 2 * ops.length := by
  induction ops with
  | nil => rfl
  | cons e ops ih => simp [pairEnc] at ih ⊢; omega

lemma pairEnc_inj : ∀ (o o' : List (ℕ × ℕ)), pairEnc o = pairEnc o' → o = o'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [pairEnc] at h
  | _ :: _, [], h => by simp [pairEnc] at h
  | e :: o, e' :: o', h => by
    simp only [pairEnc, List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [pairEnc_inj o o' h3, Prod.ext h1 h2]

def blkEnc (b : ℕ × List (ℕ × ℕ)) : List ℕ := [b.1, b.2.length] ++ pairEnc b.2

lemma blocks_inj : ∀ (bs bs' : List (ℕ × List (ℕ × ℕ))) (R R' : List ℕ), bs.length = bs'.length →
    (bs.map blkEnc).flatten ++ R = (bs'.map blkEnc).flatten ++ R' → bs = bs' ∧ R = R'
  | [], [], _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | b :: bs, b' :: bs', R, R', hl, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, blkEnc, List.cons_append,
      List.nil_append, List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨e1, e2⟩ := List.append_inj h3 (by rw [pairEnc_len, pairEnc_len, h2])
    obtain ⟨e3, e4⟩ := blocks_inj bs bs' R R' (by simpa using hl) e2
    refine ⟨?_, e4⟩
    rw [e3, Prod.ext h1 (pairEnc_inj _ _ e1)]

namespace ShopCode
variable {n m : ℕ}

def blocks (I : ShopInstance n m) : List (ℕ × List (ℕ × ℕ)) :=
  List.ofFn fun j => (I.release j, (I.ops j).map fun e => (e.1.val, e.2))

def mat (I : ShopInstance n m) : List (List ℕ) :=
  List.ofFn fun j : Fin n => List.ofFn fun k : Fin n => if (j, k) ∈ I.prec then 1 else 0

lemma code_eq (I : ShopInstance n m) (y : ℕ) :
    I.code y = [n, m] ++ ((blocks I).map blkEnc).flatten ++ (mat I).flatten ++ [y] := by
  simp only [ShopInstance.code, blocks, mat, List.map_ofFn]
  congr 3
  congr 1; apply congrArg List.ofFn; funext j
  simp [blkEnc, pairEnc, Function.comp_def]

lemma code_inj (I I' : ShopInstance n m) (y y' : ℕ) (h : I.code y = I'.code y') :
    I = I' ∧ y = y' := by
  rw [code_eq, code_eq] at h
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq,
    true_and] at h
  obtain ⟨hb, hR⟩ := blocks_inj _ _ _ _ (by simp [blocks]) h
  obtain ⟨hm, hy⟩ := List.append_inj hR (by
    rw [List.length_flatten, List.length_flatten]; simp [mat, Function.comp_def])
  simp only [List.cons.injEq, and_true] at hy
  have hm' := flatten_inj_len n _ _ (by simp [mat]) (by simp [mat]) (by simp [mat]) hm
  refine ⟨?_, hy⟩
  obtain ⟨ops, rel, prec⟩ := I
  obtain ⟨ops', rel', prec'⟩ := I'
  simp only [blocks, List.ofFn_inj, funext_iff, Prod.mk.injEq] at hb
  simp only [mat, List.ofFn_inj, funext_iff] at hm'
  have hops : ops = ops' := by
    funext j
    exact List.map_injective_iff.2 (fun e e' he => by
      simp only [Prod.mk.injEq] at he; exact Prod.ext (Fin.ext he.1) he.2) (hb j).2
  have hrel : rel = rel' := funext fun j => (hb j).1
  have hprec : prec = prec' := by
    ext ⟨j, k⟩
    have := hm' j k
    by_cases h1 : (j, k) ∈ prec <;> by_cases h2 : (j, k) ∈ prec' <;> simp_all
  subst hops hrel hprec; rfl

lemma code_ne_nil (I : ShopInstance n m) (y : ℕ) : encNats (I.code y) ≠ [] :=
  encNats_ne_nil (by simp [ShopInstance.code])

lemma code_head (I : ShopInstance n m) (y : ℕ) : (I.code y).head? = some n := by
  simp [ShopInstance.code]

end ShopCode

lemma mem_shopLang {m : ℕ} {C : ∀ {n : ℕ}, ShopInstance n m → Prop} {n : ℕ}
    (I : ShopInstance n m) (y : ℕ) (hC : C I) :
    encNats (I.code y) ∈ shopLang m C ↔ I.HasScheduleLE y := by
  constructor
  · rintro ⟨n', I', y', -, hs, he⟩
    have hc := encNats_inj he
    have hn : n = n' := by
      have := congrArg List.head? hc
      rw [ShopCode.code_head, ShopCode.code_head] at this; simpa using this
    subst hn
    obtain ⟨rfl, rfl⟩ := ShopCode.code_inj _ _ _ _ hc
    exact hs
  · intro hs; exact ⟨n, I, y, hC, hs, rfl⟩

lemma nil_not_mem {m : ℕ} {C : ∀ {n : ℕ}, ShopInstance n m → Prop} : ([] : List BSym) ∉ shopLang m C := by
  rintro ⟨n, I, y, -, -, he⟩
  exact ShopCode.code_ne_nil I y he.symm

/-- the trivial instance without jobs -/
def emptyInst (m : ℕ) : ShopInstance 0 m := ⟨Fin.elim0, Fin.elim0, ∅⟩

lemma emptyInst_code (m : ℕ) : (emptyInst m).code 0 = [0, m, 0] := by
  simp [ShopInstance.code, emptyInst]

lemma emptyInst_sched (m : ℕ) : (emptyInst m).HasScheduleLE 0 :=
  ⟨fun o => o.1.elim0, ⟨fun o => o.1.elim0, fun j => j.elim0, fun o => o.1.elim0,
    fun j => j.elim0⟩, fun j => j.elim0⟩

lemma empty_mem {m : ℕ} {C : ∀ {n : ℕ}, ShopInstance n m → Prop} (hC : C (emptyInst m)) :
    encNats [0, m, 0] ∈ shopLang m C := by
  rw [← emptyInst_code]; exact (mem_shopLang _ _ hC).2 (emptyInst_sched m)

/-! ## The four constructions as code lists -/

def blkG (x : ℕ) : List ℕ := [0, 2, 0, x, 1, 1]
def blkI (x : ℕ) : List ℕ := [0, 1, 0, x]
def blkJ (x : ℕ) : List ℕ := [0, 2, 0, x, 2, x]

def codeG (a : List ℕ) (b t : ℕ) : List ℕ :=
  [t + 1, 2] ++ (a.map blkG).flatten ++ [b, 2, 0, 1, 1, a.sum - b] ++
    List.replicate ((t + 1) * (t + 1)) 0 ++ [a.sum + t]

def codeH (a : List ℕ) (b t : ℕ) : List ℕ :=
  [t + 2, 2] ++ (a.map blkG).flatten ++ [0, 2, 0, 1, 1, b] ++ [0, 2, 0, 1, 1, a.sum - b] ++
    (List.replicate (t * (t + 2)) 0 ++ List.replicate (t + 1) 0 ++ [1] ++ List.replicate (t + 2) 0)
    ++ [a.sum + t + 1]

def codeI (a : List ℕ) (b t : ℕ) : List ℕ :=
  [t + 1, 2] ++ (a.map blkI).flatten ++ [0, 3, 1, b, 0, 1, 1, a.sum - b] ++
    List.replicate ((t + 1) * (t + 1)) 0 ++ [a.sum + 1]

def codeJ (a : List ℕ) (b t : ℕ) : List ℕ :=
  [t + 2, 3] ++ (a.map blkJ).flatten ++ [0, 2, 0, b, 1, 2 * (a.sum - b)] ++
    [0, 2, 1, 2 * b, 2, a.sum - b] ++ List.replicate ((t + 2) * (t + 2)) 0 ++ [2 * a.sum]

lemma ofFn_get_map (a : List ℕ) (g : ℕ → List ℕ) :
    List.ofFn (fun i : Fin a.length => g (a.get ⟨i.val, i.isLt⟩)) = a.map g := by
  have : (fun i : Fin a.length => g (a.get ⟨i.val, i.isLt⟩)) = g ∘ a.get := rfl
  rw [this, ← List.map_ofFn, List.ofFn_get]

lemma flatten_rep_zero (n k : ℕ) :
    (List.replicate n (List.replicate k (0 : ℕ))).flatten = List.replicate (n * k) 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm,
      List.replicate_add]

lemma mat_empty (n : ℕ) :
    (List.ofFn fun j : Fin n => List.ofFn fun k : Fin n =>
      if (j, k) ∈ (∅ : Finset (Fin n × Fin n)) then 1 else 0).flatten = List.replicate (n * n) 0 := by
  simp [List.ofFn_const, flatten_rep_zero]

lemma ofFn_flatten_succ {t : ℕ} (f : Fin (t + 1) → List ℕ) :
    (List.ofFn f).flatten = (List.ofFn fun i : Fin t => f i.castSucc).flatten ++ f (Fin.last t) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]; simp

lemma codeI_eq (a : List ℕ) (b : ℕ) : (constrI a b).code (yI a) = codeI a b a.length := by
  have hj : (List.ofFn fun j : Fin (a.length + 1) => [(constrI a b).release j,
      ((constrI a b).ops j).length] ++ (((constrI a b).ops j).map fun e => [e.1.val, e.2]).flatten).flatten
      = (a.map blkI).flatten ++ [0, 3, 1, b, 0, 1, 1, a.sum - b] := by
    rw [ofFn_flatten_succ, ← ofFn_get_map]
    congr 1
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)); simp [constrI, blkI]
    · simp [constrI]
  have hm : (List.ofFn fun j : Fin (a.length + 1) => List.ofFn fun k : Fin (a.length + 1) =>
      if (j, k) ∈ (constrI a b).prec then 1 else 0).flatten =
      List.replicate ((a.length + 1) * (a.length + 1)) 0 := mat_empty _
  rw [ShopInstance.code, hj, hm, codeI, yI]; simp

lemma sum_map_mul (t : ℕ) (a : List ℕ) : (a.map (t * ·)).sum = t * a.sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, Nat.mul_add]

lemma codeG_eq (a : List ℕ) (b : ℕ) :
    (constrG a b).code (yG a) = codeG (a.map (a.length * ·)) (a.length * b) a.length := by
  have hj : (List.ofFn fun j : Fin (a.length + 1) => [(constrG a b).release j,
      ((constrG a b).ops j).length] ++ (((constrG a b).ops j).map fun e => [e.1.val, e.2]).flatten).flatten
      = ((a.map (a.length * ·)).map blkG).flatten ++
        [a.length * b, 2, 0, 1, 1, (a.map (a.length * ·)).sum - a.length * b] := by
    rw [ofFn_flatten_succ, List.map_map, ← ofFn_get_map]
    congr 1
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)); simp [constrG, blkG]
    · simp [constrG, sum_map_mul, Nat.mul_sub]
  have hm : (List.ofFn fun j : Fin (a.length + 1) => List.ofFn fun k : Fin (a.length + 1) =>
      if (j, k) ∈ (constrG a b).prec then 1 else 0).flatten =
      List.replicate ((a.length + 1) * (a.length + 1)) 0 := mat_empty _
  rw [ShopInstance.code, hj, hm, codeG, yG]; simp [sum_map_mul, Nat.mul_add]

lemma codeJ_eq (a : List ℕ) (b : ℕ) : (constrJ a b).code (yJ a) = codeJ a b a.length := by
  have hj : (List.ofFn fun j : Fin (a.length + 2) => [(constrJ a b).release j,
      ((constrJ a b).ops j).length] ++ (((constrJ a b).ops j).map fun e => [e.1.val, e.2]).flatten).flatten
      = (a.map blkJ).flatten ++ [0, 2, 0, b, 1, 2 * (a.sum - b)] ++ [0, 2, 1, 2 * b, 2, a.sum - b] := by
    rw [ofFn_flatten_succ, ofFn_flatten_succ, ← ofFn_get_map]
    congr 1; congr 1
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)); simp [constrJ, blkJ]
    · simp [constrJ]
    · simp [constrJ]
  have hm : (List.ofFn fun j : Fin (a.length + 2) => List.ofFn fun k : Fin (a.length + 2) =>
      if (j, k) ∈ (constrJ a b).prec then 1 else 0).flatten =
      List.replicate ((a.length + 2) * (a.length + 2)) 0 := mat_empty _
  rw [ShopInstance.code, hj, hm, codeJ, yJ]; simp

lemma matH (t : ℕ) :
    (List.ofFn fun j : Fin (t + 2) => List.ofFn fun k : Fin (t + 2) =>
      if (j, k) ∈ ({(⟨t, by omega⟩, Fin.last (t + 1))} : Finset (Fin (t + 2) × Fin (t + 2)))
      then 1 else 0).flatten =
    List.replicate (t * (t + 2)) 0 ++ List.replicate (t + 1) 0 ++ [1] ++ List.replicate (t + 2) 0 := by
  rw [ofFn_flatten_succ, ofFn_flatten_succ]
  have h1 : (List.ofFn fun i : Fin t => List.ofFn fun k : Fin (t + 2) =>
      if (i.castSucc.castSucc, k) ∈ ({(⟨t, by omega⟩, Fin.last (t + 1))} :
        Finset (Fin (t + 2) × Fin (t + 2))) then 1 else 0) =
      List.replicate t (List.replicate (t + 2) 0) := by
    rw [← List.ofFn_const]; congr 1; funext i
    rw [← List.ofFn_const]; congr 1; funext k
    have : (i.castSucc.castSucc : Fin (t + 2)) ≠ ⟨t, by omega⟩ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp [this]
  have h2 : (List.ofFn fun k : Fin (t + 2) =>
      if ((Fin.last t).castSucc, k) ∈ ({(⟨t, by omega⟩, Fin.last (t + 1))} :
        Finset (Fin (t + 2) × Fin (t + 2))) then 1 else 0) = List.replicate (t + 1) 0 ++ [1] := by
    rw [List.ofFn_succ', List.concat_eq_append]
    congr 1
    · rw [← List.ofFn_const]; congr 1; funext k
      have : (k.castSucc : Fin (t + 2)) ≠ Fin.last (t + 1) := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [this]
    · simp [Fin.ext_iff]
  have h3 : (List.ofFn fun k : Fin (t + 2) =>
      if (Fin.last (t + 1), k) ∈ ({(⟨t, by omega⟩, Fin.last (t + 1))} :
        Finset (Fin (t + 2) × Fin (t + 2))) then 1 else 0) = List.replicate (t + 2) 0 := by
    rw [← List.ofFn_const]; congr 1; funext k
    have : (Fin.last (t + 1) : Fin (t + 2)) ≠ ⟨t, by omega⟩ := by
      intro h; have := congrArg Fin.val h; simp at this
    simp [this]
  simp only [h1, h2, h3, flatten_rep_zero, List.append_assoc]

lemma codeH_eq (a : List ℕ) (b : ℕ) :
    (constrH a b).code (yH a) = codeH (a.map (a.length * ·)) (a.length * b) a.length := by
  have hj : (List.ofFn fun j : Fin (a.length + 2) => [(constrH a b).release j,
      ((constrH a b).ops j).length] ++ (((constrH a b).ops j).map fun e => [e.1.val, e.2]).flatten).flatten
      = ((a.map (a.length * ·)).map blkG).flatten ++ [0, 2, 0, 1, 1, a.length * b] ++
        [0, 2, 0, 1, 1, (a.map (a.length * ·)).sum - a.length * b] := by
    rw [ofFn_flatten_succ, ofFn_flatten_succ, List.map_map, ← ofFn_get_map]
    congr 1; congr 1
    · refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)); simp [constrH, blkG]
    · simp [constrH]
    · simp [constrH, sum_map_mul, Nat.mul_sub]
  have hm : (List.ofFn fun j : Fin (a.length + 2) => List.ofFn fun k : Fin (a.length + 2) =>
      if (j, k) ∈ (constrH a b).prec then 1 else 0).flatten =
      List.replicate (a.length * (a.length + 2)) 0 ++ List.replicate (a.length + 1) 0 ++ [1] ++
        List.replicate (a.length + 2) 0 := matH a.length
  rw [ShopInstance.code, hj, hm, codeH, yH]; simp [sum_map_mul, Nat.mul_add]

/-! ## Classes -/

lemma classG (a : List ℕ) (b : ℕ) :
    (constrG a b).IsFlowShop ∧ (constrG a b).OnlyLastReleased ∧ (constrG a b).NoPrec := by
  refine ⟨fun j => ?_, fun j hj => ?_, rfl⟩
  · simp only [constrG]; split_ifs <;> simp [List.finRange_succ]
  · simp only [constrG]; rw [if_pos (by omega)]

lemma classH (a : List ℕ) (b : ℕ) :
    (constrH a b).IsFlowShop ∧ (constrH a b).AllReleasedAtZero ∧ (constrH a b).IsBranching := by
  refine ⟨fun j => ?_, fun j => rfl, ?_, Or.inl fun k => ?_⟩
  · simp only [constrH]; split_ifs <;> simp [List.finRange_succ]
  · intro j hj
    have key : ∀ x y : Fin (a.length + 2), Relation.TransGen (fun u v => (u, v) ∈ (constrH a b).prec) x y →
        x.val < y.val := by
      intro x y h
      induction h with
      | single h => simp [constrH] at h; obtain ⟨rfl, rfl⟩ := h; simp
      | tail _ h ih => simp [constrH] at h; obtain ⟨rfl, rfl⟩ := h; simp at ih ⊢; omega
    exact lt_irrefl _ (key j j hj)
  · calc ((constrH a b).prec.filter (fun e => e.2 = k)).card ≤ (constrH a b).prec.card :=
          Finset.card_filter_le _ _
      _ = 1 := by simp [constrH]

lemma classI (a : List ℕ) (b : ℕ) :
    (constrI a b).IsJobShopOpsLE 3 ∧ (constrI a b).AllReleasedAtZero ∧ (constrI a b).NoPrec := by
  refine ⟨fun j => ?_, fun j => rfl, rfl⟩
  simp only [constrI]; split_ifs <;> simp

lemma classJ (a : List ℕ) (b : ℕ) :
    (constrJ a b).IsJobShopOpsLE 2 ∧ (constrJ a b).AllReleasedAtZero ∧ (constrJ a b).NoPrec := by
  refine ⟨fun j => ?_, fun j => rfl, rfl⟩
  simp only [constrJ]; split_ifs <;> simp

lemma emptyG : (emptyInst 2).IsFlowShop ∧ (emptyInst 2).OnlyLastReleased ∧ (emptyInst 2).NoPrec :=
  ⟨fun j => j.elim0, fun j => j.elim0, rfl⟩
lemma emptyH : (emptyInst 2).IsFlowShop ∧ (emptyInst 2).AllReleasedAtZero ∧ (emptyInst 2).IsBranching :=
  ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, Or.inl fun j => j.elim0⟩
lemma emptyI : (emptyInst 2).IsJobShopOpsLE 3 ∧ (emptyInst 2).AllReleasedAtZero ∧ (emptyInst 2).NoPrec :=
  ⟨fun j => j.elim0, fun j => j.elim0, rfl⟩
lemma emptyJ : (emptyInst 3).IsJobShopOpsLE 2 ∧ (emptyInst 3).AllReleasedAtZero ∧ (emptyInst 3).NoPrec :=
  ⟨fun j => j.elim0, fun j => j.elim0, rfl⟩

/-! ## Function specifications -/

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

noncomputable def outSpec (code : List ℕ → ℕ → ℕ → List ℕ) (m : ℕ) (w : List BSym) : List BSym :=
  match dec w with
  | some (b :: a) => if b < a.sum then encNats (code a b a.length)
      else if b = a.sum then encNats [0, m, 0] else []
  | _ => []

noncomputable def scaleSpec (w : List BSym) : List BSym :=
  match dec w with
  | some l => encNats (l.map ((l.length - 1) * ·))
  | none => []

lemma outSpec_none (code : List ℕ → ℕ → ℕ → List ℕ) (m : ℕ) {w : List BSym}
    (h : ¬ ∃ l, PosCode w l) : outSpec code m w = [] := by
  rw [outSpec, dec_none h]

lemma outSpec_some (code : List ℕ → ℕ → ℕ → List ℕ) (m : ℕ) {w : List BSym} {a : List ℕ} {b : ℕ}
    (h : PosCode w (b :: a)) : outSpec code m w = if b < a.sum then encNats (code a b a.length)
      else if b = a.sum then encNats [0, m, 0] else [] := by
  rw [outSpec, dec_of h]

/-- generic correctness of an output stage on a valid KNAPSACK code -/
lemma out_correct {m : ℕ} {C : ∀ {n : ℕ}, ShopInstance n m → Prop}
    (code : List ℕ → ℕ → ℕ → List ℕ) (hE : C (emptyInst m)) (P : List ℕ → ℕ → Prop)
    (hP : ∀ a b, (∀ v ∈ a, 0 < v) → 0 < b → b < a.sum → (encNats (code a b a.length) ∈ shopLang m C ↔ P a b))
    (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧ P a b ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec code m x ∈ shopLang m C := by
  by_cases hx : ∃ l, PosCode x l
  · obtain ⟨l, hl⟩ := hx
    obtain ⟨b, a, rfl⟩ := List.exists_cons_of_ne_nil hl.1
    have hpa : ∀ v ∈ a, 0 < v := fun v hv => hl.2.1 v (by simp [hv])
    have hb : 0 < b := hl.2.1 b (by simp)
    have uniq : ∀ (a' : List ℕ) (b' : ℕ), x = encNats (b' :: a') → a' = a ∧ b' = b := by
      intro a' b' h; have := encNats_inj (h.symm.trans hl.2.2); simp at this; exact ⟨this.2, this.1⟩
    rw [outSpec_some code m hl]
    rcases lt_trichotomy b a.sum with hlt | heq | hgt
    · rw [if_pos hlt, hP a b hpa hb hlt]
      constructor
      · rintro (⟨a', b', -, -, -, hp, hx'⟩ | ⟨a', b', -, -, he, hx'⟩)
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; exact hp
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
      · intro hp; exact Or.inl ⟨a, b, hpa, hb, hlt, hp, hl.2.2⟩
    · rw [if_neg (by omega), if_pos heq]
      exact iff_of_true (Or.inr ⟨a, b, hpa, hb, heq, hl.2.2⟩) (empty_mem hE)
    · rw [if_neg (by omega), if_neg (by omega)]
      refine iff_of_false ?_ nil_not_mem
      rintro (⟨a', b', -, -, h1, -, hx'⟩ | ⟨a', b', -, -, h1, hx'⟩)
      · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
      · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
  · rw [outSpec_none code m hx]
    refine iff_of_false ?_ nil_not_mem
    rintro (⟨a', b', h1, h2, -, -, hx'⟩ | ⟨a', b', h1, h2, -, hx'⟩)
    · exact hx ⟨b' :: a', by simp, by simpa using ⟨h2, h1⟩, hx'⟩
    · exact hx ⟨b' :: a', by simp, by simpa using ⟨h2, h1⟩, hx'⟩

lemma scale_correct {m : ℕ} {C : ∀ {n : ℕ}, ShopInstance n m → Prop}
    (code : List ℕ → ℕ → ℕ → List ℕ) (hE : C (emptyInst m)) (P : List ℕ → ℕ → Prop)
    (hP : ∀ a b, (∀ v ∈ a, 0 < v) → 0 < b → b < a.sum →
      (encNats (code (a.map (a.length * ·)) (a.length * b) a.length) ∈ shopLang m C ↔ P a b))
    (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧ P a b ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec code m (scaleSpec x) ∈ shopLang m C := by
  by_cases hx : ∃ l, PosCode x l
  · obtain ⟨l, hl⟩ := hx
    obtain ⟨b, a, rfl⟩ := List.exists_cons_of_ne_nil hl.1
    have hpa : ∀ v ∈ a, 0 < v := fun v hv => hl.2.1 v (by simp [hv])
    have hb : 0 < b := hl.2.1 b (by simp)
    have uniq : ∀ (a' : List ℕ) (b' : ℕ), x = encNats (b' :: a') → a' = a ∧ b' = b := by
      intro a' b' h; have := encNats_inj (h.symm.trans hl.2.2); simp at this; exact ⟨this.2, this.1⟩
    have hs : scaleSpec x = encNats (a.length * b :: a.map (a.length * ·)) := by
      rw [scaleSpec, dec_of hl]; simp
    rw [hs]
    rcases Nat.eq_zero_or_pos a.length with ht | ht
    · have ha : a = [] := List.eq_nil_of_length_eq_zero ht
      subst ha
      rw [outSpec_none]
      · refine iff_of_false ?_ nil_not_mem
        rintro (⟨a', b', -, -, h1, -, hx'⟩ | ⟨a', b', -, -, h1, hx'⟩)
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; simp at h1
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; simp at h1; omega
      · rintro ⟨l', hl'⟩
        have := encNats_inj hl'.2.2
        have := hl'.2.1 0 (by rw [← this]; simp)
        omega
    · have hpos : PosCode (encNats (a.length * b :: a.map (a.length * ·)))
          (a.length * b :: a.map (a.length * ·)) := by
        refine ⟨by simp, ?_, rfl⟩
        intro v hv
        simp only [List.mem_cons, List.mem_map] at hv
        rcases hv with rfl | ⟨u, hu, rfl⟩
        · exact Nat.mul_pos ht hb
        · exact Nat.mul_pos ht (hpa u hu)
      rw [outSpec_some code m hpos, List.length_map, sum_map_mul]
      rcases lt_trichotomy b a.sum with hlt | heq | hgt
      · rw [if_pos (Nat.mul_lt_mul_of_pos_left hlt ht), hP a b hpa hb hlt]
        constructor
        · rintro (⟨a', b', -, -, -, hp, hx'⟩ | ⟨a', b', -, -, he, hx'⟩)
          · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; exact hp
          · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
        · intro hp; exact Or.inl ⟨a, b, hpa, hb, hlt, hp, hl.2.2⟩
      · rw [if_neg (by rw [heq]; omega), if_pos (by rw [heq])]
        exact iff_of_true (Or.inr ⟨a, b, hpa, hb, heq, hl.2.2⟩) (empty_mem hE)
      · rw [if_neg (by intro h; have := Nat.lt_of_mul_lt_mul_left h; omega),
          if_neg (by intro h; have := Nat.eq_of_mul_eq_mul_left ht h; omega)]
        refine iff_of_false ?_ nil_not_mem
        rintro (⟨a', b', -, -, h1, -, hx'⟩ | ⟨a', b', -, -, h1, hx'⟩)
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
        · obtain ⟨rfl, rfl⟩ := uniq a' b' hx'; omega
  · have hs : scaleSpec x = [] := by rw [scaleSpec, dec_none hx]
    rw [hs, outSpec_none]
    · refine iff_of_false ?_ nil_not_mem
      rintro (⟨a', b', h1, h2, -, -, hx'⟩ | ⟨a', b', h1, h2, -, hx'⟩)
      · exact hx ⟨b' :: a', by simp, by simpa using ⟨h2, h1⟩, hx'⟩
      · exact hx ⟨b' :: a', by simp, by simpa using ⟨h2, h1⟩, hx'⟩
    · rintro ⟨l', hl'⟩; exact encNats_ne_nil hl'.1 hl'.2.2.symm

theorem correctG (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (constrG a b).HasScheduleLE (yG a) ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeG 2 (scaleSpec x) ∈ langFlowRn :=
  scale_correct codeG emptyG _ (fun a b _ _ _ => by
    rw [← codeG_eq]; exact mem_shopLang _ _ (classG a b)) x

theorem correctH (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (constrH a b).HasScheduleLE (yH a) ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeH 2 (scaleSpec x) ∈ langFlowTree :=
  scale_correct codeH emptyH _ (fun a b _ _ _ => by
    rw [← codeH_eq]; exact mem_shopLang _ _ (classH a b)) x

theorem correctI (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (constrI a b).HasScheduleLE (yI a) ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeI 2 x ∈ langJob2Ops3 :=
  out_correct codeI emptyI _ (fun a b _ _ _ => by
    rw [← codeI_eq]; exact mem_shopLang _ _ (classI a b)) x

theorem correctJ (x : List BSym) :
    ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
        (constrJ a b).HasScheduleLE (yJ a) ∧ x = encNats (b :: a)) ∨
      (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
      outSpec codeJ 3 x ∈ langJob3Ops2 :=
  out_correct codeJ emptyJ _ (fun a b _ _ _ => by
    rw [← codeJ_eq]; exact mem_shopLang _ _ (classJ a b)) x

end GHIK



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GHIK
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

end GHIK



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GHIK
open CookPvsNP ProjSchedTW.Complexity

inductive Key
  | inp | W | sc | o | z | bad | T | B | A | X | Y | tmp | car | D | R | out | M | C | V | S | N
  | Q | K1
  deriving DecidableEq

instance : Fintype Key where
  elems := {.inp, .W, .sc, .o, .z, .bad, .T, .B, .A, .X, .Y, .tmp, .car, .D, .R, .out, .M, .C, .V,
    .S, .N, .Q, .K1}
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

/-! ## The scaling stage -/

def rS : Fin 4 ↪ Key := ⟨![.X, .M, .C, .sc], by decide⟩

def bodyS : StackProg Key BSym :=
  .seq (pushProg .X .sep) (.seq (moveTok .inp .tmp) (.seq (popProg .inp) (.seq (tr1 .tmp .X)
    (.seq (copyProg .T .C .sc) (.seq (repeatCopyProg rS) (.seq (sumLoop .M .A .tmp .car)
    (.seq (tr1 .A .R) (.seq (pushProg .R .sep) (clr .X)))))))))

def PreS (t : ℕ) (s : Store) : Prop :=
  s .X = [] ∧ s .M = [] ∧ s .C = [] ∧ s .A = [] ∧ s .tmp = [] ∧ s .car = [] ∧ s .sc = [] ∧
    s .T = List.replicate t .one

lemma tok_stop (rest : List BSym) : stopAt ne (BSym.sep :: rest) := by simp [stopAt]

lemma len_tokOf_le (k : ℕ) (l : List ℕ) (hk : k ≤ l.sum) : (tokOf k).length ≤ (encNats l).length := by
  have h1 := sum_lt_pow l
  have : k < 2 ^ (encNats l).length := by omega
  simpa [tokOf, enc] using bits_length_le_of_lt this

lemma exec_bodyS (t k : ℕ) (rest : List BSym) (s : Store) (hk : 0 < k)
    (hs : s .inp = tokOf k ++ .sep :: rest) (hp : PreS t s) :
    ExecLe bodyS s (Function.update (Function.update s .inp rest) .R
      ((encNat (t * k)).reverse ++ s .R))
      (60 * ((t + 1) * ((tokOf k).length + 2)) ^ 2 + 100) := by
  obtain ⟨hX, hM, hC, hA, htmp, hcar, hsc, hT⟩ := hp
  set ℓ := (tokOf k).length
  have e1 := exec_pushE Key.X BSym.sep s
  set s1 := Function.update s Key.X (BSym.sep :: s Key.X)
  have e2 := exec_moveTok Key.inp Key.tmp (by decide) (tokOf k) (.sep :: rest) s1
    (by simp [s1, hs]) (tokOf_ne k) (tok_stop rest)
  set s2 := Function.update (Function.update s1 Key.inp (BSym.sep :: rest)) Key.tmp
    ((tokOf k).reverse ++ s1 Key.tmp)
  have e3 := exec_popE Key.inp s2
  set s3 := Function.update s2 Key.inp (s2 Key.inp).tail
  have e4 := exec_tr1 Key.tmp Key.X (by decide) s3
  set s4 := Function.update (Function.update s3 Key.tmp []) Key.X ((s3 Key.tmp).reverse ++ s3 Key.X)
  have e5 := exec_copyE Key.T Key.C Key.sc (by decide) (by decide) (by decide) s4
    (by simp [s4, s3, s2, s1, hsc])
  set s5 := Function.update s4 Key.C (s4 Key.T ++ s4 Key.C)
  have e6 := ExecLe.of (stack_repeat_copy rS s5 (by simp [rS, s5, s4, s3, s2, s1, hsc])) le_rfl
  set s6 := Function.update (Function.update s5 (rS 2) []) (rS 1)
    ((List.replicate (s5 (rS 2)).length (s5 (rS 0))).flatten ++ s5 (rS 1))
  have hX5 : s5 (rS 0) = tokOf k ++ [.sep] := by simp [rS, s5, s4, s3, s2, s1, htmp, hX]
  have hC5 : s5 (rS 2) = List.replicate t .one := by simp [rS, s5, s4, s3, s2, s1, hT, hC]
  have hM6 : s6 .M = encNats (List.replicate t k) := by
    simp only [s6, rS]; simp [encNats_rep, s5, s4, s3, s2, s1, hM, hT, hC, htmp, hX]
  have e7 := exec_sumE Key.M Key.A Key.tmp Key.car (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (List.replicate t k) 0 s6 hM6
    (by simp [s6, rS, s5, s4, s3, s2, s1, hA, tokOf_zero])
    (by simp [s6, rS, s5, s4, s3, s2, s1])
    (by simp [s6, rS, s5, s4, s3, s2, s1, hcar])
  set s7 := Function.update (Function.update s6 Key.M []) Key.A
    (tokOf (0 + (List.replicate t k).sum))
  have e8 := exec_tr1 Key.A Key.R (by decide) s7
  set s8 := Function.update (Function.update s7 Key.A []) Key.R ((s7 Key.A).reverse ++ s7 Key.R)
  have e9 := exec_pushE Key.R BSym.sep s8
  set s9 := Function.update s8 Key.R (BSym.sep :: s8 Key.R)
  have e10 := exec_clr Key.X s9
  have e := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq e10))))))))
  refine (e.congr ?_).mono ?_
  · funext j
    cases j <;> simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, rS, hX, hM, hC, hA, htmp, hcar, hsc,
      encNat_eq, List.sum_replicate, mul_comm]
  · have L3 : (s3 Key.tmp).length = ℓ := by simp [s3, s2, s1, htmp, ℓ]
    have L4 : (s4 Key.T).length = t := by simp [s4, s3, s2, s1, hT]
    have L50 : (s5 (rS 0)).length = ℓ + 1 := by rw [hX5]; simp [ℓ]
    have L52 : (s5 (rS 2)).length = t := by rw [hC5]; simp
    have LM : (encNats (List.replicate t k)).length = t * (ℓ + 1) := by
      rw [encNats_rep]; simp [ℓ]
    have L7 : (s7 Key.A).length ≤ t * (ℓ + 1) := by
      simp only [s7, Function.update_self]; rw [← LM]; apply len_tokOf_le; simp
    have L9 : (s9 Key.X).length = ℓ + 1 := by
      simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, rS, hX, htmp, ℓ]
    rw [L3, L4, L50, L52, LM, L9]
    have hb0 : (Nat.bits 0).length = 0 := by simp
    rw [hb0]
    generalize (s7 Key.A).length = a7 at L7 ⊢
    have hP : t * (ℓ + 1) ≤ (t + 1) * (ℓ + 2) := by nlinarith
    have hP2 : ℓ + 2 ≤ (t + 1) * (ℓ + 2) := by nlinarith
    have hP3 : t + 1 ≤ (t + 1) * (ℓ + 2) := by nlinarith
    generalize (t + 1) * (ℓ + 2) = P at hP hP2 hP3 ⊢
    generalize t * (ℓ + 1) = m at hP L7 ⊢
    nlinarith

def mainS : StackProg Key BSym :=
  .seq (copyProg .inp .W .sc) (.seq (countP .W .T) (.seq (popProg .T)
    (.seq (tokLoop .inp bodyS) (tr1 .R .out))))

lemma rev_flatten_map (g : ℕ → List BSym) (l : List ℕ) :
    (l.reverse.map (fun k => (g k).reverse)).flatten = ((l.map g).flatten).reverse := by
  induction l with
  | nil => rfl
  | cons k l ih => simp [List.reverse_flatten, List.map_reverse, Function.comp_def]

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

lemma exec_mainS (l : List ℕ) (hl : l ≠ []) (hpos : ∀ v ∈ l, 0 < v) :
    ∃ t : Store, ExecLe mainS (initS (encNats l)) t
      (200 * ((encNats l).length + 2) ^ 5 + 200) ∧
      t .out = encNats (l.map ((l.length - 1) * ·)) := by
  set w := encNats l
  set L := w.length
  set t := l.length - 1
  have e1 := exec_copyE Key.inp Key.W Key.sc (by decide) (by decide) (by decide) (initS w) rfl
  set s1 := Function.update (initS w) Key.W (initS w Key.inp ++ initS w Key.W)
  have e2 := exec_countP Key.W Key.T (by decide) s1
  set s2 := Function.update (Function.update s1 Key.W []) Key.T
    (List.replicate ((s1 Key.W).count .sep) .one ++ s1 Key.T)
  have e3 := exec_popE Key.T s2
  set s3 := Function.update s2 Key.T (s2 Key.T).tail
  have hT3 : s3 Key.T = List.replicate t .one := by
    simp [s3, s2, s1, initS, w, count_sep_encNats, t]
  have hpre : PreS t s3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hT3⟩ <;> simp [s3, s2, s1, initS]
  have e4 := exec_tokLoop Key.inp Key.R (by decide) bodyS (PreS t)
    (fun k => (encNat (t * k)).reverse) (60 * ((t + 1) * (L + 2)) ^ 2 + 100)
    (fun k => 0 < k ∧ k ∈ l)
    (by
      intro s rest x ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5], by simp [h6],
        by simp [h7], by simp [h8]⟩)
    (by
      intro k rest s hk hs hp
      have hb := exec_bodyS t k rest s hk.1 hs hp
      refine hb.mono ?_
      have : (tokOf k).length ≤ L := len_tok_le_code hk.2
      have : (t + 1) * ((tokOf k).length + 2) ≤ (t + 1) * (L + 2) := Nat.mul_le_mul_left _ (by omega)
      have := Nat.pow_le_pow_left this 2
      omega)
    l s3 (fun v hv => ⟨hpos v hv, hv⟩) (by simp [s3, s2, s1, initS, w]) hpre
  set s4 := Function.update (Function.update s3 Key.inp []) Key.R
    ((l.reverse.map (fun k => (encNat (t * k)).reverse)).flatten ++ s3 Key.R)
  have e5 := exec_tr1 Key.R Key.out (by decide) s4
  have hR : s4 Key.R = (encNats (l.map (t * ·))).reverse := by
    simp only [s4, Function.update_self]
    rw [rev_flatten_map (fun k => encNat (t * k))]
    simp [s3, s2, s1, initS, encNats, List.flatMap, Function.comp_def]
  refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_, ?_⟩
  · rw [hR]
    have hLw : L = (encNats l).length := rfl
    have hl1 : (initS w Key.inp).length = L := by simp [initS, hLw, w]
    have hl2 : (s1 Key.W).length = L := by simp [s1, initS, hLw, w]
    rw [hl1, hl2, List.length_reverse]
    have hlen : l.length ≤ L := len_code_ge l
    have htL : t + 1 ≤ L + 1 := by omega
    have hRl : (encNats (l.map (t * ·))).length ≤ L * (L * (L + 1) + 1) := by
      refine le_trans (len_encNats_le _ (L * (L + 1)) ?_) ?_
      · intro v hv
        simp only [List.mem_map] at hv
        obtain ⟨k, hk, rfl⟩ := hv
        refine le_trans (len_tokOf_le (t * k) (List.replicate t k) (by simp)) ?_
        rw [encNats_rep]; simp
        have := len_tok_le_code hk
        rw [← hLw] at this
        exact Nat.mul_le_mul (by omega) (by omega)
      · rw [List.length_map]; exact Nat.mul_le_mul_right _ hlen
    have hq : (t + 1) * (L + 2) ≤ (L + 2) * (L + 2) := Nat.mul_le_mul_right _ (by omega)
    have hq2 := Nat.pow_le_pow_left hq 2
    have hq3 : l.length * (60 * ((t + 1) * (L + 2)) ^ 2 + 100 + 2) ≤
        (L + 2) * (60 * ((L + 2) * (L + 2)) ^ 2 + 102) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hq4 : 3 * (L * (L * (L + 1) + 1)) ≤ 3 * (L + 2) ^ 5 := by
      have : L * (L * (L + 1) + 1) ≤ (L + 2) ^ 5 := by nlinarith
      omega
    have hq5 : (L + 2) * (60 * ((L + 2) * (L + 2)) ^ 2 + 102) = 60 * (L + 2) ^ 5 + 102 * (L + 2) := by
      ring
    nlinarith
  · simp only [Function.update_self]
    rw [hR]; simp [s4, s3, s2, s1, initS]

/-! ## Polynomial absorption -/

lemma absorb5 (L : ℕ) : 300 * (L + 2) ^ 5 ≤ L ^ 100000 + 100000 := by
  rcases Nat.lt_or_ge L 2 with h | h
  · interval_cases L <;> norm_num
  · have h1 : (L + 2) ^ 5 ≤ (2 * L) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    have h2 : (2 : ℕ) ^ 14 ≤ L ^ 14 := Nat.pow_le_pow_left h 14
    have h3 : L ^ 19 ≤ L ^ 100000 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : (2 * L) ^ 5 = 32 * L ^ 5 := by ring
    have h5 : L ^ 19 = L ^ 5 * L ^ 14 := by ring
    have h6 : 300 * (32 * L ^ 5) ≤ L ^ 5 * L ^ 14 := by
      have : 300 * 32 ≤ L ^ 14 := le_trans (by norm_num) h2
      nlinarith [Nat.zero_le (L ^ 5)]
    omega

lemma initS_eq (w : List BSym) : initS w = fun j => if j = Key.inp then w else [] := rfl

theorem scale_poly : PolyTimeComputable scaleSpec := by
  apply stack_program_polytime (wrap mainS) Key.inp Key.out scaleSpec 100000
  intro w
  by_cases hv : vrun w = (false, false, false)
  · obtain ⟨l, hl⟩ := (vrun_iff w).1 hv
    obtain ⟨t, ⟨n, hn, e⟩, ht⟩ := exec_mainS l hl.1 hl.2.1
    rw [← hl.2.2] at e
    obtain ⟨m, hm, e'⟩ := exec_wrap_valid mainS w t _ hv ⟨n, hn, e⟩
    refine ⟨t, m, ?_, e', ?_⟩
    · have := absorb5 w.length
      rw [← hl.2.2] at hm
      have h2 : 9 * w.length ≤ 9 * (w.length + 2) ^ 5 := by
        have : w.length ≤ (w.length + 2) ^ 5 := by
          calc w.length ≤ w.length + 2 := by omega
            _ ≤ (w.length + 2) ^ 5 := Nat.le_self_pow (by norm_num) _
        omega
      omega
    · rw [ht, scaleSpec, dec_of hl]
  · obtain ⟨m, hm, e'⟩ := exec_wrap_invalid mainS w hv
    refine ⟨valStore w, m, ?_, e', ?_⟩
    · have := absorb5 w.length
      have : w.length ≤ (w.length + 2) ^ 5 := by
          calc w.length ≤ w.length + 2 := by omega
            _ ≤ (w.length + 2) ^ 5 := Nat.le_self_pow (by norm_num) _
      omega
    · have hn : ¬ ∃ l, PosCode w l := fun h => hv ((vrun_iff w).2 h)
      simp [valStore, scaleSpec, dec_none hn]

end GHIK



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GHIK
open CookPvsNP ProjSchedTW.Complexity

/-! ## Output scripts -/

def baseStore (a : List ℕ) (b t vA vD : ℕ) (R' : List BSym) : Store := fun k =>
  match k with
  | .inp => encNats a | .B => tokOf b | .T => List.replicate t .one | .A => tokOf vA
  | .D => tokOf vD | .R => R' | _ => []

def rO : Fin 4 ↪ Key := ⟨![.Q, .M, .C, .sc], by decide⟩

def loadN : Option Key → StackProg Key BSym
  | none => skipP
  | some k => copyProg k .N .sc

def baseVal (b vA vD : ℕ) : Option Key → ℕ
  | some .A => vA
  | some .B => b
  | some .D => vD
  | _ => 0

def BaseOK : Option Key → Prop
  | none => True
  | some k => k = .A ∨ k = .B ∨ k = .D

def cntP (k : Key) (α : Bool) (c : ℕ) : StackProg Key BSym :=
  .seq (if α then copyProg .T k .sc else skipP) (pushSeq k (List.replicate c .one))

def numP (base : Option Key) (α : Bool) (c : ℕ) (dbl : Bool) : StackProg Key BSym :=
  .seq (loadN base) (.seq (cntP .C α c) (.seq (addOnes rO .N .tmp .car)
    (.seq (if dbl then pushProg .R .zero else skipP) (.seq (tr1 .N .R) (pushProg .R .sep)))))

lemma tokOf_double {x : ℕ} (hx : 0 < x) : tokOf (2 * x) = .zero :: tokOf x := by
  have : Nat.bits (2 * x) = false :: Nat.bits x := by
    have h := Nat.bits_append_bit x false (fun h => by omega)
    simpa [Nat.bit] using h
  simp [tokOf, this, enc, toB]

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

structure LenOK (a : List ℕ) (b t vA vD L : ℕ) : Prop where
  ha : (encNats a).length ≤ L
  hb : (tokOf b).length ≤ L
  hA : (tokOf vA).length ≤ L
  hD : (tokOf vD).length ≤ L
  ht : t ≤ L

lemma baseVal_len {a : List ℕ} {b t vA vD L : ℕ} (h : LenOK a b t vA vD L) (base : Option Key)
    (hb : BaseOK base) : (tokOf (baseVal b vA vD base)).length ≤ L := by
  rcases base with _ | k
  · simp [baseVal, tokOf_zero]
  · rcases hb with rfl | rfl | rfl
    · exact h.hA
    · exact h.hb
    · exact h.hD

lemma exec_loadN (a : List ℕ) (b t vA vD : ℕ) (R' : List BSym) (base : Option Key)
    (hb : BaseOK base) :
    ExecLe (loadN base) (baseStore a b t vA vD R')
      (Function.update (baseStore a b t vA vD R') .N (tokOf (baseVal b vA vD base)))
      (6 * (tokOf (baseVal b vA vD base)).length + 3) := by
  rcases base with _ | k
  · refine ((exec_skip _).congr ?_).mono (by omega)
    funext j; cases j <;> simp [baseStore, baseVal, tokOf_zero]
  · rcases hb with rfl | rfl | rfl
    all_goals
      refine ((exec_copyE _ Key.N Key.sc (by decide) (by decide) (by decide) _ rfl).congr ?_).mono
        (by simp [baseStore, baseVal])
      funext j; cases j <;> simp [baseStore, baseVal]

lemma exec_num (a : List ℕ) (b t vA vD L : ℕ) (R' : List BSym) (hL : LenOK a b t vA vD L)
    (base : Option Key) (hb : BaseOK base) (α : Bool) (c : ℕ) (hc : c ≤ 2) (dbl : Bool)
    (hpos : dbl = true → 0 < baseVal b vA vD base + ((if α then t else 0) + c)) :
    ExecLe (numP base α c dbl) (baseStore a b t vA vD R')
      (baseStore a b t vA vD ((encNat (if dbl then 2 * (baseVal b vA vD base +
        ((if α then t else 0) + c)) else baseVal b vA vD base + ((if α then t else 0) + c))).reverse
        ++ R')) (100 * (L + 3) ^ 2) := by
  set v0 := baseVal b vA vD base
  set c' := (if α then t else 0) + c
  have hc' : c' ≤ L + 2 := by simp only [c']; split_ifs <;> have := hL.ht <;> omega
  have hv0 := baseVal_len hL base hb
  have e1 := exec_loadN a b t vA vD R' base hb
  set s1 := Function.update (baseStore a b t vA vD R') Key.N (tokOf v0)
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

lemma exec_consts (a : List ℕ) (b t vA vD : ℕ) (R' : List BSym) (cs : List ℕ) :
    ExecLe (pushSeq Key.R (encNats cs)) (baseStore a b t vA vD R')
      (baseStore a b t vA vD ((encNats cs).reverse ++ R')) (2 * (encNats cs).length + 1) := by
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

def rL : Fin 4 ↪ Key := ⟨![.Q, .R, .C, .sc], by decide⟩
def rV : Fin 4 ↪ Key := ⟨![.Q, .V, .C, .sc], by decide⟩
def rG : Fin 4 ↪ Key := ⟨![.V, .R, .K1, .sc], by decide⟩

def lineP (c : ℕ) : StackProg Key BSym :=
  .seq (cntP .C true c) (.seq (pushProg .Q .sep) (.seq (repeatCopyProg rL) (clr .Q)))

def gridP (cr cc : ℕ) : StackProg Key BSym :=
  .seq (cntP .C true cc) (.seq (pushProg .Q .sep) (.seq (repeatCopyProg rV) (.seq (clr .Q)
    (.seq (cntP .K1 true cr) (.seq (repeatCopyProg rG) (clr .V))))))

lemma exec_line (a : List ℕ) (b t vA vD L : ℕ) (R' : List BSym) (hL : LenOK a b t vA vD L)
    (c : ℕ) (hc : c ≤ 2) :
    ExecLe (lineP c) (baseStore a b t vA vD R')
      (baseStore a b t vA vD ((encNats (List.replicate (t + c) 0)).reverse ++ R'))
      (100 * (L + 3) ^ 2) := by
  have e1 := exec_cntP Key.C (by decide) (by decide) true c t (baseStore a b t vA vD R')
    (by simp [baseStore]) (by simp [baseStore]) (by simp [baseStore])
  set s1 := Function.update (baseStore a b t vA vD R') Key.C
    (List.replicate ((if true = true then t else 0) + c) .one)
  have e2 := exec_pushE Key.Q BSym.sep s1
  set s2 := Function.update s1 Key.Q (BSym.sep :: s1 Key.Q)
  have e3 := ExecLe.of (stack_repeat_copy rL s2 (by simp [rL, s2, s1, baseStore])) le_rfl
  set s3 := Function.update (Function.update s2 (rL 2) []) (rL 1)
    ((List.replicate (s2 (rL 2)).length (s2 (rL 0))).flatten ++ s2 (rL 1))
  have e4 := exec_clr Key.Q s3
  have e := e1.seq (e2.seq (e3.seq e4))
  refine (e.congr ?_).mono ?_
  · funext j; cases j <;> simp [s3, s2, s1, rL, baseStore, encNats_rep_zero, flatten_rep_sep]
  · have h2 : (s2 (rL 2)).length = t + c := by simp [s2, s1, rL, baseStore]
    have h0 : (s2 (rL 0)).length = 1 := by simp [s2, s1, rL, baseStore]
    have h3 : (s3 Key.Q).length = 1 := by simp [s3, s2, s1, rL, baseStore]
    rw [h2, h0, h3]
    have := hL.ht
    nlinarith

lemma exec_grid (a : List ℕ) (b t vA vD L : ℕ) (R' : List BSym) (hL : LenOK a b t vA vD L)
    (cr cc : ℕ) (hr : cr ≤ 2) (hc : cc ≤ 2) :
    ExecLe (gridP cr cc) (baseStore a b t vA vD R')
      (baseStore a b t vA vD ((encNats (List.replicate ((t + cr) * (t + cc)) 0)).reverse ++ R'))
      (100 * (L + 3) ^ 2) := by
  have e1 := exec_cntP Key.C (by decide) (by decide) true cc t (baseStore a b t vA vD R')
    (by simp [baseStore]) (by simp [baseStore]) (by simp [baseStore])
  set s1 := Function.update (baseStore a b t vA vD R') Key.C
    (List.replicate ((if true = true then t else 0) + cc) .one)
  have e2 := exec_pushE Key.Q BSym.sep s1
  set s2 := Function.update s1 Key.Q (BSym.sep :: s1 Key.Q)
  have e3 := ExecLe.of (stack_repeat_copy rV s2 (by simp [rV, s2, s1, baseStore])) le_rfl
  set s3 := Function.update (Function.update s2 (rV 2) []) (rV 1)
    ((List.replicate (s2 (rV 2)).length (s2 (rV 0))).flatten ++ s2 (rV 1))
  have e4 := exec_clr Key.Q s3
  set s4 := Function.update s3 Key.Q []
  have e5 := exec_cntP Key.K1 (by decide) (by decide) true cr t s4
    (by simp [s4, s3, s2, s1, rV, baseStore]) (by simp [s4, s3, s2, s1, rV, baseStore])
    (by simp [s4, s3, s2, s1, rV, baseStore])
  set s5 := Function.update s4 Key.K1 (List.replicate ((if true = true then t else 0) + cr) .one)
  have e6 := ExecLe.of (stack_repeat_copy rG s5 (by simp [rG, s5, s4, s3, s2, s1, rV, baseStore]))
    le_rfl
  set s6 := Function.update (Function.update s5 (rG 2) []) (rG 1)
    ((List.replicate (s5 (rG 2)).length (s5 (rG 0))).flatten ++ s5 (rG 1))
  have e7 := exec_clr Key.V s6
  have e := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  refine (e.congr ?_).mono ?_
  · funext j; cases j <;> simp [s6, s5, s4, s3, s2, s1, rG, rV, baseStore, encNats_rep_zero,
      flatten_rep_sep]
  · have h2 : (s2 (rV 2)).length = t + cc := by simp [s2, s1, rV, baseStore]
    have h0 : (s2 (rV 0)).length = 1 := by simp [s2, s1, rV, baseStore]
    have h3 : (s3 Key.Q).length = 1 := by simp [s3, s2, s1, rV, baseStore]
    have h52 : (s5 (rG 2)).length = t + cr := by simp [s5, rG]
    have h50 : (s5 (rG 0)).length = t + cc := by simp [s5, s4, s3, s2, s1, rG, rV, baseStore]
    have h6 : (s6 Key.V).length = t + cc := by simp [s6, s5, s4, s3, s2, s1, rG, rV, baseStore]
    rw [h2, h0, h3, h52, h50, h6]
    have := hL.ht
    have : (6 * (t + cc) + 7) * (t + cr) ≤ (6 * (L + 2) + 7) * (L + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith

/-! ### job loops -/

def jobsP (body : StackProg Key BSym) : StackProg Key BSym :=
  .seq (copyProg .inp .W .sc) (tokLoop .W body)

lemma encNats_flatten (L : List (List ℕ)) : encNats L.flatten = (L.map encNats).flatten := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [encNats_append, ih]

lemma exec_jobs (a : List ℕ) (b t vA vD : ℕ) (R' : List BSym) (hpos : ∀ v ∈ a, 0 < v)
    (body : StackProg Key BSym) (blk : ℕ → List ℕ) (Bd : ℕ)
    (hbody : ∀ k rest (s : Store), k ∈ a → s .W = tokOf k ++ .sep :: rest → s .S = [] → s .X = [] →
      ExecLe body s (Function.update (Function.update s .W rest) .R
        ((encNats (blk k)).reverse ++ s .R)) Bd) :
    ExecLe (jobsP body) (baseStore a b t vA vD R')
      (baseStore a b t vA vD ((encNats ((a.map blk).flatten)).reverse ++ R'))
      (6 * (encNats a).length + 3 + (a.length * (Bd + 2) + 1) + 1) := by
  have e1 := exec_copyE Key.inp Key.W Key.sc (by decide) (by decide) (by decide)
    (baseStore a b t vA vD R') rfl
  set s1 := Function.update (baseStore a b t vA vD R') Key.W
    (baseStore a b t vA vD R' Key.inp ++ baseStore a b t vA vD R' Key.W)
  have e2 := exec_tokLoop Key.W Key.R (by decide) body (fun s => s .S = [] ∧ s .X = [])
    (fun k => (encNats (blk k)).reverse) Bd (fun k => k ∈ a)
    (by intro s rest x ⟨h1, h2⟩; exact ⟨by simp [h1], by simp [h2]⟩)
    (fun k rest s hk hs hp => hbody k rest s hk hs hp.1 hp.2) a s1 (fun v hv => hv)
    (by simp [s1, baseStore]) ⟨by simp [s1, baseStore], by simp [s1, baseStore]⟩
  refine ((e1.seq e2).congr ?_).mono (by simp [baseStore])
  funext j; cases j <;> simp [s1, baseStore]
  simp [encNats_flatten, List.reverse_flatten, List.map_reverse, Function.comp_def]

lemma tokOf_two : tokOf 2 = [.zero, .one] := by
  rw [show (2 : ℕ) = 2 * 1 by rfl, tokOf_double (by norm_num), tokOf_one]

lemma tokOf_three : tokOf 3 = [.one, .one] := by
  have : Nat.bits 3 = [true, true] := by
    have h := Nat.bits_append_bit 1 true (fun h => by simp at h)
    simpa [Nat.bit] using h
  simp [tokOf, this, enc, toB]

def bodyG : StackProg Key BSym :=
  .seq (pushSeq .R (encNats [0, 2, 0])) (.seq (moveTok .W .R) (.seq (popProg .W)
    (.seq (pushProg .R .sep) (pushSeq .R (encNats [1, 1])))))

def bodyI : StackProg Key BSym :=
  .seq (pushSeq .R (encNats [0, 1, 0])) (.seq (moveTok .W .R) (.seq (popProg .W)
    (pushProg .R .sep)))

def bodyJ : StackProg Key BSym :=
  .seq (pushSeq .R (encNats [0, 2, 0])) (.seq (moveTok2 .W .R .S) (.seq (popProg .W)
    (.seq (pushProg .R .sep) (.seq (pushSeq .R (encNats [2])) (.seq (tr1 .S .X)
    (.seq (tr1 .X .R) (pushProg .R .sep)))))))

lemma exec_bodyG (k : ℕ) (rest : List BSym) (s : Store) (hs : s .W = tokOf k ++ .sep :: rest) :
    ExecLe bodyG s (Function.update (Function.update s .W rest) .R
      ((encNats (blkG k)).reverse ++ s .R)) (3 * (tokOf k).length + 40) := by
  have e1 := exec_pushSeq Key.R (encNats [0, 2, 0]) s
  set s1 := Function.update s Key.R ((encNats [0, 2, 0]).reverse ++ s Key.R)
  have e2 := exec_moveTok Key.W Key.R (by decide) (tokOf k) (.sep :: rest) s1 (by simp [s1, hs])
    (tokOf_ne k) (tok_stop rest)
  set s2 := Function.update (Function.update s1 Key.W (BSym.sep :: rest)) Key.R
    ((tokOf k).reverse ++ s1 Key.R)
  have e3 := exec_popE Key.W s2
  set s3 := Function.update s2 Key.W (s2 Key.W).tail
  have e4 := exec_pushE Key.R BSym.sep s3
  set s4 := Function.update s3 Key.R (BSym.sep :: s3 Key.R)
  have e5 := exec_pushSeq Key.R (encNats [1, 1]) s4
  refine ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr ?_).mono ?_
  · funext j; cases j <;> simp [s4, s3, s2, s1, blkG, encNats, encNat_eq, tokOf_zero, tokOf_one,
      tokOf_two]
  · simp [encNats, encNat_eq, tokOf_zero, tokOf_one, tokOf_two] <;> omega

lemma exec_bodyI (k : ℕ) (rest : List BSym) (s : Store) (hs : s .W = tokOf k ++ .sep :: rest) :
    ExecLe bodyI s (Function.update (Function.update s .W rest) .R
      ((encNats (blkI k)).reverse ++ s .R)) (3 * (tokOf k).length + 40) := by
  have e1 := exec_pushSeq Key.R (encNats [0, 1, 0]) s
  set s1 := Function.update s Key.R ((encNats [0, 1, 0]).reverse ++ s Key.R)
  have e2 := exec_moveTok Key.W Key.R (by decide) (tokOf k) (.sep :: rest) s1 (by simp [s1, hs])
    (tokOf_ne k) (tok_stop rest)
  set s2 := Function.update (Function.update s1 Key.W (BSym.sep :: rest)) Key.R
    ((tokOf k).reverse ++ s1 Key.R)
  have e3 := exec_popE Key.W s2
  set s3 := Function.update s2 Key.W (s2 Key.W).tail
  have e4 := exec_pushE Key.R BSym.sep s3
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · funext j; cases j <;> simp [s3, s2, s1, blkI, encNats, encNat_eq, tokOf_zero, tokOf_one,
      tokOf_two]
  · simp [encNats, encNat_eq, tokOf_zero, tokOf_one, tokOf_two] <;> omega

lemma exec_bodyJ (k : ℕ) (rest : List BSym) (s : Store) (hs : s .W = tokOf k ++ .sep :: rest)
    (hS : s .S = []) (hX : s .X = []) :
    ExecLe bodyJ s (Function.update (Function.update s .W rest) .R
      ((encNats (blkJ k)).reverse ++ s .R)) (9 * (tokOf k).length + 40) := by
  have e1 := exec_pushSeq Key.R (encNats [0, 2, 0]) s
  set s1 := Function.update s Key.R ((encNats [0, 2, 0]).reverse ++ s Key.R)
  have e2 := exec_moveTok2 Key.W Key.R Key.S (by decide) (by decide) (tokOf k) (.sep :: rest) s1
    (by simp [s1, hs]) (tokOf_ne k) (tok_stop rest)
  set s2 : Store := fun j => if j = Key.W then BSym.sep :: rest else
      if j = Key.R ∨ j = Key.S then (tokOf k).reverse ++ s1 j else s1 j
  have e3 := exec_popE Key.W s2
  set s3 := Function.update s2 Key.W (s2 Key.W).tail
  have e4 := exec_pushE Key.R BSym.sep s3
  set s4 := Function.update s3 Key.R (BSym.sep :: s3 Key.R)
  have e5 := exec_pushSeq Key.R (encNats [2]) s4
  set s5 := Function.update s4 Key.R ((encNats [2]).reverse ++ s4 Key.R)
  have e6 := exec_tr1 Key.S Key.X (by decide) s5
  set s6 := Function.update (Function.update s5 Key.S []) Key.X ((s5 Key.S).reverse ++ s5 Key.X)
  have e7 := exec_tr1 Key.X Key.R (by decide) s6
  set s7 := Function.update (Function.update s6 Key.X []) Key.R ((s6 Key.X).reverse ++ s6 Key.R)
  have e8 := exec_pushE Key.R BSym.sep s7
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).congr ?_).mono ?_
  · funext j; cases j <;> simp [s7, s6, s5, s4, s3, s2, s1, blkJ, encNats, encNat_eq, tokOf_zero,
      tokOf_one, tokOf_two, hS, hX]
  · simp [s6, s5, s4, s3, s2, s1, encNats, encNat_eq, tokOf_zero, tokOf_one, tokOf_two, hS, hX]
      <;> omega

/-! ### scripts -/

inductive JK | G | I | J

inductive Ins
  | consts (cs : List ℕ)
  | num (base : Option Key) (α : Bool) (c : ℕ) (dbl : Bool)
  | jobs (j : JK)
  | grid (cr cc : ℕ)
  | line (c : ℕ)

def JK.body : JK → StackProg Key BSym
  | .G => bodyG
  | .I => bodyI
  | .J => bodyJ

def JK.blk : JK → ℕ → List ℕ
  | .G => blkG
  | .I => blkI
  | .J => blkJ

def Ins.prog : Ins → StackProg Key BSym
  | .consts cs => pushSeq .R (encNats cs)
  | .num base α c dbl => numP base α c dbl
  | .jobs j => jobsP j.body
  | .grid cr cc => gridP cr cc
  | .line c => lineP c

def Ins.emit (a : List ℕ) (b t vA vD : ℕ) : Ins → List ℕ
  | .consts cs => cs
  | .num base α c dbl => [if dbl then 2 * (baseVal b vA vD base + ((if α then t else 0) + c))
      else baseVal b vA vD base + ((if α then t else 0) + c)]
  | .jobs j => (a.map j.blk).flatten
  | .grid cr cc => List.replicate ((t + cr) * (t + cc)) 0
  | .line c => List.replicate (t + c) 0

def Ins.OK (b t vA vD : ℕ) : Ins → Prop
  | .consts cs => (encNats cs).length ≤ 30
  | .num base α c dbl => BaseOK base ∧ c ≤ 2 ∧
      (dbl = true → 0 < baseVal b vA vD base + ((if α then t else 0) + c))
  | .jobs _ => True
  | .grid cr cc => cr ≤ 2 ∧ cc ≤ 2
  | .line c => c ≤ 2

lemma exec_ins (a : List ℕ) (b t vA vD L : ℕ) (R' : List BSym) (hL : LenOK a b t vA vD L)
    (hpos : ∀ v ∈ a, 0 < v) (i : Ins) (hi : i.OK b t vA vD) :
    ExecLe i.prog (baseStore a b t vA vD R')
      (baseStore a b t vA vD ((encNats (i.emit a b t vA vD)).reverse ++ R')) (100 * (L + 3) ^ 2) := by
  cases i with
  | consts cs =>
    refine (exec_consts a b t vA vD R' cs).mono ?_
    have : (encNats cs).length ≤ 30 := hi
    have : 9 ≤ (L + 3) ^ 2 := by
      have := Nat.pow_le_pow_left (show 3 ≤ L + 3 by omega) 2
      simpa using this
    omega
  | num base α c dbl =>
    obtain ⟨h1, h2, h3⟩ := hi
    have e := exec_num a b t vA vD L R' hL base h1 α c h2 dbl h3
    refine e.congr ?_
    simp [Ins.emit, encNats]
  | jobs j =>
    have hlen : a.length ≤ L := le_trans (len_code_ge a) hL.ha
    have htok : ∀ k ∈ a, (tokOf k).length ≤ L := fun k hk => le_trans (len_tok_le_code hk) hL.ha
    have key : ExecLe (jobsP j.body) (baseStore a b t vA vD R')
        (baseStore a b t vA vD ((encNats ((a.map j.blk).flatten)).reverse ++ R'))
        (6 * (encNats a).length + 3 + (a.length * (9 * L + 40 + 2) + 1) + 1) := by
      apply exec_jobs a b t vA vD R' hpos j.body j.blk
      intro k rest s hk hs hS hX
      have hkL := htok k hk
      cases j with
      | G => exact (exec_bodyG k rest s hs).mono (by omega)
      | I => exact (exec_bodyI k rest s hs).mono (by omega)
      | J => exact (exec_bodyJ k rest s hs hS hX).mono (by omega)
    refine key.mono ?_
    have := hL.ha
    have : a.length * (9 * L + 40 + 2) ≤ L * (9 * L + 42) := Nat.mul_le_mul_right _ hlen
    nlinarith
  | grid cr cc => exact exec_grid a b t vA vD L R' hL cr cc hi.1 hi.2
  | line c => exact exec_line a b t vA vD L R' hL c hi

def script : List Ins → StackProg Key BSym
  | [] => skipP
  | i :: l => .seq i.prog (script l)

lemma exec_script (a : List ℕ) (b t vA vD L : ℕ) (hL : LenOK a b t vA vD L)
    (hpos : ∀ v ∈ a, 0 < v) : ∀ (l : List Ins) (R' : List BSym), (∀ i ∈ l, i.OK b t vA vD) →
    ExecLe (script l) (baseStore a b t vA vD R')
      (baseStore a b t vA vD ((encNats (l.flatMap (Ins.emit a b t vA vD))).reverse ++ R'))
      (l.length * (100 * (L + 3) ^ 2 + 1) + 1)
  | [], R', _ => by simpa [script, encNats] using exec_skip (baseStore a b t vA vD R')
  | i :: l, R', h => by
    have e1 := exec_ins a b t vA vD L R' hL hpos i (h i (by simp))
    have e2 := exec_script a b t vA vD L hL hpos l ((encNats (i.emit a b t vA vD)).reverse ++ R')
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

lemma len_jobs (blk : ℕ → List ℕ) (hb : ∀ x, (encNats (blk x)).length ≤ 10 * (encNat x).length) :
    ∀ a : List ℕ, (encNats (a.map blk).flatten).length ≤ 10 * (encNats a).length
  | [] => by simp [encNats]
  | x :: a => by
    have h1 := hb x
    have h2 := len_jobs blk hb a
    simp only [List.map_cons, List.flatten_cons, encNats_append, List.length_append]
    rw [show encNats (x :: a) = encNat x ++ encNats a by simp [encNats]]
    simp only [List.length_append]; omega

lemma len_emit (a : List ℕ) (b t vA vD L : ℕ) (hL : LenOK a b t vA vD L) (i : Ins)
    (hi : i.OK b t vA vD) : (encNats (i.emit a b t vA vD)).length ≤ 30 * (L + 3) ^ 2 := by
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
    generalize baseVal b vA vD base + ((if α then t else 0) + c) = v0 at hl h3 ⊢
    cases dbl
    · simp [encNats, len_encNat]; omega
    · simp only [if_true]
      rw [show encNats [2 * v0] = encNat (2 * v0) by simp [encNats], len_encNat,
        tokOf_double (h3 rfl)]
      simp; omega
  | jobs j =>
    simp only [Ins.emit]
    have : (encNats (a.map j.blk).flatten).length ≤ 10 * (encNats a).length := by
      apply len_jobs
      intro x
      cases j <;> simp [JK.blk, blkG, blkI, blkJ, encNats, len_encNat, tokOf_zero, tokOf_one,
        tokOf_two] <;> omega
    have := hL.ha
    omega
  | grid cr cc =>
    obtain ⟨hr, hc⟩ := hi
    simp only [Ins.emit, encNats_rep_zero, List.length_replicate]
    have := hL.ht
    have : (t + cr) * (t + cc) ≤ (L + 3) * (L + 3) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  | line c =>
    simp only [Ins.emit, encNats_rep_zero, List.length_replicate]
    have := hL.ht
    have : t + c ≤ L + 3 := by have := hi; simp only [Ins.OK] at this; omega
    omega

lemma len_script (a : List ℕ) (b t vA vD L : ℕ) (hL : LenOK a b t vA vD L) :
    ∀ l : List Ins, (∀ i ∈ l, i.OK b t vA vD) →
      (encNats (l.flatMap (Ins.emit a b t vA vD))).length ≤ l.length * (30 * (L + 3) ^ 2)
  | [], _ => by simp [encNats]
  | i :: l, h => by
    have h1 := len_emit a b t vA vD L hL i (h i (by simp))
    have h2 := len_script a b t vA vD L hL l (fun j hj => h j (by simp [hj]))
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

def tailP (scr : List Ins) (m : ℕ) : StackProg Key BSym :=
  .branch (fun h => (h .car).isSome) skipP (.seq (stripZ .tmp)
    (.branch (fun h => (h .tmp).isSome) (.seq (tr1 .tmp .D) (.seq (script scr) (tr1 .R .out)))
      (pushSeq .out (encNats [0, m, 0]).reverse)))

def outProg (scr : List Ins) (m : ℕ) : StackProg Key BSym := wrap (.seq preO (tailP scr m))

lemma exec_tail (scr : List Ins) (m : ℕ) (code : List ℕ → ℕ → ℕ → List ℕ)
    (hscr : ∀ (a : List ℕ) (b : ℕ), 0 < b → b < a.sum → (∀ v ∈ a, 0 < v) →
      (∀ i ∈ scr, i.OK b a.length a.sum (a.sum - b)) ∧
      scr.flatMap (Ins.emit a b a.length a.sum (a.sum - b)) = code a b a.length)
    (hm : (encNats [0, m, 0]).length ≤ 10)
    (a : List ℕ) (b : ℕ) (hb : 0 < b) (hpos : ∀ v ∈ a, 0 < v) (L : ℕ)
    (hLa : (encNats a).length ≤ L) (hLb : (tokOf b).length ≤ L) :
    ∃ t : Store, ExecLe (tailP scr m) (P1 a b) t
      (scr.length * (200 * (L + 3) ^ 2 + 1) + 6 * L + 30) ∧
      t .out = (if b < a.sum then encNats (code a b a.length)
        else if b = a.sum then encNats [0, m, 0] else []) := by
  have hLA : (tokOf a.sum).length ≤ L := le_trans (len_tokOf_le a.sum a le_rfl) hLa
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
      have e2 := exec_pushSeq Key.out (encNats [0, m, 0]).reverse s1
      refine ⟨_, (ExecLe.brF (by simp [P1, subR, hnb, carS])
        (e1.seq (ExecLe.brF (by simp [s1, hz, enc]) e2))).mono ?_, ?_⟩
      · simp only [List.length_reverse]; nlinarith
      · simp [s1, P1]; rw [if_neg (by omega), if_pos hbA]
    · -- b < A
      have hbA : b < a.sum := by omega
      obtain ⟨hok, hem⟩ := hscr a b hb hbA hpos
      have e2 := exec_tr1 Key.tmp Key.D (by decide) s1
      have hbase : Function.update (Function.update s1 Key.tmp []) Key.D
          ((s1 Key.tmp).reverse ++ s1 Key.D) = baseStore a b a.length a.sum (a.sum - b) [] := by
        funext k; cases k <;> simp [s1, P1, baseStore, hnb, subR, carS, tokOf] <;> simp_all [subR]
      rw [hbase] at e2
      have hLD : (tokOf (a.sum - b)).length ≤ L := by
        refine le_trans ?_ hLA
        simp only [tokOf, enc, List.length_map]
        rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size (by omega)
      have hLL : LenOK a b a.length a.sum (a.sum - b) L :=
        ⟨hLa, hLb, hLA, hLD, le_trans (len_code_ge a) hLa⟩
      have e3 := exec_script a b a.length a.sum (a.sum - b) L hLL hpos scr [] hok
      have e4 := exec_tr1 Key.R Key.out (by decide) (baseStore a b a.length a.sum (a.sum - b)
        ((encNats (scr.flatMap (Ins.emit a b a.length a.sum (a.sum - b)))).reverse ++ []))
      have hR := len_script a b a.length a.sum (a.sum - b) L hLL scr hok
      refine ⟨_, (ExecLe.brF (by simp [P1, subR, hnb, carS])
        (e1.seq (ExecLe.brT (by
          simp only [s1, Function.update_self]
          have := head_rev_bits (a.sum - b)
          obtain ⟨d, hd⟩ := tok_split _ hz
          simp [show enc (Nat.bits (a.sum - b)) = tokOf (a.sum - b) from rfl, hd])
          (e2.seq (e3.seq e4))))).mono ?_, ?_⟩
      · simp only [baseStore, List.append_nil, List.length_reverse]
        simp [s1, enc] at hLb ⊢
        simp [tokOf, enc] at hLD
        generalize (L + 3) ^ 2 = Q at hR ⊢
        nlinarith [hR]
      · simp [baseStore, hem, hbA]

lemma absorb2 (L : ℕ) : 10000 * (L + 3) ^ 2 ≤ L ^ 1000000 + 1000000 := by
  rcases Nat.lt_or_ge L 2 with h | h
  · interval_cases L <;> norm_num
  · have h1 : (L + 3) ^ 2 ≤ (3 * L) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (2 : ℕ) ^ 17 ≤ L ^ 17 := Nat.pow_le_pow_left h 17
    have h3 : L ^ 19 ≤ L ^ 1000000 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : (3 * L) ^ 2 = 9 * L ^ 2 := by ring
    have h5 : L ^ 19 = L ^ 2 * L ^ 17 := by ring
    have h6 : 10000 * (9 * L ^ 2) ≤ L ^ 2 * L ^ 17 := by
      have : 10000 * 9 ≤ L ^ 17 := le_trans (by norm_num) h2
      nlinarith [Nat.zero_le (L ^ 2)]
    omega

theorem out_poly (scr : List Ins) (m : ℕ) (code : List ℕ → ℕ → ℕ → List ℕ)
    (hscr : ∀ (a : List ℕ) (b : ℕ), 0 < b → b < a.sum → (∀ v ∈ a, 0 < v) →
      (∀ i ∈ scr, i.OK b a.length a.sum (a.sum - b)) ∧
      scr.flatMap (Ins.emit a b a.length a.sum (a.sum - b)) = code a b a.length)
    (hm : (encNats [0, m, 0]).length ≤ 10) (hlen : scr.length ≤ 20) :
    PolyTimeComputable (outSpec code m) := by
  apply stack_program_polytime (outProg scr m) Key.inp Key.out (outSpec code m) 1000000
  intro w
  have hab := absorb2 w.length
  have hsq : w.length ≤ (w.length + 3) ^ 2 := by
    calc w.length ≤ w.length + 3 := by omega
      _ ≤ (w.length + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
  by_cases hv : vrun w = (false, false, false)
  · obtain ⟨l, hl⟩ := (vrun_iff w).1 hv
    obtain ⟨b, a, rfl⟩ := List.exists_cons_of_ne_nil hl.1
    have hpa : ∀ v ∈ a, 0 < v := fun v hv => hl.2.1 v (by simp [hv])
    have hb : 0 < b := hl.2.1 b (by simp)
    have hw : w = tokOf b ++ .sep :: encNats a := by rw [hl.2.2, encNats_cons]
    have hLa : (encNats a).length ≤ w.length := by rw [hw]; simp; omega
    have hLb : (tokOf b).length ≤ w.length := by rw [hw]; simp
    obtain ⟨t, et, ht⟩ := exec_tail scr m code hscr hm a b hb hpa w.length hLa hLb
    have e0 := exec_preO a b
    rw [← hl.2.2] at e0
    obtain ⟨n, hn, e⟩ := exec_wrap_valid _ w t _ hv (e0.seq et)
    refine ⟨t, n, ?_, e, ?_⟩
    · have : scr.length * (200 * (w.length + 3) ^ 2 + 1) ≤ 20 * (200 * (w.length + 3) ^ 2 + 1) :=
        Nat.mul_le_mul_right _ hlen
      omega
    · rw [ht, outSpec_some code m hl]
  · obtain ⟨m', hm', e'⟩ := exec_wrap_invalid (.seq preO (tailP scr m)) w hv
    refine ⟨valStore w, m', by omega, e', ?_⟩
    have hn : ¬ ∃ l, PosCode w l := fun h => hv ((vrun_iff w).2 h)
    simp [valStore, outSpec_none code m hn]

end GHIK



set_option autoImplicit false

namespace GHIK
open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Shops

def scriptG : List Ins :=
  [.num none true 1 false, .consts [2], .jobs .G, .num (some .B) false 0 false,
    .consts [2, 0, 1, 1], .num (some .D) false 0 false, .grid 1 1, .num (some .A) true 0 false]

def scriptH : List Ins :=
  [.num none true 2 false, .consts [2], .jobs .G, .consts [0, 2, 0, 1, 1],
    .num (some .B) false 0 false, .consts [0, 2, 0, 1, 1], .num (some .D) false 0 false,
    .grid 0 2, .line 1, .consts [1], .line 2, .num (some .A) true 1 false]

def scriptI : List Ins :=
  [.num none true 1 false, .consts [2], .jobs .I, .consts [0, 3, 1], .num (some .B) false 0 false,
    .consts [0, 1, 1], .num (some .D) false 0 false, .grid 1 1, .num (some .A) false 1 false]

def scriptJ : List Ins :=
  [.num none true 2 false, .consts [3], .jobs .J, .consts [0, 2, 0], .num (some .B) false 0 false,
    .consts [1], .num (some .D) false 0 true, .consts [0, 2, 1], .num (some .B) false 0 true,
    .consts [2], .num (some .D) false 0 false, .grid 2 2, .num (some .A) false 0 true]

lemma polyG : PolyTimeComputable (outSpec codeG 2) := by
  apply out_poly scriptG 2 codeG _ (by simp [encNats, encNat_eq, tokOf_zero, tokOf_two]) (by decide)
  intro a b hb hbA hpos
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [scriptG, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Ins.OK, BaseOK, encNats, encNat_eq, tokOf_zero, tokOf_one, tokOf_two]
  · simp [scriptG, Ins.emit, baseVal, JK.blk, codeG]

lemma polyH : PolyTimeComputable (outSpec codeH 2) := by
  apply out_poly scriptH 2 codeH _ (by simp [encNats, encNat_eq, tokOf_zero, tokOf_two]) (by decide)
  intro a b hb hbA hpos
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [scriptH, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Ins.OK, BaseOK, encNats, encNat_eq, tokOf_zero, tokOf_one, tokOf_two]
  · simp [scriptH, Ins.emit, baseVal, JK.blk, codeH, List.replicate_add, Nat.add_assoc]

lemma polyI : PolyTimeComputable (outSpec codeI 2) := by
  apply out_poly scriptI 2 codeI _ (by simp [encNats, encNat_eq, tokOf_zero, tokOf_two]) (by decide)
  intro a b hb hbA hpos
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [scriptI, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Ins.OK, BaseOK, encNats, encNat_eq, tokOf_zero, tokOf_one, tokOf_two, tokOf_three]
  · simp [scriptI, Ins.emit, baseVal, JK.blk, codeI]

lemma polyJ : PolyTimeComputable (outSpec codeJ 3) := by
  apply out_poly scriptJ 3 codeJ _ (by simp [encNats, encNat_eq, tokOf_zero, tokOf_three])
    (by decide)
  intro a b hb hbA hpos
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [scriptJ, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Ins.OK, BaseOK, encNats, encNat_eq, tokOf_zero, tokOf_one, tokOf_two, tokOf_three,
        baseVal] <;> omega
  · simp [scriptJ, Ins.emit, baseVal, JK.blk, codeJ]

end GHIK

open CookPvsNP ProjSchedTW.Complexity SchedComplexity.Shops in
theorem solution :
    (∃ fG : List BSym → List BSym, PolyTimeComputable fG ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrG a b).HasScheduleLE (yG a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fG x ∈ langFlowRn) ∧
    (∃ fH : List BSym → List BSym, PolyTimeComputable fH ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrH a b).HasScheduleLE (yH a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fH x ∈ langFlowTree) ∧
    (∃ fI : List BSym → List BSym, PolyTimeComputable fI ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrI a b).HasScheduleLE (yI a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fI x ∈ langJob2Ops3) ∧
    (∃ fJ : List BSym → List BSym, PolyTimeComputable fJ ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrJ a b).HasScheduleLE (yJ a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fJ x ∈ langJob3Ops2) :=
  ⟨⟨GHIK.outSpec GHIK.codeG 2 ∘ GHIK.scaleSpec,
      polyTimeComputable_comp _ _ GHIK.scale_poly GHIK.polyG, GHIK.correctG⟩,
    ⟨GHIK.outSpec GHIK.codeH 2 ∘ GHIK.scaleSpec,
      polyTimeComputable_comp _ _ GHIK.scale_poly GHIK.polyH, GHIK.correctH⟩,
    ⟨GHIK.outSpec GHIK.codeI 2, GHIK.polyI, GHIK.correctI⟩,
    ⟨GHIK.outSpec GHIK.codeJ 3, GHIK.polyJ, GHIK.correctJ⟩⟩


