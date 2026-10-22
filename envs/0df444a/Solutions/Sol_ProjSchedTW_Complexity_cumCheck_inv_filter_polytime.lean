-- Prove2me | solution 1 for ProjSchedTW.Complexity.cumCheck_inv_filter_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:42:30.627994+00:00
-- url     : https://prove2.me/submissions/90938f89-52eb-46ec-92b8-de2b75aead81

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false
set_option linter.all false

/-! Shared stack library for the d0bf0960 checker children (D0bfL).
Part 1: a generic one-pass Mealy scan loop, and the shape DFA for
`(encInts c).map ι1 ++ none :: (encNats d).map ι2`. -/

open CookPvsNP ProjSchedTW.Complexity

namespace D0bfL

/-! ## Generic Mealy scan -/

section Scan
variable {K A : Type} [DecidableEq K]

def scanAct (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A)
    (h : K → Option A) (k : K) : StackAct A :=
  match h ki with
  | none => .keep
  | some a =>
    if k = ki then .pop else if k = st then .push (δ (h st) a)
    else match out k (h st) a with
      | some b => .push b
      | none => .keep

def scanProg (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    StackProg K A :=
  .loop (fun h => (h ki).isSome) (.act (scanAct ki st δ out))

def scanStep (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A)
    (s : K → List A) (a : A) : K → List A := fun k =>
  if k = ki then (s ki).tail else if k = st then δ (s st).head? a :: s st
  else (out k (s st).head? a).toList ++ s k

def scanRun (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    List A → (K → List A) → (K → List A)
  | [], s => s
  | a :: l, s => scanRun ki st δ out l (scanStep ki st δ out s a)

lemma applyAct_scan (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A)
    (s : K → List A) (a : A) (l : List A) (hs : s ki = a :: l) :
    StackProg.applyAct (scanAct ki st δ out) s = scanStep ki st δ out s a := by
  funext k
  simp only [StackProg.applyAct, scanAct, scanStep, hs, List.head?_cons]
  by_cases h1 : k = ki
  · subst h1; simp [StackAct.apply, hs]
  · by_cases h2 : k = st
    · subst h2; simp [h1, StackAct.apply]
    · simp only [h1, h2, if_false]
      cases out k (s st).head? a <;> simp [StackAct.apply]

lemma exec_scan (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    ∀ (l : List A) (s : K → List A), s ki = l →
      (scanProg ki st δ out).Exec s (scanRun ki st δ out l s) (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro s hs
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons a l ih =>
    intro s hs
    have h1 := StackProg.Exec.act (scanAct ki st δ out) s
    rw [applyAct_scan ki st δ out s a l hs] at h1
    have h2 := ih (scanStep ki st δ out s a) (by simp [scanStep, hs])
    have h3 := StackProg.Exec.loopTrue (test := fun h => (h ki).isSome) (by simp [hs]) h1 h2
    simp only [scanRun, List.length_cons]
    have e : 3 * (l.length + 1) + 1 = 1 + 1 + 1 + (3 * l.length + 1) := by ring
    rw [e]; exact h3

/-- the state trace: `runQ q l` is the top of the state stack after scanning `l` from top `q`. -/
def runQ (δ : Option A → A → A) : Option A → List A → Option A
  | q, [] => q
  | q, a :: l => runQ δ (some (δ q a)) l

/-- what a non-state stack `k` receives (in stack order) while scanning `l` from top `q`. -/
def emitR (δ : Option A → A → A) (out : K → Option A → A → Option A) (k : K) :
    Option A → List A → List A
  | _, [] => []
  | q, a :: l => emitR δ out k (some (δ q a)) l ++ (out k q a).toList

lemma scanRun_ki (ki st : K) (δ : Option A → A → A) (out : K → Option A → A → Option A) :
    ∀ (l : List A) (s : K → List A), s ki = l → scanRun ki st δ out l s ki = [] := by
  intro l
  induction l with
  | nil => intro s hs; simpa [scanRun] using hs
  | cons a l ih => intro s hs; exact ih _ (by simp [scanStep, hs])

lemma scanRun_st (ki st : K) (hks : ki ≠ st) (δ : Option A → A → A)
    (out : K → Option A → A → Option A) :
    ∀ (l : List A) (s : K → List A), (scanRun ki st δ out l s st).head? = runQ δ (s st).head? l := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [scanRun, ih]
    simp [scanStep, Ne.symm hks, runQ]

lemma scanRun_other (ki st : K) (hks : ki ≠ st) (δ : Option A → A → A)
    (out : K → Option A → A → Option A) (k : K) (hk1 : k ≠ ki) (hk2 : k ≠ st) :
    ∀ (l : List A) (s : K → List A),
      scanRun ki st δ out l s k = emitR δ out k (s st).head? l ++ s k := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [scanRun, ih]
    simp [scanStep, hk1, hk2, Ne.symm hks, emitR]

end Scan

/-! ## The shape DFA -/

abbrev A := Option (BSym ⊕ BSym)

def ι1 (b : BSym) : A := some (Sum.inl b)
def ι2 (b : BSym) : A := some (Sum.inr b)
def dg (b : Bool) : BSym := if b then BSym.one else BSym.zero

/-- the input shape: an integer list, a `none` separator, a natural list. -/
def Ew (c : List ℤ) (d : List ℕ) : List A :=
  (encInts c).map ι1 ++ none :: (encNats d).map ι2

inductive DS
  | S0 | M | Z | O | T0 | TZ | TO | X
  deriving DecidableEq

open DS

def dstep : DS → A → DS
  | S0, some (.inl .minus) => M
  | S0, some (.inl .sep) => S0
  | O, some (.inl .sep) => S0
  | S0, none => T0
  | S0, some (.inl .zero) => Z
  | M, some (.inl .zero) => Z
  | Z, some (.inl .zero) => Z
  | O, some (.inl .zero) => Z
  | S0, some (.inl .one) => O
  | M, some (.inl .one) => O
  | Z, some (.inl .one) => O
  | O, some (.inl .one) => O
  | T0, some (.inr .zero) => TZ
  | TZ, some (.inr .zero) => TZ
  | TO, some (.inr .zero) => TZ
  | T0, some (.inr .one) => TO
  | TZ, some (.inr .one) => TO
  | TO, some (.inr .one) => TO
  | T0, some (.inr .sep) => T0
  | TO, some (.inr .sep) => T0
  | _, _ => X

def runD (q : DS) (l : List A) : DS := l.foldl dstep q

@[simp] lemma runD_nil (q : DS) : runD q [] = q := rfl
@[simp] lemma runD_cons (q : DS) (a : A) (l : List A) : runD q (a :: l) = runD (dstep q a) l := rfl
lemma runD_append (q : DS) (l l' : List A) : runD q (l ++ l') = runD (runD q l) l' := by
  simp [runD, List.foldl_append]

@[simp] lemma runD_X : ∀ l : List A, runD X l = X := by
  intro l; induction l with
  | nil => rfl
  | cons a l ih => rw [runD_cons]; cases a <;> exact ih

/-! ### canonical bit lists -/

lemma bits_getLast : ∀ k : ℕ, k ≠ 0 → (Nat.bits k).getLast? = some true := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro h; exact absurd rfl h
  | bit b n hn ih =>
    intro _
    rw [Nat.bits_append_bit _ _ hn]
    by_cases h0 : n = 0
    · subst h0; have := hn rfl; subst this; simp
    · have := ih h0
      rw [List.getLast?_cons]
      simp [this]

lemma canon_bits : ∀ bs : List Bool, (bs = [] ∨ bs.getLast? = some true) → ∃ k, Nat.bits k = bs := by
  intro bs
  induction bs with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons b bs ih =>
    intro h
    rcases bs with _ | ⟨b', bs'⟩
    · have hb : b = true := by simpa using h
      subst hb
      exact ⟨1, by
        have := Nat.bits_append_bit 0 true (by simp)
        simpa using this⟩
    · have hl : (b' :: bs').getLast? = some true := by
        rcases h with h | h
        · simp at h
        · rw [List.getLast?_cons_cons] at h; exact h
      obtain ⟨k, hk⟩ := ih (Or.inr hl)
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk
      refine ⟨Nat.bit b k, ?_⟩
      rw [Nat.bits_append_bit _ _ (fun h => absurd h hk0), hk]

/-! ### the natural-number part -/

lemma dpart_digits : ∀ (l : List A) (q : DS), (q = TZ ∨ q = TO) → runD q l = T0 →
    ∃ (bs : List Bool) (rest : List A), l = bs.map (ι2 ∘ dg) ++ ι2 .sep :: rest ∧
      (bs.getLast? = some true ∨ (bs = [] ∧ q = TO)) ∧ runD T0 rest = T0 := by
  intro l
  induction l with
  | nil => intro q hq h; rcases hq with rfl | rfl <;> simp at h
  | cons a l ih =>
    intro q hq h
    rw [runD_cons] at h
    rcases a with _ | (b | b)
    · rcases hq with rfl | rfl <;> simp [dstep] at h
    · rcases hq with rfl | rfl <;> cases b <;> simp [dstep] at h
    · cases b with
      | zero =>
        have hd : dstep q (some (.inr .zero)) = TZ := by rcases hq with rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih TZ (Or.inl rfl) h
        refine ⟨false :: bs, rest, by simp [h1, ι2, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨_, h2⟩
        · rw [List.getLast?_cons]; simp [h2]
        · exact absurd h2 (by decide)
      | one =>
        have hd : dstep q (some (.inr .one)) = TO := by rcases hq with rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih TO (Or.inr rfl) h
        refine ⟨true :: bs, rest, by simp [h1, ι2, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨h2, _⟩
        · rw [List.getLast?_cons]; simp [h2]
        · subst h2; simp
      | minus => rcases hq with rfl | rfl <;> simp [dstep] at h
      | sep =>
        rcases hq with rfl | rfl
        · simp [dstep] at h
        · exact ⟨[], l, rfl, Or.inr ⟨rfl, rfl⟩, by simpa [dstep] using h⟩

lemma encNats_cons (k : ℕ) (d : List ℕ) : encNats (k :: d) = encNat k ++ encNats d := by
  simp [encNats]

lemma encInts_cons (z : ℤ) (c : List ℤ) : encInts (z :: c) = encInt z ++ encInts c := by
  simp [encInts]

lemma dpart_sound : ∀ (L : ℕ) (l : List A), l.length ≤ L → runD T0 l = T0 →
    ∃ d : List ℕ, l = (encNats d).map ι2 := by
  intro L
  induction L with
  | zero =>
    intro l hl _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by simp [this, encNats]⟩
  | succ L ih =>
    intro l hl h
    rcases l with _ | ⟨a, l⟩
    · exact ⟨[], by simp [encNats]⟩
    rw [runD_cons] at h
    simp only [List.length_cons] at hl
    rcases a with _ | (b | b)
    · simp [dstep] at h
    · cases b <;> simp [dstep] at h
    · cases b with
      | sep =>
        obtain ⟨d, hd⟩ := ih l (by omega) (by simpa [dstep] using h)
        exact ⟨0 :: d, by simp [hd, encNats_cons, encNat, ι2]⟩
      | minus => simp [dstep] at h
      | zero =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := dpart_digits l TZ (Or.inl rfl) (by simpa [dstep] using h)
        have hc : (false :: bs) = [] ∨ (false :: bs).getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · right; rw [List.getLast?_cons]; simp [h2]
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨d, hd⟩ := ih rest hlen h3
        refine ⟨k :: d, ?_⟩
        rw [encNats_cons, List.map_append, ← hd, encNat, hk, h1]
        simp [ι2, dg]
      | one =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := dpart_digits l TO (Or.inr rfl) (by simpa [dstep] using h)
        have hc : (true :: bs) = [] ∨ (true :: bs).getLast? = some true := by
          right
          rcases h2 with h2 | ⟨h2, _⟩
          · rw [List.getLast?_cons]; simp [h2]
          · subst h2; simp
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨d, hd⟩ := ih rest hlen h3
        refine ⟨k :: d, ?_⟩
        rw [encNats_cons, List.map_append, ← hd, encNat, hk, h1]
        simp [ι2, dg]

lemma dpart_bits : ∀ (k : ℕ) (q : DS), (q = T0 ∨ q = TZ ∨ q = TO) → k ≠ 0 →
    runD q ((Nat.bits k).map (ι2 ∘ dg)) = TO := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro q _ h; exact absurd rfl h
  | bit b n hn ih =>
    intro q hq _
    rw [Nat.bits_append_bit _ _ hn, List.map_cons, runD_cons]
    by_cases h0 : n = 0
    · subst h0
      have hb := hn rfl; subst hb
      rcases hq with rfl | rfl | rfl <;> rfl
    · apply ih _ _ h0
      rcases hq with rfl | rfl | rfl <;> cases b <;> simp [dstep, ι2, dg]

lemma encNat_dg (k : ℕ) : encNat k = (Nat.bits k).map dg ++ [BSym.sep] := rfl

lemma dpart_complete : ∀ d : List ℕ, runD T0 ((encNats d).map ι2) = T0 := by
  intro d
  induction d with
  | nil => rfl
  | cons k d ih =>
    rw [encNats_cons, List.map_append, runD_append, encNat_dg, List.map_append, runD_append]
    by_cases hk : k = 0
    · subst hk; simpa [ι2, dstep] using ih
    · rw [List.map_map, dpart_bits k T0 (Or.inl rfl) hk]
      simpa [ι2, dstep] using ih

/-! ### the integer part -/

lemma cpart_digits : ∀ (l : List A) (q : DS), (q = M ∨ q = Z ∨ q = O) → runD q l = T0 →
    ∃ (bs : List Bool) (rest : List A), l = bs.map (ι1 ∘ dg) ++ ι1 .sep :: rest ∧
      (bs.getLast? = some true ∨ (bs = [] ∧ q = O)) ∧ runD S0 rest = T0 := by
  intro l
  induction l with
  | nil => intro q hq h; rcases hq with rfl | rfl | rfl <;> simp at h
  | cons a l ih =>
    intro q hq h
    rw [runD_cons] at h
    rcases a with _ | (b | b)
    · rcases hq with rfl | rfl | rfl <;> simp [dstep] at h
    · cases b with
      | zero =>
        have hd : dstep q (some (.inl .zero)) = Z := by rcases hq with rfl | rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih Z (Or.inr (Or.inl rfl)) h
        refine ⟨false :: bs, rest, by simp [h1, ι1, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨_, h2⟩
        · rw [List.getLast?_cons]; simp [h2]
        · exact absurd h2 (by decide)
      | one =>
        have hd : dstep q (some (.inl .one)) = O := by rcases hq with rfl | rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih O (Or.inr (Or.inr rfl)) h
        refine ⟨true :: bs, rest, by simp [h1, ι1, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨h2, _⟩
        · rw [List.getLast?_cons]; simp [h2]
        · subst h2; simp
      | minus => rcases hq with rfl | rfl | rfl <;> simp [dstep] at h
      | sep =>
        rcases hq with rfl | rfl | rfl
        · simp [dstep] at h
        · simp [dstep] at h
        · exact ⟨[], l, rfl, Or.inr ⟨rfl, rfl⟩, by simpa [dstep] using h⟩
    · rcases hq with rfl | rfl | rfl <;> cases b <;> simp [dstep] at h

lemma encInt_neg (k : ℕ) (hk : k ≠ 0) :
    encInt (-(k : ℤ)) = BSym.minus :: ((Nat.bits k).map dg ++ [BSym.sep]) := by
  have h : (-(k : ℤ)) < 0 := by omega
  simp only [encInt, if_pos h, Int.natAbs_neg, Int.natAbs_natCast, List.singleton_append]; rfl

lemma encInt_nat (k : ℕ) : encInt (k : ℤ) = (Nat.bits k).map dg ++ [BSym.sep] := by
  have h : ¬ ((k : ℤ) < 0) := by omega
  simp only [encInt, if_neg h, Int.natAbs_natCast, List.nil_append]; rfl

lemma cpart_sound : ∀ (L : ℕ) (l : List A), l.length ≤ L → runD S0 l = T0 →
    ∃ (c : List ℤ) (d : List ℕ), l = Ew c d := by
  intro L
  induction L with
  | zero =>
    intro l hl h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at h
  | succ L ih =>
    intro l hl h
    rcases l with _ | ⟨a, l⟩
    · simp at h
    rw [runD_cons] at h
    simp only [List.length_cons] at hl
    rcases a with _ | (b | b)
    · obtain ⟨d, hd⟩ := dpart_sound l.length l le_rfl (by simpa [dstep] using h)
      exact ⟨[], d, by simp [Ew, hd, encInts]⟩
    · cases b with
      | sep =>
        obtain ⟨c, d, hcd⟩ := ih l (by omega) (by simpa [dstep] using h)
        exact ⟨0 :: c, d, by simp [hcd, Ew, encInts_cons, encInt, encNat, ι1]⟩
      | minus =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l M (Or.inl rfl) (by simpa [dstep] using h)
        have hl2 : bs.getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · exact h2
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ (Or.inr hl2)
        have hk0 : k ≠ 0 := by rintro rfl; simp at hk; subst hk; simp at hl2
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨-(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [Ew, encInts_cons, encInt_neg k hk0, hk]
        simp [ι1, dg]
      | zero =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l Z (Or.inr (Or.inl rfl))
          (by simpa [dstep] using h)
        have hc : (false :: bs) = [] ∨ (false :: bs).getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · right; rw [List.getLast?_cons]; simp [h2]
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [Ew, encInts_cons, encInt_nat k, hk]
        simp [ι1, dg]
      | one =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l O (Or.inr (Or.inr rfl))
          (by simpa [dstep] using h)
        have hc : (true :: bs) = [] ∨ (true :: bs).getLast? = some true := by
          right
          rcases h2 with h2 | ⟨h2, _⟩
          · rw [List.getLast?_cons]; simp [h2]
          · subst h2; simp
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [Ew, encInts_cons, encInt_nat k, hk]
        simp [ι1, dg]
    · cases b <;> simp [dstep] at h

lemma cpart_bits : ∀ (k : ℕ) (q : DS), (q = S0 ∨ q = M ∨ q = Z ∨ q = O) → k ≠ 0 →
    runD q ((Nat.bits k).map (ι1 ∘ dg)) = O := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro q _ h; exact absurd rfl h
  | bit b n hn ih =>
    intro q hq _
    rw [Nat.bits_append_bit _ _ hn, List.map_cons, runD_cons]
    by_cases h0 : n = 0
    · subst h0
      have hb := hn rfl; subst hb
      rcases hq with rfl | rfl | rfl | rfl <;> rfl
    · apply ih _ _ h0
      rcases hq with rfl | rfl | rfl | rfl <;> cases b <;> simp [dstep, ι1, dg]

lemma cpart_int (z : ℤ) : runD S0 ((encInt z).map ι1) = S0 := by
  rcases lt_or_ge z 0 with hz | hz
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨z.natAbs, by omega⟩
    have hk : k ≠ 0 := by omega
    rw [encInt_neg k hk, List.map_cons, runD_cons, List.map_append, runD_append, List.map_map,
      show dstep S0 (ι1 .minus) = M from rfl, cpart_bits k M (Or.inr (Or.inl rfl)) hk]
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = (k : ℤ) := ⟨z.natAbs, by omega⟩
    rw [encInt_nat, List.map_append, runD_append, List.map_map]
    by_cases hk : k = 0
    · subst hk; rfl
    · rw [cpart_bits k S0 (Or.inl rfl) hk]; rfl

lemma cpart_complete (c : List ℤ) (d : List ℕ) : runD S0 (Ew c d) = T0 := by
  have hc : ∀ c : List ℤ, runD S0 ((encInts c).map ι1) = S0 := by
    intro c
    induction c with
    | nil => rfl
    | cons z c ih => rw [encInts_cons, List.map_append, runD_append, cpart_int, ih]
  rw [Ew, runD_append, hc, runD_cons]
  exact dpart_complete d

/-- the shape DFA accepts exactly the well-shaped words. -/
theorem runD_iff (u : List A) : runD S0 u = T0 ↔ ∃ (c : List ℤ) (d : List ℕ), u = Ew c d := by
  constructor
  · exact cpart_sound u.length u le_rfl
  · rintro ⟨c, d, rfl⟩; exact cpart_complete c d

/-! ## Generic transfer / copy / halving (ported from P5c6, generic in `K`, `A`) -/

section Basic
variable {K A : Type} [DecidableEq K]

lemma exec_transfer (src : K) (targets : K → Bool) :
    ∀ (l : List A) (s : K → List A), s src = l →
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

lemma exec_copy (src dst scr : K) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (s : K → List A) (hs : s scr = []) :
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

/-- halve stack `U` (any content): one mark on `H` per pair, the parity bit toggles on `P`. -/
def halveAct (U H P : K) (mk : A) (h : K → Option A) (k : K) : StackAct A :=
  if k = U then .pop
  else if k = P then (if (h P).isSome then .pop else .push mk)
  else if k = H then (if (h P).isSome then .push mk else .keep) else .keep

def halveProg (U H P : K) (mk : A) : StackProg K A :=
  .loop (fun h => (h U).isSome) (.act (halveAct U H P mk))

lemma exec_halve (U H P : K) (hUH : U ≠ H) (hUP : U ≠ P) (hHP : H ≠ P) (mk : A) :
    ∀ (L p0 : ℕ) (s : K → List A), (s U).length = L → p0 ≤ 1 → s P = List.replicate p0 mk →
      (halveProg U H P mk).Exec s
        (Function.update (Function.update (Function.update s U []) P
          (List.replicate ((p0 + L) % 2) mk)) H
          (List.replicate ((p0 + L) / 2) mk ++ s H)) (3 * L + 1) := by
  intro L
  induction L with
  | zero =>
    intro p0 s hL hp hP
    have hU : s U = [] := List.eq_nil_of_length_eq_zero hL
    have hpost : Function.update (Function.update (Function.update s U []) P
        (List.replicate ((p0 + 0) % 2) mk)) H (List.replicate ((p0 + 0) / 2) mk ++ s H) = s := by
      have h1 : (p0 + 0) % 2 = p0 := by omega
      have h2 : (p0 + 0) / 2 = 0 := by omega
      rw [h1, h2, ← hP, ← hU]
      funext k
      by_cases k1 : k = H
      · subst k1; simp
      by_cases k2 : k = P
      · subst k2; simp [k1]
      by_cases k3 : k = U
      · subst k3; simp [k1, k2]
      · simp [k1, k2, k3]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simp [hU])
  | succ L ih =>
    intro p0 s hL hp hP
    obtain ⟨a, l, hU⟩ : ∃ a l, s U = a :: l := by
      rcases h : s U with _ | ⟨a, l⟩
      · rw [h] at hL; simp at hL
      · exact ⟨a, l, rfl⟩
    set s1 := StackProg.applyAct (halveAct U H P mk) s with hs1
    have e1U : s1 U = l := by simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hU]
    have hlen : (s1 U).length = L := by rw [e1U]; rw [hU] at hL; simpa using hL
    rcases (show p0 = 0 ∨ p0 = 1 by omega) with rfl | rfl
    · have e1P : s1 P = List.replicate 1 mk := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUP]
      have e1H : s1 H = s H := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUH, hHP]
      have h2 := ih 1 s1 hlen le_rfl e1P
      have hpost : Function.update (Function.update (Function.update s1 U []) P
          (List.replicate ((1 + L) % 2) mk)) H (List.replicate ((1 + L) / 2) mk ++ s1 H) =
          Function.update (Function.update (Function.update s U []) P
          (List.replicate ((0 + (L + 1)) % 2) mk)) H
          (List.replicate ((0 + (L + 1)) / 2) mk ++ s H) := by
        rw [e1H, show (1 + L) % 2 = (0 + (L + 1)) % 2 by omega,
          show (1 + L) / 2 = (0 + (L + 1)) / 2 by omega]
        funext k
        by_cases k1 : k = H
        · subst k1; simp
        by_cases k2 : k = P
        · subst k2; simp [k1]
        by_cases k3 : k = U
        · subst k3; simp [k1, k2]
        · simp [k1, k2, k3, hs1, StackProg.applyAct, halveAct, StackAct.apply]
      rw [← hpost]
      have := StackProg.Exec.loopTrue (test := fun h => (h U).isSome) (by simp [hU])
        (StackProg.Exec.act (halveAct U H P mk) s) h2
      rw [show 3 * (L + 1) + 1 = 1 + 1 + 1 + (3 * L + 1) by ring]; exact this
    · have e1P : s1 P = List.replicate 0 mk := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUP]
      have e1H : s1 H = mk :: s H := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUH, hHP]
      have h2 := ih 0 s1 hlen (by omega) e1P
      have hpost : Function.update (Function.update (Function.update s1 U []) P
          (List.replicate ((0 + L) % 2) mk)) H (List.replicate ((0 + L) / 2) mk ++ s1 H) =
          Function.update (Function.update (Function.update s U []) P
          (List.replicate ((1 + (L + 1)) % 2) mk)) H
          (List.replicate ((1 + (L + 1)) / 2) mk ++ s H) := by
        rw [e1H, show (0 + L) % 2 = (1 + (L + 1)) % 2 by omega,
          show (1 + (L + 1)) / 2 = (0 + L) / 2 + 1 by omega, List.replicate_succ',
          List.append_assoc, List.singleton_append]
        funext k
        by_cases k1 : k = H
        · subst k1; simp
        by_cases k2 : k = P
        · subst k2; simp [k1]
        by_cases k3 : k = U
        · subst k3; simp [k1, k2]
        · simp [k1, k2, k3, hs1, StackProg.applyAct, halveAct, StackAct.apply]
      rw [← hpost]
      have := StackProg.Exec.loopTrue (test := fun h => (h U).isSome) (by simp [hU])
        (StackProg.Exec.act (halveAct U H P mk) s) h2
      rw [show 3 * (L + 1) + 1 = 1 + 1 + 1 + (3 * L + 1) by ring]; exact this

end Basic

/-! ## Binary-token vs unary-count comparison (`halvcmp`) -/

section HalvCmp
variable {K A : Type} [DecidableEq K]

/-- number of parity mismatches when the bits `bs` (LSB first) are compared with `v`. -/
def mism : List Bool → ℕ → ℕ
  | [], _ => 0
  | b :: bs, v => mism bs (v / 2) + (if (decide (v % 2 = 1) != b) = true then 1 else 0)

lemma mism_bits : ∀ (k v : ℕ), (mism (Nat.bits k) v = 0 ∧ v / 2 ^ (Nat.bits k).length = 0) ↔ k = v := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro v; simp [mism]; omega
  | bit b n hn ih =>
    intro v
    rw [Nat.bits_append_bit _ _ hn, mism, List.length_cons, pow_succ', ← Nat.div_div_eq_div_mul]
    have h := ih (v / 2)
    constructor
    · rintro ⟨h1, h2⟩
      have hm : mism n.bits (v / 2) = 0 := by omega
      have hb : (decide (v % 2 = 1) != b) = false := by
        by_contra hc; simp only [Bool.not_eq_false] at hc; rw [if_pos hc] at h1; omega
      have hn' := h.1 ⟨hm, h2⟩
      rw [Nat.bit_val]
      cases b <;> simp at hb ⊢ <;> omega
    · intro hv
      subst hv
      rw [Nat.bit_val] at h ⊢
      have e1 : (2 * n + b.toNat) / 2 = n := by cases b <;> simp <;> omega
      rw [e1] at h ⊢
      obtain ⟨h1, h2⟩ := h.2 rfl
      refine ⟨?_, h2⟩
      rw [h1]
      cases b <;> simp <;> omega

def hcAct (T P B : K) (mk : A) (isOne : Option A → Bool) (h : K → Option A) (k : K) : StackAct A :=
  if k = T then .pop
  else if k = P then (if (h P).isSome then .pop else .keep)
  else if k = B then (if ((h P).isSome != isOne (h T)) = true then .push mk else .keep)
  else .keep

def hcLoop (T U H P B : K) (mk : A) (isD isOne : Option A → Bool) : StackProg K A :=
  .loop (fun h => isD (h T))
    (.seq (halveProg U H P mk) (.seq (.act (hcAct T P B mk isOne))
      (transferProg H (fun k => decide (k = U)))))

def hcPost (T U B : K) (mk : A) (s : K → List A) (bs : List Bool) (v : ℕ) (r : List A) :
    K → List A :=
  Function.update (Function.update (Function.update s T r) U
    (List.replicate (v / 2 ^ bs.length) mk)) B (List.replicate (mism bs v) mk ++ s B)

lemma exec_hc (T U H P B : K) (hTU : T ≠ U) (hTH : T ≠ H) (hTP : T ≠ P) (hTB : T ≠ B)
    (hUH : U ≠ H) (hUP : U ≠ P) (hUB : U ≠ B) (hHP : H ≠ P) (hHB : H ≠ B) (hPB : P ≠ B)
    (mk : A) (dsym : Bool → A) (isD isOne : Option A → Bool)
    (hD : ∀ b, isD (some (dsym b)) = true) (hO : ∀ b, isOne (some (dsym b)) = b)
    (r : List A) (hr : isD r.head? = false) :
    ∀ (bs : List Bool) (v : ℕ) (s : K → List A), s T = bs.map dsym ++ r →
      s U = List.replicate v mk → s H = [] → s P = [] →
      ∃ n ≤ bs.length * (6 * v + 12) + 1,
        (hcLoop T U H P B mk isD isOne).Exec s (hcPost T U B mk s bs v r) n := by
  intro bs
  induction bs with
  | nil =>
    intro v s hT hU hH hP
    refine ⟨1, by simp, ?_⟩
    have hpost : hcPost T U B mk s [] v r = s := by
      funext k
      simp only [hcPost, mism, List.length_nil, pow_zero, Nat.div_one, List.replicate_zero,
        List.nil_append]
      by_cases k1 : k = B
      · subst k1; simp
      by_cases k2 : k = U
      · subst k2; simp [k1, hU]
      by_cases k3 : k = T
      · subst k3; simp [k1, k2, hT]
      · simp [k1, k2, k3]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simpa [hT] using hr)
  | cons b bs ih =>
    intro v s hT hU hH hP
    -- halving
    have e1 := exec_halve U H P hUH hUP hHP mk v 0 s (by simp [hU]) (by omega) (by simp [hP])
    set s1 := Function.update (Function.update (Function.update s U []) P
      (List.replicate ((0 + v) % 2) mk)) H (List.replicate ((0 + v) / 2) mk ++ s H) with hs1
    -- the act
    set s2 := StackProg.applyAct (hcAct T P B mk isOne) s1 with hs2
    have e2 := StackProg.Exec.act (hcAct T P B mk isOne) s1
    have h1T : s1 T = dsym b :: (bs.map dsym ++ r) := by
      simp [hs1, hTU, hTH, hTP, hT]
    have h1P : s1 P = List.replicate (v % 2) mk := by simp [hs1, Ne.symm hHP]
    have h1H : s1 H = List.replicate (v / 2) mk := by simp [hs1, hH]
    have h1U : s1 U = [] := by simp [hs1, hUH, hUP]
    have hpar : (s1 P).head?.isSome = decide (v % 2 = 1) := by
      rw [h1P]; rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    -- transfer
    obtain ⟨n3, hn3, e3⟩ := exec_transfer H (fun k => decide (k = U)) (s2 H) s2 rfl
    set mb := if (decide (v % 2 = 1) != b) = true then 1 else 0 with hmb
    set s' := Function.update (Function.update (Function.update s T (bs.map dsym ++ r)) U
      (List.replicate (v / 2) mk)) B (List.replicate mb mk ++ s B) with hs'
    have hsB : s1 B = s B := by simp [hs1, Ne.symm hHB, Ne.symm hPB, Ne.symm hUB]
    have h2T : s2 T = bs.map dsym ++ r := by
      simp [hs2, StackProg.applyAct, hcAct, StackAct.apply, h1T]
    have h2P : s2 P = [] := by
      simp only [hs2, StackProg.applyAct, hcAct, if_neg (Ne.symm hTP), if_true, h1P]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h, StackAct.apply]
    have h2B : s2 B = List.replicate mb mk ++ s B := by
      have hx : ((s1 P).head?.isSome != isOne (s1 T).head?) = (decide (v % 2 = 1) != b) := by
        rw [hpar, h1T, List.head?_cons, hO]
      simp only [hs2, StackProg.applyAct, hcAct, if_neg (Ne.symm hTB), if_neg (Ne.symm hPB),
        if_true]
      simp only [hx]
      by_cases hc : (decide (v % 2 = 1) != b) = true
      · simp [hc, hmb, StackAct.apply, hsB]
      · simp [hc, hmb, StackAct.apply, hsB]
    have h2o : ∀ k, k ≠ T → k ≠ P → k ≠ B → s2 k = s1 k := by
      intro k k1 k2 k3
      simp [hs2, StackProg.applyAct, hcAct, StackAct.apply, k1, k2, k3]
    have hs2H : s2 H = List.replicate (v / 2) mk := by
      rw [h2o H (Ne.symm hTH) hHP hHB, h1H]
    have hs2U : s2 U = [] := by rw [h2o U (Ne.symm hTU) hUP hUB, h1U]
    have h3 : transferStore H (fun k => decide (k = U)) s2 = s' := by
      funext k
      by_cases k1 : k = H
      · rw [k1]; simp [transferStore, hs', Ne.symm hTH, hUH.symm, hHB, hH]
      by_cases k2 : k = U
      · rw [k2]; simp [transferStore, hs', hUB, hs2H, hs2U, hUH]
      by_cases k3 : k = T
      · rw [k3]; simp [transferStore, hs', hTB, hTU, hTH, h2T]
      by_cases k4 : k = P
      · rw [k4]; simp [transferStore, hs', hPB, hUP.symm, hTP.symm, hHP.symm, h2P, hP]
      by_cases k5 : k = B
      · rw [k5]; simp [transferStore, hs', hHB.symm, hUB.symm, h2B]
      · simp only [transferStore, k1, k2, if_false, decide_false, Bool.false_eq_true]
        rw [h2o k k3 k4 k5]
        simp [hs', hs1, k1, k2, k3, k4, k5]
    rw [h3] at e3
    -- induction hypothesis
    obtain ⟨n', hn', e4⟩ := ih (v / 2) s' (by simp [hs', hTB, hTU])
      (by simp [hs', hUB])
      (by simp [hs', Ne.symm hUH, hHB, Ne.symm hTH, hH])
      (by simp [hs', Ne.symm hUP, hPB, Ne.symm hTP, hP])
    have hpost : hcPost T U B mk s' bs (v / 2) r = hcPost T U B mk s (b :: bs) v r := by
      have hdiv : v / 2 / 2 ^ bs.length = v / 2 ^ (b :: bs).length := by
        rw [List.length_cons, pow_succ, Nat.div_div_eq_div_mul, mul_comm]
      funext k
      simp only [hcPost, hdiv, mism]
      by_cases k1 : k = B
      · rw [k1]
        have hB' : s' B = List.replicate mb mk ++ s B := by simp [hs']
        simp only [Function.update_self, hB', hmb, List.replicate_add, List.append_assoc]
      by_cases k2 : k = U
      · subst k2; simp [k1]
      by_cases k3 : k = T
      · subst k3; simp [k1, k2]
      · simp [hs', k1, k2, k3]
    rw [← hpost]
    refine ⟨1 + ((3 * v + 1) + 1 + (1 + 1 + n3)) + 1 + n', ?_,
      StackProg.Exec.loopTrue (by simp [hT, hD]) (StackProg.Exec.seq (by simpa using e1)
        (StackProg.Exec.seq e2 e3)) e4⟩
    have hmul := Nat.mul_le_mul_left bs.length (show 6 * (v / 2) + 12 ≤ 6 * v + 12 by omega)
    have hexp : (bs.length + 1) * (6 * v + 12) = bs.length * (6 * v + 12) + (6 * v + 12) := by ring
    rw [hs2H] at hn3
    simp only [List.length_replicate] at hn3
    rw [List.length_cons, hexp]
    generalize bs.length * (6 * v + 12) = X at hmul ⊢
    generalize bs.length * (6 * (v / 2) + 12) = Y at hmul hn'
    omega

end HalvCmp

/-! ## Phase A scan: the DFA on a state stack plus counters and part copies -/

section ScanA
open DS

/-- states as stack symbols -/
def dsA : DS → A
  | S0 => some (.inr .minus) | M => some (.inl .minus) | Z => some (.inl .zero)
  | O => some (.inl .one) | T0 => some (.inr .sep) | TZ => some (.inr .zero)
  | TO => some (.inr .one) | X => some (.inl .sep)

def decS : Option A → DS
  | some (some (.inl .minus)) => M
  | some (some (.inl .zero)) => Z
  | some (some (.inl .one)) => O
  | some (some (.inr .sep)) => T0
  | some (some (.inr .zero)) => TZ
  | some (some (.inr .one)) => TO
  | some (some (.inl .sep)) => X
  | some none => X
  | _ => S0

lemma decS_dsA (q : DS) : decS (some (dsA q)) = q := by cases q <;> rfl

lemma dsA_inj {q q' : DS} (h : dsA q = dsA q') : q = q' := by
  rw [← decS_dsA q, ← decS_dsA q', h]

def δA (q : Option A) (a : A) : A := dsA (dstep (decS q) a)

lemma runQ_some : ∀ (l : List A) (q : DS), runQ δA (some (dsA q)) l = some (dsA (runD q l)) := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons a l ih => intro q; simp only [runQ, δA, decS_dsA, ih, runD_cons]

lemma runQ_none_accept (u : List A) :
    runQ δA none u = some (dsA T0) ↔ ∃ (c : List ℤ) (d : List ℕ), u = Ew c d := by
  rw [← runD_iff]
  rcases u with _ | ⟨a, l⟩
  · simp [runQ]
  · simp only [runQ, δA, runQ_some, runD_cons, Option.some.injEq]
    have : decS none = S0 := rfl
    rw [this]
    exact ⟨fun h => dsA_inj h, fun h => by rw [h]⟩

def mkA : A := none

def gc (a : A) : Option A := if a = ι1 .sep then some mkA else none
def gd (a : A) : Option A := if a = ι2 .sep then some mkA else none
def gC (a : A) : Option A := match a with | some (.inl _) => some a | _ => none
def gD (a : A) : Option A := match a with | some (.inr _) => some a | _ => none

lemma encInt_split (z : ℤ) : encInt z =
    ((if z < 0 then [BSym.minus] else []) ++ (Nat.bits z.natAbs).map dg) ++ [BSym.sep] := by
  simp only [encInt, encNat_dg, List.append_assoc]

lemma pre_no_sep (z : ℤ) : ∀ b ∈ ((if z < 0 then [BSym.minus] else []) ++ (Nat.bits z.natAbs).map dg),
    b ≠ BSym.sep := by
  intro b hb
  simp only [List.mem_append, List.mem_map] at hb
  rcases hb with hb | ⟨x, -, rfl⟩
  · split_ifs at hb <;> simp_all
  · cases x <;> simp [dg]

lemma digits_no_sep (k : ℕ) : ∀ b ∈ (Nat.bits k).map dg, b ≠ BSym.sep := by
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨x, -, rfl⟩ := hb
  cases x <;> simp [dg]

lemma fm_ι2_gc (l : List BSym) : (l.map ι2).filterMap gc = [] := by
  induction l <;> simp_all [gc, ι1, ι2]
lemma fm_ι1_gd (l : List BSym) : (l.map ι1).filterMap gd = [] := by
  induction l <;> simp_all [gd, ι1, ι2]
lemma fm_ι2_gC (l : List BSym) : (l.map ι2).filterMap gC = [] := by
  induction l <;> simp_all [gC, ι2]
lemma fm_ι1_gD (l : List BSym) : (l.map ι1).filterMap gD = [] := by
  induction l <;> simp_all [gD, ι1]
lemma fm_ι1_gC (l : List BSym) : (l.map ι1).filterMap gC = l.map ι1 := by
  induction l <;> simp_all [gC, ι1]
lemma fm_ι2_gD (l : List BSym) : (l.map ι2).filterMap gD = l.map ι2 := by
  induction l <;> simp_all [gD, ι2]
lemma fm_ι1_gc_nosep (l : List BSym) (h : ∀ b ∈ l, b ≠ BSym.sep) : (l.map ι1).filterMap gc = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [gc, ι1, hb, this]
lemma fm_ι2_gd_nosep (l : List BSym) (h : ∀ b ∈ l, b ≠ BSym.sep) : (l.map ι2).filterMap gd = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [gd, ι2, hb, this]

lemma fm_gc (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gc = List.replicate c.length mkA := by
  have h0 : gc none = none := by simp [gc, ι1]
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι2_gc, List.append_nil]
  induction c with
  | nil => rfl
  | cons z c ih =>
    rw [encInts_cons, List.map_append, List.filterMap_append, ih, encInt_split, List.map_append,
      List.filterMap_append, fm_ι1_gc_nosep _ (pre_no_sep z)]
    simp [gc, ι1, List.replicate_succ]

lemma fm_gd (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gd = List.replicate d.length mkA := by
  have h0 : gd none = none := by simp [gd, ι2]
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι1_gd, List.nil_append]
  induction d with
  | nil => rfl
  | cons k d ih =>
    rw [encNats_cons, List.map_append, List.filterMap_append, ih, encNat_dg, List.map_append,
      List.filterMap_append, fm_ι2_gd_nosep _ (digits_no_sep k)]
    simp [gd, ι2, List.replicate_succ]

lemma fm_gC (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gC = (encInts c).map ι1 := by
  have h0 : gC none = none := rfl
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι2_gC, List.append_nil, fm_ι1_gC]

lemma fm_gD (c : List ℤ) (d : List ℕ) : (Ew c d).filterMap gD = (encNats d).map ι2 := by
  have h0 : gD none = none := rfl
  rw [Ew, List.filterMap_append, List.filterMap_cons_none h0, fm_ι1_gD, List.nil_append, fm_ι2_gD]

variable {K : Type} [DecidableEq K]

lemma emitR_indep (δ : Option A → A → A) (out : K → Option A → A → Option A) (k : K)
    (g : A → Option A) (hg : ∀ q a, out k q a = g a) :
    ∀ (l : List A) (q : Option A), emitR δ out k q l = (l.filterMap g).reverse := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons a l ih =>
    intro q
    rw [emitR, ih, hg, List.filterMap_cons]
    cases g a <;> simp

/-- the phase-A output function: counters `kc`, `kd` and part copies `kC`, `kD`. -/
def outA (kc kd kC kD : K) (k : K) (_q : Option A) (a : A) : Option A :=
  if k = kc then gc a else if k = kd then gd a else if k = kC then gC a
  else if k = kD then gD a else none

end ScanA

section ScanA2
variable {K : Type} [DecidableEq K]

/-- Phase-A scan, summarised. -/
lemma scanA_result (ki st kc kd kC kD : K) (h01 : ki ≠ st)
    (hc0 : kc ≠ ki) (hc1 : kc ≠ st) (hd0 : kd ≠ ki) (hd1 : kd ≠ st)
    (hC0 : kC ≠ ki) (hC1 : kC ≠ st) (hD0 : kD ≠ ki) (hD1 : kD ≠ st)
    (hcd : kc ≠ kd) (hcC : kc ≠ kC) (hcD : kc ≠ kD) (hdC : kd ≠ kC) (hdD : kd ≠ kD) (hCD : kC ≠ kD)
    (u : List A) (s : K → List A) (hs : s ki = u) (hst : s st = [])
    (hkc : s kc = []) (hkd : s kd = []) (hkC : s kC = []) (hkD : s kD = []) :
    (scanProg ki st δA (outA kc kd kC kD)).Exec s (scanRun ki st δA (outA kc kd kC kD) u s)
        (3 * u.length + 1) ∧
      ((scanRun ki st δA (outA kc kd kC kD) u s st).head? = some (dsA DS.T0) ↔
        ∃ (c : List ℤ) (d : List ℕ), u = Ew c d) ∧
      (∀ c d, u = Ew c d →
        scanRun ki st δA (outA kc kd kC kD) u s kc = List.replicate c.length mkA ∧
        scanRun ki st δA (outA kc kd kC kD) u s kd = List.replicate d.length mkA ∧
        scanRun ki st δA (outA kc kd kC kD) u s kC = ((encInts c).map ι1).reverse ∧
        scanRun ki st δA (outA kc kd kC kD) u s kD = ((encNats d).map ι2).reverse) ∧
      (∀ k, k ≠ ki → k ≠ st → k ≠ kc → k ≠ kd → k ≠ kC → k ≠ kD →
        scanRun ki st δA (outA kc kd kC kD) u s k = s k) := by
  set out := outA kc kd kC kD with hout
  refine ⟨exec_scan ki st δA out u s hs, ?_, ?_, ?_⟩
  · rw [scanRun_st ki st h01, hst]
    exact runQ_none_accept u
  · intro c d hu
    have ec : ∀ q a, out kc q a = gc a := by intro q a; simp [hout, outA]
    have ed : ∀ q a, out kd q a = gd a := by intro q a; simp [hout, outA, Ne.symm hcd]
    have eC : ∀ q a, out kC q a = gC a := by intro q a; simp [hout, outA, Ne.symm hcC, Ne.symm hdC]
    have eD : ∀ q a, out kD q a = gD a := by
      intro q a; simp [hout, outA, Ne.symm hcD, Ne.symm hdD, Ne.symm hCD]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [scanRun_other ki st h01 δA out kc hc0 hc1, emitR_indep δA out kc gc ec, hkc, hu, fm_gc]
      simp
    · rw [scanRun_other ki st h01 δA out kd hd0 hd1, emitR_indep δA out kd gd ed, hkd, hu, fm_gd]
      simp
    · rw [scanRun_other ki st h01 δA out kC hC0 hC1, emitR_indep δA out kC gC eC, hkC, hu, fm_gC]
      simp
    · rw [scanRun_other ki st h01 δA out kD hD0 hD1, emitR_indep δA out kD gD eD, hkD, hu, fm_gD]
      simp
  · intro k k0 k1 k2 k3 k4 k5
    have e : ∀ q a, out k q a = (fun _ => none) a := by intro q a; simp [hout, outA, k2, k3, k4, k5]
    rw [scanRun_other ki st h01 δA out k k0 k1, emitR_indep δA out k _ e]
    simp

end ScanA2

/-! ## Unary arithmetic: synchronous pop, repeated copy, division -/

section Unary
variable {K A : Type} [DecidableEq K]

def syncPopAct (i j : K) (_h : K → Option A) (k : K) : StackAct A :=
  if k = i ∨ k = j then .pop else .keep

/-- pop `i` and `j` together while both are nonempty. -/
def syncPopProg (i j : K) : StackProg K A :=
  .loop (fun h => (h i).isSome && (h j).isSome) (.act (syncPopAct i j))

lemma exec_syncPop (i j : K) (hij : i ≠ j) : ∀ (L : ℕ) (s : K → List A),
    min (s i).length (s j).length = L →
    (syncPopProg i j).Exec s
      (Function.update (Function.update s i ((s i).drop L)) j ((s j).drop L)) (3 * L + 1) := by
  intro L
  induction L with
  | zero =>
    intro s hL
    have hpost : Function.update (Function.update s i ((s i).drop 0)) j ((s j).drop 0) = s := by
      funext k; by_cases k1 : k = j
      · subst k1; simp
      · by_cases k2 : k = i
        · subst k2; simp [k1]
        · simp [k1, k2]
    rw [hpost]
    refine StackProg.Exec.loopFalse ?_
    rcases Nat.min_eq_zero_iff.1 hL with h | h
    · simp [List.eq_nil_of_length_eq_zero h]
    · simp [List.eq_nil_of_length_eq_zero h]
  | succ L ih =>
    intro s hL
    obtain ⟨a, l1, h1⟩ : ∃ a l1, s i = a :: l1 := by
      rcases h : s i with _ | ⟨a, l1⟩
      · rw [h] at hL; simp at hL
      · exact ⟨a, l1, rfl⟩
    obtain ⟨b, l2, h2⟩ : ∃ b l2, s j = b :: l2 := by
      rcases h : s j with _ | ⟨b, l2⟩
      · rw [h] at hL; simp at hL
      · exact ⟨b, l2, rfl⟩
    set s1 := StackProg.applyAct (syncPopAct i j) s with hs1
    have e1i : s1 i = l1 := by simp [hs1, StackProg.applyAct, syncPopAct, StackAct.apply, h1]
    have e1j : s1 j = l2 := by simp [hs1, StackProg.applyAct, syncPopAct, StackAct.apply, h2]
    have hL1 : min (s1 i).length (s1 j).length = L := by
      rw [e1i, e1j]; rw [h1, h2] at hL; simp at hL; omega
    have e2 := ih s1 hL1
    have hpost : Function.update (Function.update s1 i ((s1 i).drop L)) j ((s1 j).drop L) =
        Function.update (Function.update s i ((s i).drop (L + 1))) j ((s j).drop (L + 1)) := by
      funext k
      by_cases k1 : k = j
      · subst k1; simp [e1j, h2]
      by_cases k2 : k = i
      · subst k2; simp [k1, e1i, h1]
      · simp [k1, k2, hs1, StackProg.applyAct, syncPopAct, StackAct.apply]
    rw [← hpost, show 3 * (L + 1) + 1 = 1 + 1 + 1 + (3 * L + 1) by ring]
    exact StackProg.Exec.loopTrue (by simp [h1, h2]) (StackProg.Exec.act _ _) e2

lemma exec_pop (c : K) (s : K → List A) :
    (popProg c).Exec s (Function.update s c (s c).tail) 1 := by
  have h := StackProg.Exec.act (fun (_ : K → Option A) k => if k = c then StackAct.pop else .keep) s
  have e : StackProg.applyAct (fun (_ : K → Option A) k => if k = c then StackAct.pop else .keep) s =
      Function.update s c (s c).tail := by
    funext k; by_cases k1 : k = c
    · subst k1; simp [StackProg.applyAct, StackAct.apply]
    · simp [StackProg.applyAct, StackAct.apply, k1]
  rw [e] at h; exact h

/-- repeated copy: `cnt` times append (a copy of) `src` to `dst`. -/
def rcLoop (src dst cnt scr : K) : StackProg K A :=
  .loop (fun h => (h cnt).isSome) (.seq (popProg cnt) (copyProg src dst scr))

lemma exec_rc (src dst cnt scr : K) (h1 : src ≠ dst) (h2 : src ≠ scr) (h3 : dst ≠ scr)
    (h4 : cnt ≠ src) (h5 : cnt ≠ dst) (h6 : cnt ≠ scr) (mk : A) (a : ℕ) :
    ∀ (k : ℕ) (s : K → List A), (s cnt).length = k → s src = List.replicate a mk → s scr = [] →
      ∃ n ≤ k * (6 * a + 8) + 1, (rcLoop src dst cnt scr).Exec s
        (Function.update (Function.update s cnt []) dst (List.replicate (k * a) mk ++ s dst)) n := by
  intro k
  induction k with
  | zero =>
    intro s hk _ _
    have hc : s cnt = [] := List.eq_nil_of_length_eq_zero hk
    refine ⟨1, by simp, ?_⟩
    have hpost : Function.update (Function.update s cnt []) dst
        (List.replicate (0 * a) mk ++ s dst) = s := by
      funext k; by_cases k1 : k = dst
      · subst k1; simp
      · by_cases k2 : k = cnt
        · subst k2; simp [k1, hc]
        · simp [k1, k2]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simp [hc])
  | succ k ih =>
    intro s hk hsrc hscr
    have e1 := exec_pop cnt s
    set s1 := Function.update s cnt (s cnt).tail with hs1
    obtain ⟨n2, hn2, e2⟩ := exec_copy src dst scr h1 h2 h3 s1 (by simp [hs1, h6.symm, hscr])
    set s2 := Function.update s1 dst (s1 src ++ s1 dst) with hs2
    have h2c : (s2 cnt).length = k := by simp [hs2, hs1, h5, hk]
    have h2s : s2 src = List.replicate a mk := by simp [hs2, hs1, h1, h4.symm, hsrc]
    have h2r : s2 scr = [] := by simp [hs2, hs1, h3.symm, h6.symm, hscr]
    obtain ⟨n3, hn3, e3⟩ := ih s2 h2c h2s h2r
    have hpost : Function.update (Function.update s2 cnt []) dst (List.replicate (k * a) mk ++ s2 dst) =
        Function.update (Function.update s cnt []) dst
          (List.replicate ((k + 1) * a) mk ++ s dst) := by
      funext x
      by_cases k1 : x = dst
      · rw [k1]
        simp only [Function.update_self]
        have e : s2 dst = List.replicate a mk ++ s dst := by
          rw [hs2, Function.update_self, hs1, Function.update_of_ne h4.symm,
            Function.update_of_ne h5.symm, hsrc]
        rw [e, ← List.append_assoc, List.replicate_append_replicate, add_mul, one_mul]
      by_cases k2 : x = cnt
      · subst k2; simp [k1]
      · simp [k1, k2, hs2, hs1]
    rw [← hpost]
    have hsrc1 : (s1 src).length = a := by simp [hs1, h4.symm, hsrc]
    refine ⟨1 + (1 + 1 + n2) + 1 + n3, ?_, StackProg.Exec.loopTrue ?_ (StackProg.Exec.seq e1 e2) e3⟩
    · rw [hsrc1] at hn2
      have : (k + 1) * (6 * a + 8) = k * (6 * a + 8) + (6 * a + 8) := by ring
      rw [this]
      generalize k * (6 * a + 8) = X at hn3 ⊢
      omega
    · rcases h : s cnt with _ | ⟨b, l⟩
      · rw [h] at hk; simp at hk
      · simp [h]

end Unary

/-! ## Unary division with remainder flag -/

section Div
variable {K A : Type} [DecidableEq K]

def divAct (Y Q Bd : K) (mk : A) (h : K → Option A) (k : K) : StackAct A :=
  if k = Q then .push mk else if k = Bd then (if (h Y).isSome then .push mk else .keep) else .keep

/-- `Q` gets `⌈r/D⌉` marks, `Bd` one mark iff `D ∤ r` (`R` holds `r`, `Np` holds `D`). -/
def divLoop (R Np Y Q Bd scr : K) (mk : A) : StackProg K A :=
  .loop (fun h => (h R).isSome)
    (.seq (copyProg Np Y scr) (.seq (syncPopProg R Y)
      (.seq (.act (divAct Y Q Bd mk)) (clearProg Y))))

def divPost (R Q Bd : K) (mk : A) (s : K → List A) (r D : ℕ) : K → List A :=
  Function.update (Function.update (Function.update s R []) Q
    (List.replicate ((r + D - 1) / D) mk ++ s Q)) Bd
    (List.replicate (if r % D = 0 then 0 else 1) mk ++ s Bd)

lemma exec_div (R Np Y Q Bd scr : K)
    (hRN : R ≠ Np) (hRY : R ≠ Y) (hRQ : R ≠ Q) (hRB : R ≠ Bd) (hRs : R ≠ scr)
    (hNY : Np ≠ Y) (hNQ : Np ≠ Q) (hNB : Np ≠ Bd) (hNs : Np ≠ scr)
    (hYQ : Y ≠ Q) (hYB : Y ≠ Bd) (hYs : Y ≠ scr) (hQB : Q ≠ Bd) (hQs : Q ≠ scr) (hBs : Bd ≠ scr)
    (mk : A) (D : ℕ) (hD : 1 ≤ D) :
    ∀ (r : ℕ) (s : K → List A), s R = List.replicate r mk → s Np = List.replicate D mk →
      s Y = [] → s scr = [] →
      ∃ n ≤ r * (12 * D + 12) + 1, (divLoop R Np Y Q Bd scr mk).Exec s (divPost R Q Bd mk s r D) n := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s hR hN hY hs
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨1, by simp, ?_⟩
    have hpost : divPost R Q Bd mk s 0 D = s := by
      have h1 : (0 + D - 1) / D = 0 := Nat.div_eq_of_lt (by omega)
      funext k
      simp only [divPost, h1, Nat.zero_mod, if_true, List.replicate_zero, List.nil_append]
      by_cases k1 : k = Bd
      · subst k1; simp
      by_cases k2 : k = Q
      · subst k2; simp [k1]
      by_cases k3 : k = R
      · subst k3; simp [k1, k2, hR]
      · simp [k1, k2, k3]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simp [hR])
  · -- one iteration
    obtain ⟨n1, hn1, e1⟩ := exec_copy Np Y scr hNY hNs hYs s hs
    set s1 := Function.update s Y (s Np ++ s Y) with hs1
    set L := min r D with hL
    have hL1 : 1 ≤ L := by omega
    have e2 := exec_syncPop R Y hRY L s1 (by simp [hs1, hRY, hR, hN, hY, hL])
    set s2 := Function.update (Function.update s1 R ((s1 R).drop L)) Y ((s1 Y).drop L) with hs2
    have h2R : s2 R = List.replicate (r - L) mk := by
      simp [hs2, hs1, hRY, hR, List.drop_replicate]
    have h2Y : s2 Y = List.replicate (D - L) mk := by
      simp [hs2, hs1, hN, hY, List.drop_replicate]
    have h2o : ∀ k, k ≠ R → k ≠ Y → s2 k = s k := by
      intro k k1 k2; simp [hs2, hs1, k1, k2]
    have e3 := StackProg.Exec.act (divAct Y Q Bd mk) s2
    set s3 := StackProg.applyAct (divAct Y Q Bd mk) s2 with hs3
    have h3Q : s3 Q = mk :: s Q := by
      simp [hs3, StackProg.applyAct, divAct, StackAct.apply, h2o Q (Ne.symm hRQ) (Ne.symm hYQ)]
    have h3B : s3 Bd = List.replicate (if r < D then 1 else 0) mk ++ s Bd := by
      simp only [hs3, StackProg.applyAct, divAct, if_neg (Ne.symm hQB), if_true, h2Y,
        h2o Bd (Ne.symm hRB) (Ne.symm hYB)]
      by_cases hrD : r < D
      · have : D - L ≠ 0 := by omega
        obtain ⟨j, hj⟩ : ∃ j, D - L = j + 1 := ⟨D - L - 1, by omega⟩
        simp [hrD, hj, List.replicate_succ, StackAct.apply]
      · have : D - L = 0 := by omega
        simp [hrD, this, StackAct.apply]
    have h3o : ∀ k, k ≠ Q → k ≠ Bd → s3 k = s2 k := by
      intro k k1 k2; simp [hs3, StackProg.applyAct, divAct, StackAct.apply, k1, k2]
    obtain ⟨n4, hn4, e4⟩ := exec_transfer Y (fun _ => false) (s3 Y) s3 rfl
    set s4 := transferStore Y (fun _ => false) s3 with hs4
    have h3Y : s3 Y = List.replicate (D - L) mk := by rw [h3o Y hYQ hYB, h2Y]
    have h4R : s4 R = List.replicate (r - L) mk := by
      simp [hs4, transferStore, hRY, h3o R hRQ hRB, h2R]
    have h4N : s4 Np = List.replicate D mk := by
      simp [hs4, transferStore, hNY, h3o Np hNQ hNB, h2o Np hRN.symm hNY, hN]
    have h4Y : s4 Y = [] := by simp [hs4, transferStore]
    have h4s : s4 scr = [] := by
      simp [hs4, transferStore, hYs.symm, h3o scr hQs.symm hBs.symm, h2o scr hRs.symm hYs.symm, hs]
    have hlt : r - L < r := by omega
    obtain ⟨n', hn', e5⟩ := ih (r - L) hlt s4 h4R h4N h4Y h4s
    have hpost : divPost R Q Bd mk s4 (r - L) D = divPost R Q Bd mk s r D := by
      have h4Q : s4 Q = mk :: s Q := by simp [hs4, transferStore, hYQ.symm, h3Q]
      have h4B : s4 Bd = List.replicate (if r < D then 1 else 0) mk ++ s Bd := by
        simp [hs4, transferStore, hYB.symm, h3B]
      have hq : (r - L + D - 1) / D + 1 = (r + D - 1) / D := by
        by_cases hrD : r < D
        · have h0 : r - L = 0 := by omega
          rw [h0, Nat.div_eq_of_lt (by omega : 0 + D - 1 < D)]
          symm; apply Nat.div_eq_of_lt_le <;> omega
        · have h0 : r - L = r - D := by omega
          rw [h0, ← Nat.add_div_right _ (by omega : 0 < D)]
          congr 1; omega
      have hb : (if (r - L) % D = 0 then 0 else 1) + (if r < D then 1 else 0) =
          (if r % D = 0 then 0 else 1) := by
        by_cases hrD : r < D
        · have h0 : r - L = 0 := by omega
          have h1 : r % D = r := Nat.mod_eq_of_lt hrD
          rw [h0, Nat.zero_mod, h1]; simp [hrD]; omega
        · have h0 : r - L = r - D := by omega
          rw [h0, ← Nat.mod_eq_sub_mod (by omega)]
          simp [hrD]
      funext k
      by_cases k1 : k = Bd
      · subst k1
        simp only [divPost, Function.update_self, h4B, ← List.append_assoc,
          List.replicate_append_replicate, hb]
      by_cases k2 : k = Q
      · subst k2
        simp only [divPost, Function.update_self, Function.update_of_ne k1, h4Q]
        rw [← hq, List.replicate_succ', List.append_assoc, List.singleton_append]
      by_cases k3 : k = R
      · subst k3; simp [divPost, k1, k2]
      · simp only [divPost, Function.update_of_ne k1, Function.update_of_ne k2,
          Function.update_of_ne k3]
        by_cases k4 : k = Y
        · subst k4; rw [h4Y, hY]
        · simp [hs4, transferStore, k4, h3o k k2 k1, h2o k k3 k4]
    rw [← hpost]
    refine ⟨1 + (n1 + 1 + ((3 * L + 1) + 1 + (1 + 1 + n4))) + 1 + n', ?_,
      StackProg.Exec.loopTrue (by simp [hR]; omega)
        (StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 e4))) e5⟩
    rw [h3Y, List.length_replicate] at hn4
    rw [hN, List.length_replicate] at hn1
    have hmul : (r - L) * (12 * D + 12) ≤ (r - 1) * (12 * D + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : r * (12 * D + 12) = (r - 1) * (12 * D + 12) + (12 * D + 12) := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp; ring
    rw [hexp]
    generalize (r - 1) * (12 * D + 12) = X at hmul ⊢
    generalize (r - L) * (12 * D + 12) = Y at hmul hn'
    omega

end Div

/-! ## Token-level facts for the digit loops -/

section Tokens

def isDA (o : Option A) : Bool := decide (o = some (ι1 .zero)) || decide (o = some (ι1 .one))
def isOneA (o : Option A) : Bool := decide (o = some (ι1 .one))
def dsymA (b : Bool) : A := ι1 (dg b)

lemma isDA_dsym (b : Bool) : isDA (some (dsymA b)) = true := by cases b <;> rfl
lemma isOneA_dsym (b : Bool) : isOneA (some (dsymA b)) = b := by cases b <;> rfl

/-- the head token of a nonnegative integer: its digits, then the separator. -/
lemma encInts_head_nonneg (z : ℤ) (hz : 0 ≤ z) (c : List ℤ) :
    (encInts (z :: c)).map ι1 =
      (Nat.bits z.natAbs).map dsymA ++ ι1 .sep :: (encInts c).map ι1 := by
  rw [encInts_cons, encInt_split, if_neg (by omega)]
  simp [dsymA, Function.comp_def]

lemma encInts_head_neg (z : ℤ) (hz : z < 0) (c : List ℤ) :
    ((encInts (z :: c)).map ι1).head? = some (ι1 .minus) := by
  rw [encInts_cons, encInt_split, if_pos hz]
  simp

lemma isDA_sep : isDA (some (ι1 .sep)) = false := rfl

lemma head_encInts_nonneg (z : ℤ) (hz : 0 ≤ z) (c : List ℤ) :
    isDA ((encInts (z :: c)).map ι1).head? = decide (z ≠ 0) := by
  rw [encInts_head_nonneg z hz]
  rcases Nat.eq_zero_or_pos z.natAbs with h | h
  · have : z = 0 := by omega
    subst this; simp [isDA_sep]
  · have hb := bits_getLast z.natAbs (by omega)
    obtain ⟨b, l, hbl⟩ : ∃ b l, Nat.bits z.natAbs = b :: l := by
      rcases hh : Nat.bits z.natAbs with _ | ⟨b, l⟩
      · rw [hh] at hb; simp at hb
      · exact ⟨b, l, rfl⟩
    rw [hbl]
    have : z ≠ 0 := by omega
    simp [isDA_dsym, this]

end Tokens

/-! ## The length guard `Glen` and the conditions the E_len program checks -/

section Glen

/-- layout guard: `n = c₀ ≥ 1`, `m = c₁ ≥ 0`, `|c| = lenC (n+2) m`, `|d| = 2(n+2)`. -/
def Glen (c : List ℤ) (d : List ℕ) : Prop :=
  1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
  c.length = 2 + ((c.getD 0 0).toNat + 2) +
    2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
    ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat + (c.getD 1 0).toNat ∧
  d.length = 2 * ((c.getD 0 0).toNat + 2)

/-- the unary constant built by the program: `2N·N + N + 2`. -/
def Xv (N : ℕ) : ℕ := 2 * N * N + N + 2

/-- the conditions checked one after the other by the E_len program. -/
def GlenSteps (c : List ℤ) (d : List ℕ) : Prop :=
  d.length % 2 = 0 ∧ ∃ z c', c = z :: c' ∧ 1 ≤ z ∧ z.natAbs = d.length / 2 - 2 ∧
    (∀ z' c'', c' = z' :: c'' → 0 ≤ z') ∧ Xv (d.length / 2) ≤ c.length ∧
    (c.length - Xv (d.length / 2)) % (d.length / 2 + 2) = 0 ∧
    (c'.getD 0 0).natAbs = (c.length - Xv (d.length / 2)) / (d.length / 2 + 2)

lemma glen_iff (c : List ℤ) (d : List ℕ) : Glen c d ↔ GlenSteps c d := by
  constructor
  · rintro ⟨h0, h1, hc, hd⟩
    rcases c with _ | ⟨z, c'⟩
    · simp at h0
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons] at h0 h1 hc hd
    set N := z.toNat + 2 with hN
    set m := (c'.getD 0 0).toNat with hm
    have hN2 : d.length / 2 = N := by omega
    have hX : Xv N + (N + 2) * m = c'.length + 1 := by
      simp only [Xv]; rw [hc]; ring
    refine ⟨by omega, z, c', rfl, h0, by rw [hN2]; omega, ?_, ?_, ?_, ?_⟩
    · intro z' c'' h; subst h; simpa using h1
    · rw [hN2, List.length_cons]; omega
    · rw [hN2, List.length_cons, ← hX, Nat.add_sub_cancel_left, Nat.mul_mod_right]
    · rw [hN2, List.length_cons, ← hX, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by omega)]
      omega
  · rintro ⟨hev, z, c', rfl, hz, hzN, hc4, hX, hmod, hq⟩
    unfold Glen
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons] at hX hmod hq ⊢
    have h1 : 0 ≤ c'.getD 0 0 := by
      rcases c' with _ | ⟨z', c''⟩
      · simp
      · simpa using hc4 z' c'' rfl
    set N := d.length / 2 with hN
    have hNz : N = z.toNat + 2 := by omega
    set m := (c'.getD 0 0).toNat with hm
    have hmq : m = (c'.length + 1 - Xv N) / (N + 2) := by omega
    have hdiv := Nat.div_add_mod (c'.length + 1 - Xv N) (N + 2)
    rw [hmod, ← hmq] at hdiv
    refine ⟨hz, h1, ?_, by omega⟩
    rw [← hNz]
    have e : c'.length + 1 = Xv N + (N + 2) * m := by omega
    rw [e]; simp only [Xv]; ring

end Glen

end D0bfL

/-! ## Library part 2 (namespace D0bfT): token skipping and binary comparison -/

namespace D0bfT
open D0bfL

/-! ### binary values, last difference -/

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

lemma bval_cons (b : Bool) (l : List Bool) : bval (b :: l) = 2 * bval l + b.toNat := by
  simp only [bval, Nat.bit_val]

lemma bval_bits (n : ℕ) : bval (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval]
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval, ih]

/-- the comparison result of the most significant differing position (LSB-first lists). -/
def lastDiff : List Bool → List Bool → Option Bool
  | a :: as, b :: bs => (lastDiff as bs).elim (if a = b then none else some b) some
  | _, _ => none

lemma lastDiff_eq : ∀ (as bs : List Bool), as.length = bs.length →
    lastDiff as bs = (if bval as < bval bs then some true
      else if bval bs < bval as then some false else none) := by
  intro as
  induction as with
  | nil =>
    intro bs h
    rcases bs with _ | ⟨b, bs⟩
    · simp [lastDiff, bval]
    · simp at h
  | cons a as ih =>
    intro bs h
    rcases bs with _ | ⟨b, bs⟩
    · simp at h
    simp only [lastDiff, bval_cons]
    rw [ih bs (by simpa using h)]
    have ha : a.toNat ≤ 1 := by cases a <;> decide
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    by_cases h1 : bval as < bval bs
    · have h3 : 2 * bval as + a.toNat < 2 * bval bs + b.toNat := by omega
      simp [h1, h3]
    · by_cases h2 : bval bs < bval as
      · have h3 : ¬ 2 * bval as + a.toNat < 2 * bval bs + b.toNat := by omega
        have h4 : 2 * bval bs + b.toNat < 2 * bval as + a.toNat := by omega
        simp [h1, h2, h3, h4]
      · have e : bval as = bval bs := by omega
        rw [if_neg h1, if_neg h2, e]
        cases a <;> cases b <;> simp

lemma lt_of_bits_len {a b : ℕ} (h : (Nat.bits a).length < (Nat.bits b).length) : a < b := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at h
  calc a < 2 ^ Nat.size a := Nat.lt_size_self a
    _ ≤ 2 ^ (Nat.size b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ b := Nat.lt_size.1 (by omega)

/-! ### token lists -/

/-- a list of sep-free tokens, each followed by the separator, embedded by `e`. -/
def toksE (e : BSym → A) (ts : List (List BSym)) : List A :=
  (ts.map (fun t => t.map e ++ [e .sep])).flatten

lemma toksE_nil (e : BSym → A) : toksE e [] = [] := rfl

lemma toksE_cons (e : BSym → A) (t : List BSym) (ts : List (List BSym)) :
    toksE e (t :: ts) = t.map e ++ e .sep :: toksE e ts := by
  simp [toksE]

/-- the digit token of a natural number. -/
def tokN (k : ℕ) : List BSym := (Nat.bits k).map dg

lemma tokN_no_sep (k : ℕ) : BSym.sep ∉ tokN k := fun h => digits_no_sep k _ h rfl

lemma encNats_toks (e : BSym → A) : ∀ d : List ℕ, (encNats d).map e = toksE e (d.map tokN) := by
  intro d
  induction d with
  | nil => rfl
  | cons k d ih => rw [encNats_cons, encNat_dg, List.map_cons, toksE_cons, ← ih]; simp [tokN]

/-! ### skipping tokens -/

section Skip
variable {K : Type} [DecidableEq K]

def skipOne (W : K) (e : BSym → A) : StackProg K A :=
  .seq (.loop (fun h => (h W).isSome && !decide (h W = some (e .sep))) (popProg W)) (popProg W)

lemma exec_skipOne (W : K) (e : BSym → A) (he : Function.Injective e) (rest : List A) :
    ∀ (tok : List BSym) (s : K → List A), BSym.sep ∉ tok →
      s W = tok.map e ++ e .sep :: rest →
      ∃ n ≤ 3 * tok.length + 3, (skipOne W e).Exec s (Function.update s W rest) n := by
  have hl : ∀ (tok : List BSym) (s : K → List A), BSym.sep ∉ tok →
      s W = tok.map e ++ e .sep :: rest →
      (StackProg.loop (fun h => (h W).isSome && !decide (h W = some (e .sep))) (popProg W)).Exec s
        (Function.update s W (e .sep :: rest)) (3 * tok.length + 1) := by
    intro tok
    induction tok with
    | nil =>
      intro s _ hs
      have : Function.update s W (e .sep :: rest) = s := by
        funext k; by_cases hk : k = W
        · subst hk; simp [hs]
        · simp [hk]
      rw [this]
      exact StackProg.Exec.loopFalse (by simp [hs])
    | cons b tok ih =>
      intro s hsep hs
      have hb : b ≠ BSym.sep := fun h => hsep (h ▸ List.mem_cons_self)
      have e1 := exec_pop W s
      have e2 := ih (Function.update s W (s W).tail) (fun h => hsep (List.mem_cons_of_mem _ h))
        (by simp [hs])
      have hu : Function.update (Function.update s W (s W).tail) W (e .sep :: rest) =
          Function.update s W (e .sep :: rest) := by simp
      rw [hu] at e2
      have hne : e b ≠ e .sep := fun h => hb (he h)
      have e3 := StackProg.Exec.loopTrue
        (test := fun h => (h W).isSome && !decide (h W = some (e .sep)))
        (by simp [hs, hne]) e1 e2
      simp only [List.length_cons]
      have e : 3 * (tok.length + 1) + 1 = 1 + 1 + 1 + (3 * tok.length + 1) := by ring
      rw [e]; exact e3
  intro tok s hsep hs
  have e1 := hl tok s hsep hs
  have e2 := exec_pop W (Function.update s W (e .sep :: rest))
  have hu : Function.update (Function.update s W (e .sep :: rest)) W
      ((Function.update s W (e .sep :: rest)) W).tail = Function.update s W rest := by simp
  rw [hu] at e2
  exact ⟨_, by omega, StackProg.Exec.seq e1 e2⟩

def skipToks (cnt W : K) (e : BSym → A) : StackProg K A :=
  .loop (fun h => (h cnt).isSome) (.seq (popProg cnt) (skipOne W e))

lemma exec_skipToks (cnt W : K) (hcW : cnt ≠ W) (e : BSym → A) (he : Function.Injective e)
    (mk : A) (rest : List A) :
    ∀ (k : ℕ) (ts : List (List BSym)) (s : K → List A),
      (∀ t ∈ ts, BSym.sep ∉ t) → k ≤ ts.length →
      s cnt = List.replicate k mk → s W = toksE e ts ++ rest →
      ∃ n ≤ 7 * (s W).length + 1, (skipToks cnt W e).Exec s
        (Function.update (Function.update s cnt []) W (toksE e (ts.drop k) ++ rest)) n := by
  intro k
  induction k with
  | zero =>
    intro ts s _ _ hc hW
    refine ⟨1, by omega, ?_⟩
    have : Function.update (Function.update s cnt []) W (toksE e (ts.drop 0) ++ rest) = s := by
      funext j
      by_cases h1 : j = W
      · subst h1; simp [hW]
      · by_cases h2 : j = cnt
        · subst h2; simp [hc, h1]
        · simp [h1, h2]
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hc])
  | succ k ih =>
    intro ts s hts hk hc hW
    rcases ts with _ | ⟨t, ts⟩
    · simp at hk
    have ht : BSym.sep ∉ t := hts t List.mem_cons_self
    have e1 := exec_pop cnt s
    set s1 := Function.update s cnt (s cnt).tail with hs1
    have hs1W : s1 W = t.map e ++ e .sep :: (toksE e ts ++ rest) := by
      simp [hs1, Ne.symm hcW, hW, toksE_cons]
    obtain ⟨n2, hn2, e2⟩ := exec_skipOne W e he (toksE e ts ++ rest) t s1 ht hs1W
    set s2 := Function.update s1 W (toksE e ts ++ rest) with hs2
    obtain ⟨n3, hn3, e3⟩ := ih ts s2 (fun t' h' => hts t' (List.mem_cons_of_mem _ h'))
      (by simp at hk; omega) (by simp [hs2, hs1, hcW, hc]) (by simp [hs2])
    have hpost : Function.update (Function.update s2 cnt []) W (toksE e (ts.drop k) ++ rest) =
        Function.update (Function.update s cnt []) W (toksE e ((t :: ts).drop (k + 1)) ++ rest) := by
      funext j
      by_cases h1 : j = W
      · subst h1; simp
      · by_cases h2 : j = cnt
        · subst h2; simp [h1]
        · simp [hs2, hs1, h1, h2]
    rw [hpost] at e3
    refine ⟨1 + (1 + 1 + n2) + 1 + n3, ?_, StackProg.Exec.loopTrue (by simp [hc])
      (StackProg.Exec.seq e1 e2) e3⟩
    have hl : (s W).length = t.length + 1 + (s2 W).length := by
      simp [hs2, hW, toksE_cons]; omega
    rw [hl]; omega

end Skip

/-! ### comparing two natural-number tokens -/

section Cmp
variable {K : Type} [DecidableEq K]

def isDig (e : BSym → A) (o : Option A) : Bool :=
  decide (o = some (e .zero)) || decide (o = some (e .one))

def stSym (b : Bool) : A := if b then ι1 .one else ι1 .zero

def cmpAct (X Y St : K) (e : BSym → A) (h : K → Option A) (k : K) : StackAct A :=
  if k = X ∨ k = Y then .pop
  else if k = St then
    (if h X = h Y then .keep else if h X = some (e .zero) then .push (stSym true)
      else .push (stSym false))
  else .keep

def cmpLoop (X Y St : K) (e : BSym → A) : StackProg K A :=
  .loop (fun h => isDig e (h X) && isDig e (h Y)) (.act (cmpAct X Y St e))

/-- what the compare loop pushes on `St` (stack order). -/
def cmpPush : List Bool → List Bool → List A
  | a :: as, b :: bs => cmpPush as bs ++ (if a = b then [] else [stSym b])
  | _, _ => []

lemma cmpPush_head : ∀ (as bs : List Bool) (l : List A),
    (cmpPush as bs ++ l).head? = (lastDiff as bs).elim l.head? (fun r => some (stSym r)) := by
  intro as
  induction as with
  | nil => intro bs l; simp [cmpPush, lastDiff]
  | cons a as ih =>
    intro bs l
    rcases bs with _ | ⟨b, bs⟩
    · simp [cmpPush, lastDiff]
    simp only [cmpPush, lastDiff, List.append_assoc]
    rw [ih]
    cases lastDiff as bs with
    | none => by_cases hab : a = b <;> simp [hab]
    | some r => rfl

lemma isDig_dg (e : BSym → A) (b : Bool) : isDig e (some (e (dg b))) = true := by
  cases b <;> simp [isDig, dg]

lemma exec_cmp (X Y St : K) (hXY : X ≠ Y) (hXS : X ≠ St) (hYS : Y ≠ St) (e : BSym → A)
    (he : Function.Injective e) (rX rY : List A) (hrX : isDig e rX.head? = false)
    (hrY : isDig e rY.head? = false) :
    ∀ (as bs : List Bool) (s : K → List A),
      s X = as.map (e ∘ dg) ++ rX → s Y = bs.map (e ∘ dg) ++ rY →
      (cmpLoop X Y St e).Exec s
        (Function.update (Function.update (Function.update s
          X ((as.drop (min as.length bs.length)).map (e ∘ dg) ++ rX))
          Y ((bs.drop (min as.length bs.length)).map (e ∘ dg) ++ rY))
          St (cmpPush as bs ++ s St)) (3 * min as.length bs.length + 1) := by
  intro as
  induction as with
  | nil =>
    intro bs s hX hY
    have : Function.update (Function.update (Function.update s
        X ((([] : List Bool).drop (min 0 bs.length)).map (e ∘ dg) ++ rX))
        Y ((bs.drop (min 0 bs.length)).map (e ∘ dg) ++ rY)) St (cmpPush [] bs ++ s St) = s := by
      funext k
      by_cases h1 : k = St
      · subst h1; simp [cmpPush]
      · by_cases h2 : k = Y
        · subst h2; simp [h1, hY]
        · by_cases h3 : k = X
          · subst h3; simp [h1, h2, hX]
          · simp [h1, h2, h3]
    simp only [List.length_nil] at this ⊢
    rw [this]
    exact StackProg.Exec.loopFalse (by simp [hX, hrX])
  | cons a as ih =>
    intro bs s hX hY
    rcases bs with _ | ⟨b, bs⟩
    · have : Function.update (Function.update (Function.update s
          X (((a :: as).drop (min (a :: as).length 0)).map (e ∘ dg) ++ rX))
          Y ((([] : List Bool).drop (min (a :: as).length 0)).map (e ∘ dg) ++ rY))
          St (cmpPush (a :: as) [] ++ s St) = s := by
        funext k
        by_cases h1 : k = St
        · subst h1; simp [cmpPush]
        · by_cases h2 : k = Y
          · subst h2; simp [h1, hY]
          · by_cases h3 : k = X
            · subst h3; simp [h1, h2, hX]
            · simp [h1, h2, h3]
      simp only [List.length_nil] at this ⊢
      rw [this]
      exact StackProg.Exec.loopFalse (by simp [hY, hrY])
    · have e1 := StackProg.Exec.act (cmpAct X Y St e) s
      set s1 := StackProg.applyAct (cmpAct X Y St e) s with hs1
      have h1X : s1 X = as.map (e ∘ dg) ++ rX := by
        simp [hs1, StackProg.applyAct, cmpAct, StackAct.apply, hX]
      have h1Y : s1 Y = bs.map (e ∘ dg) ++ rY := by
        simp [hs1, StackProg.applyAct, cmpAct, StackAct.apply, hY, hXY]
      have hdg : ∀ x y : Bool, (e (dg x) = e (dg y)) ↔ x = y := by
        intro x y; constructor
        · intro h; have := he h; clear ih e1 h1X h1Y; cases x <;> cases y <;> simp_all [dg]
        · intro h; rw [h]
      have h1S : s1 St = (if a = b then [] else [stSym b]) ++ s St := by
        simp only [hs1, StackProg.applyAct, cmpAct, hX, hY, List.map_cons, List.cons_append,
          List.head?_cons, Option.some.injEq, Function.comp_apply, hXS.symm, hYS.symm, or_self,
          if_false, if_true]
        by_cases hab : a = b
        · subst hab; simp [StackAct.apply]
        · have hne : ¬ e (dg a) = e (dg b) := fun h => hab ((hdg a b).1 h)
          rw [if_neg hne]
          clear ih e1 h1X h1Y hdg; cases a <;> cases b <;> simp_all [StackAct.apply, dg, stSym]
      have e2 := ih bs s1 h1X h1Y
      have hpost : Function.update (Function.update (Function.update s1
          X ((as.drop (min as.length bs.length)).map (e ∘ dg) ++ rX))
          Y ((bs.drop (min as.length bs.length)).map (e ∘ dg) ++ rY))
          St (cmpPush as bs ++ s1 St) =
          Function.update (Function.update (Function.update s
          X (((a :: as).drop (min (a :: as).length (b :: bs).length)).map (e ∘ dg) ++ rX))
          Y (((b :: bs).drop (min (a :: as).length (b :: bs).length)).map (e ∘ dg) ++ rY))
          St (cmpPush (a :: as) (b :: bs) ++ s St) := by
        have hm : min (a :: as).length (b :: bs).length = min as.length bs.length + 1 := by
          simp [Nat.succ_min_succ]
        rw [hm]
        funext k
        by_cases k1 : k = St
        · subst k1; simp [h1S, cmpPush]
        · by_cases k2 : k = Y
          · subst k2; simp [k1]
          · by_cases k3 : k = X
            · subst k3; simp [k1, k2]
            · simp [k1, k2, k3, hs1, StackProg.applyAct, cmpAct, StackAct.apply]
      rw [hpost] at e2
      have e3 := StackProg.Exec.loopTrue (test := fun h => isDig e (h X) && isDig e (h Y))
        (by simp [hX, hY, isDig_dg]) e1 e2
      have hm : min (a :: as).length (b :: bs).length = min as.length bs.length + 1 := by
        simp [Nat.succ_min_succ]
      have e : 3 * min (a :: as).length (b :: bs).length + 1 =
          1 + 1 + 1 + (3 * min as.length bs.length + 1) := by
        rw [hm]; ring
      rw [e]; exact e3

/-- the final test after the compare loop: `X < Y`. -/
def ltTest (X Y St : K) (e : BSym → A) (h : K → Option A) : Bool :=
  (decide (h X = some (e .sep)) && isDig e (h Y)) ||
    (decide (h X = some (e .sep)) && decide (h Y = some (e .sep)) &&
      decide (h St = some (stSym true)))

lemma cmp_lt (X Y St : K) (hXY : X ≠ Y) (hXS : X ≠ St) (hYS : Y ≠ St) (e : BSym → A)
    (he : Function.Injective e) (a b : ℕ) (rX rY : List A) (s : K → List A) (hS : s St = []) :
    ltTest X Y St e (fun k => (Function.update (Function.update (Function.update s
          X (((Nat.bits a).drop (min (Nat.bits a).length (Nat.bits b).length)).map (e ∘ dg) ++
            e .sep :: rX))
          Y (((Nat.bits b).drop (min (Nat.bits a).length (Nat.bits b).length)).map (e ∘ dg) ++
            e .sep :: rY))
          St (cmpPush (Nat.bits a) (Nat.bits b) ++ s St) k).head?) = decide (a < b) := by
  have hsepdg : ∀ x : Bool, e (dg x) ≠ e .sep := by
    intro x h; have := he h; cases x <;> simp [dg] at this
  have hsepdig : isDig e (some (e .sep)) = false := by
    simp only [isDig, Option.some.injEq]
    have h1 : e .sep ≠ e .zero := fun h => by have := he h; cases this
    have h2 : e .sep ≠ e .one := fun h => by have := he h; cases this
    simp [h1, h2]
  have hSne : stSym true ≠ stSym false := by simp [stSym, ι1]
  rcases lt_trichotomy (Nat.bits a).length (Nat.bits b).length with hlt | heq | hgt
  · have hmin : min (Nat.bits a).length (Nat.bits b).length = (Nat.bits a).length :=
      min_eq_left hlt.le
    rw [hmin]
    obtain ⟨x, l, hxl⟩ : ∃ x l, (Nat.bits b).drop (Nat.bits a).length = x :: l := by
      rcases h : (Nat.bits b).drop (Nat.bits a).length with _ | ⟨x, l⟩
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨x, l, rfl⟩
    have hab : a < b := lt_of_bits_len hlt
    simp [ltTest, hXY, hXS, hYS, Ne.symm hXY, Ne.symm hXS, Ne.symm hYS, hxl, isDig_dg, hab]
  · rw [heq, min_self]
    have hab := lastDiff_eq (Nat.bits a) (Nat.bits b) heq
    rw [bval_bits, bval_bits] at hab
    have hh : (cmpPush (Nat.bits a) (Nat.bits b) ++ s St).head? =
        (lastDiff (Nat.bits a) (Nat.bits b)).elim none (fun r => some (stSym r)) := by
      rw [cmpPush_head, hS]; rfl
    have hda : (Nat.bits a).drop (Nat.bits b).length = [] := by simp [heq]
    simp only [ltTest, Function.update_apply, hXY, hXS, hYS, Ne.symm hXY, Ne.symm hXS,
      Ne.symm hYS, if_true, if_false, hda, List.drop_length, List.map_nil, List.nil_append,
      List.head?_cons, hsepdig, Bool.and_false, Bool.false_or, decide_true, Bool.true_and, hh]
    rw [hab]
    by_cases h1 : a < b
    · simp [h1]
    · by_cases h2 : b < a
      · simp [h1, h2, hSne, hSne.symm]
      · simp [h1, h2]
  · have hmin : min (Nat.bits a).length (Nat.bits b).length = (Nat.bits b).length :=
      min_eq_right hgt.le
    rw [hmin]
    obtain ⟨x, l, hxl⟩ : ∃ x l, (Nat.bits a).drop (Nat.bits b).length = x :: l := by
      rcases h : (Nat.bits a).drop (Nat.bits b).length with _ | ⟨x, l⟩
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨x, l, rfl⟩
    have hab : ¬ a < b := not_lt.2 (lt_of_bits_len hgt).le
    simp [ltTest, hXY, hXS, hYS, Ne.symm hXY, Ne.symm hXS, Ne.symm hYS, hxl, hsepdg, hab]

end Cmp

/-! ### generic counted loop, skipping a possibly missing token -/

section For
variable {K : Type} [DecidableEq K]

/-- a loop whose body pops the counter `C` once per round, specified by an invariant. -/
lemma exec_for (C : K) (body : StackProg K A) (mk : A) (Inv : ℕ → (K → List A) → Prop) (n T : ℕ)
    (hbody : ∀ k < n, ∀ s, Inv k s → s C = List.replicate (n - k) mk →
      ∃ s' t, t ≤ T ∧ body.Exec s s' t ∧ Inv (k + 1) s' ∧
        s' C = List.replicate (n - k - 1) mk) :
    ∀ s, Inv 0 s → s C = List.replicate n mk →
      ∃ s' t, t ≤ n * (T + 2) + 1 ∧
        (StackProg.loop (fun h => (h C).isSome) body).Exec s s' t ∧ Inv n s' := by
  have key : ∀ r, r ≤ n → ∀ s, Inv (n - r) s → s C = List.replicate r mk →
      ∃ s' t, t ≤ r * (T + 2) + 1 ∧
        (StackProg.loop (fun h => (h C).isSome) body).Exec s s' t ∧ Inv n s' := by
    intro r
    induction r with
    | zero =>
      intro _ s hI hC
      exact ⟨s, 1, by omega, StackProg.Exec.loopFalse (by simp [hC]), by simpa using hI⟩
    | succ r ih =>
      intro hr s hI hC
      obtain ⟨s1, t1, ht1, e1, hI1, hC1⟩ :=
        hbody (n - (r + 1)) (by omega) s hI (by rw [hC]; congr 1; omega)
      have hk : n - (r + 1) + 1 = n - r := by omega
      rw [hk] at hI1
      obtain ⟨s2, t2, ht2, e2, hI2⟩ := ih (by omega) s1 hI1 (by rw [hC1]; congr 1; omega)
      refine ⟨s2, 1 + t1 + 1 + t2, ?_, StackProg.Exec.loopTrue (by simp [hC]) e1 e2, hI2⟩
      have : (r + 1) * (T + 2) = r * (T + 2) + T + 2 := by ring
      omega
  intro s hI hC
  exact key n le_rfl s (by simpa using hI) hC

lemma exec_skipOne' (W : K) (e : BSym → A) (he : Function.Injective e) :
    ∀ (ts : List (List BSym)) (s : K → List A), (∀ t ∈ ts, BSym.sep ∉ t) →
      s W = toksE e ts →
      ∃ n ≤ 3 * (s W).length + 3, (skipOne W e).Exec s (Function.update s W (toksE e ts.tail)) n := by
  intro ts s hts hW
  rcases ts with _ | ⟨t, ts⟩
  · have e1 : (StackProg.loop (fun h => (h W).isSome && !decide (h W = some (e .sep)))
        (popProg W)).Exec s s 1 := StackProg.Exec.loopFalse (by simp [hW, toksE_nil])
    have e2 := exec_pop W s
    rw [hW, toksE_nil] at e2
    exact ⟨1 + 1 + 1, by omega, StackProg.Exec.seq e1 e2⟩
  · obtain ⟨n, hn, h⟩ := exec_skipOne W e he (toksE e ts) t s (hts t List.mem_cons_self)
      (by rw [hW, toksE_cons])
    refine ⟨n, ?_, h⟩
    rw [hW, toksE_cons]; simp; omega

end For

/-! ### generic one-step helpers and the "token = 1" reader -/

section Gen
variable {K : Type} [DecidableEq K]

lemma ι1_inj : Function.Injective ι1 := fun a b h => by simpa [ι1] using h
lemma ι2_inj : Function.Injective ι2 := fun a b h => by simpa [ι2] using h

lemma exec_congrG {p : StackProg K A} {s t t' : K → List A} {n : ℕ} (h : p.Exec s t n)
    (e : t = t') : p.Exec s t' n := e ▸ h

def skipP : StackProg K A := .act (fun _ _ => .keep)

lemma exec_skipP (s : K → List A) : (skipP : StackProg K A).Exec s s 1 := by
  unfold skipP
  refine exec_congrG (StackProg.Exec.act _ s) ?_
  funext k; simp [StackProg.applyAct, StackAct.apply]

def flagP (B : K) (t : (K → Option A) → Bool) : StackProg K A :=
  .act (fun h k => if k = B ∧ t h = true then .push mkA else .keep)

lemma exec_flagP (B : K) (t : (K → Option A) → Bool) (s : K → List A) :
    (flagP B t).Exec s (Function.update s B
      (if t (fun k => (s k).head?) = true then mkA :: s B else s B)) 1 := by
  unfold flagP
  refine exec_congrG (StackProg.Exec.act _ s) ?_
  funext k
  by_cases hk : k = B
  · subst hk
    by_cases ht : t (fun k => (s k).head?) = true <;> simp [StackProg.applyAct, StackAct.apply, ht]
  · simp [StackProg.applyAct, StackAct.apply, hk]

lemma exec_pushG (c : K) (a : A) (s : K → List A) :
    (pushProg c a).Exec s (Function.update s c (a :: s c)) 1 := by
  unfold pushProg
  refine exec_congrG (StackProg.Exec.act _ s) ?_
  funext k; by_cases k1 : k = c
  · subst k1; simp [StackProg.applyAct, StackAct.apply]
  · simp [StackProg.applyAct, StackAct.apply, k1]

lemma exec_clearG (c : K) (s : K → List A) :
    ∃ n ≤ 3 * (s c).length + 1, (clearProg c).Exec s (Function.update s c []) n := by
  obtain ⟨n, hn, h⟩ := exec_transfer c (fun _ => false) (s c) s rfl
  refine ⟨n, hn, exec_congrG h ?_⟩
  funext k; by_cases k1 : k = c
  · subst k1; simp [transferStore]
  · simp [transferStore, k1]

/-- read one integer token from `W`; push a mark on `F` iff the token is the integer `1`. -/
def readFlag (W F : K) : StackProg K A :=
  .seq (.branch (fun h => decide (h W = some (ι1 .one)))
    (.seq (popProg W) (.branch (fun h => decide (h W = some (ι1 .sep))) (pushProg F mkA) skipP))
    skipP) (skipOne W ι1)

lemma exec_readFlag (W F : K) (hWF : W ≠ F) :
    ∀ (ts : List (List BSym)) (s : K → List A), (∀ t ∈ ts, BSym.sep ∉ t) →
      s W = toksE ι1 ts → s F = [] →
      ∃ n ≤ 3 * (s W).length + 10, (readFlag W F).Exec s
        (Function.update (Function.update s W (toksE ι1 ts.tail)) F
          (if ts.head? = some [BSym.one] then [mkA] else [])) n := by
  intro ts s hts hW hF
  have hsep1 : ι1 BSym.sep ≠ ι1 BSym.one := fun h => by cases ι1_inj h
  rcases ts with _ | ⟨t, ts⟩
  · -- no token left
    have e1 : (StackProg.branch (fun h => decide (h W = some (ι1 .one)))
        (.seq (popProg W) (.branch (fun h => decide (h W = some (ι1 .sep))) (pushProg F mkA) skipP))
        skipP).Exec s s (1 + 1) :=
      StackProg.Exec.branchFalse (by simp [hW, toksE_nil]) (exec_skipP s)
    obtain ⟨n2, hn2, e2⟩ := exec_skipOne' W ι1 ι1_inj [] s (by simp) hW
    refine ⟨1 + 1 + 1 + n2, by omega, exec_congrG (StackProg.Exec.seq e1 e2) ?_⟩
    funext k; by_cases k1 : k = F
    · subst k1; simp [hF, Ne.symm hWF]
    · simp [k1]
  have ht : BSym.sep ∉ t := hts t List.mem_cons_self
  have hW' : s W = t.map ι1 ++ ι1 .sep :: toksE ι1 ts := by rw [hW, toksE_cons]
  by_cases hone : ∃ t', t = BSym.one :: t'
  · obtain ⟨t', rfl⟩ := hone
    have ht' : BSym.sep ∉ t' := fun h => ht (List.mem_cons_of_mem _ h)
    have e0 := exec_pop W s
    set s1 := Function.update s W (s W).tail with hs1
    have hs1W : s1 W = t'.map ι1 ++ ι1 .sep :: toksE ι1 ts := by simp [hs1, hW']
    rcases t' with _ | ⟨b, t''⟩
    · -- the token is exactly `1`
      have e2 := exec_pushG F mkA s1
      have e3 := StackProg.Exec.branchTrue (test := fun h => decide (h W = some (ι1 .sep)))
        (q := skipP) (by simp [hs1W]) e2
      have e4 := StackProg.Exec.branchTrue (test := fun h => decide (h W = some (ι1 .one)))
        (q := skipP) (by simp [hW', ι1]) (StackProg.Exec.seq e0 e3)
      obtain ⟨n5, hn5, e5⟩ := exec_skipOne W ι1 ι1_inj (toksE ι1 ts) [] (Function.update s1 F (mkA :: s1 F))
        (by simp) (by rw [Function.update_of_ne hWF, hs1W])
      refine ⟨_, ?_, exec_congrG (StackProg.Exec.seq e4 e5) ?_⟩
      · simp at hn5; omega
      · funext k
        by_cases k1 : k = F
        · subst k1; simp [hs1, hF, Ne.symm hWF]
        · by_cases k2 : k = W
          · subst k2; simp [k1]
          · simp [hs1, k1, k2]
    · -- the token starts with `1` but is longer
      have hb : b ≠ BSym.sep := fun h => ht' (h ▸ List.mem_cons_self)
      have hbne : ι1 b ≠ ι1 BSym.sep := fun h => hb (ι1_inj h)
      have e3 := StackProg.Exec.branchFalse (test := fun h => decide (h W = some (ι1 .sep)))
        (p := pushProg F mkA) (by simp [hs1W, hbne]) (exec_skipP s1)
      have e4 := StackProg.Exec.branchTrue (test := fun h => decide (h W = some (ι1 .one)))
        (q := skipP) (by simp [hW', ι1]) (StackProg.Exec.seq e0 e3)
      obtain ⟨n5, hn5, e5⟩ := exec_skipOne W ι1 ι1_inj (toksE ι1 ts) (b :: t'') s1 ht' hs1W
      refine ⟨_, ?_, exec_congrG (StackProg.Exec.seq e4 e5) ?_⟩
      · rw [hW']; simp at hn5 ⊢; omega
      · funext k
        by_cases k1 : k = F
        · subst k1; simp [hs1, hF, Ne.symm hWF]
        · by_cases k2 : k = W
          · subst k2; simp [k1]
          · simp [hs1, k1, k2]
  · -- the token does not start with `1`
    have htop : (s W).head? ≠ some (ι1 BSym.one) := by
      rw [hW']
      rcases t with _ | ⟨b, t'⟩
      · simpa using hsep1
      · intro h
        simp only [List.map_cons, List.cons_append, List.head?_cons, Option.some.injEq] at h
        exact hone ⟨t', by rw [ι1_inj h]⟩
    have e1 := StackProg.Exec.branchFalse (test := fun h => decide (h W = some (ι1 .one)))
      (p := .seq (popProg W) (.branch (fun h => decide (h W = some (ι1 .sep))) (pushProg F mkA) skipP))
      (by simpa using htop) (exec_skipP s)
    obtain ⟨n2, hn2, e2⟩ := exec_skipOne W ι1 ι1_inj (toksE ι1 ts) t s ht hW'
    have hnot : ¬ (t = [BSym.one]) := fun h => hone ⟨[], h⟩
    refine ⟨1 + 1 + 1 + n2, ?_, exec_congrG (StackProg.Exec.seq e1 e2) ?_⟩
    · rw [hW']; simp; omega
    · funext k
      by_cases k1 : k = F
      · subst k1; simp [hF, Ne.symm hWF, hnot]
      · simp [k1]

end Gen

end D0bfT

/-! ## Library part 3 (namespace D0bfS): streaming comparison of two sums of binary numbers -/

namespace D0bfS
open D0bfL D0bfT

/-- a digit symbol of either part. -/
def digA (o : Option A) : Bool :=
  decide (o = some (ι1 .zero)) || decide (o = some (ι1 .one)) ||
  decide (o = some (ι2 .zero)) || decide (o = some (ι2 .one))

def oneA (o : Option A) : Bool := decide (o = some (ι1 .one)) || decide (o = some (ι2 .one))

/-- value of a digit list (least significant digit first). -/
def dval (l : List A) : ℕ := bval (l.map (fun a => oneA (some a)))

/-- the lowest digit of a digit list (0 when empty). -/
def dtop : List A → ℕ
  | [] => 0
  | a :: _ => (oneA (some a)).toNat

lemma dval_split (l : List A) : dval l = dtop l + 2 * dval l.tail := by
  cases l with
  | nil => simp [dval, dtop, bval]
  | cons a l => simp only [dval, dtop, List.map_cons, bval_cons, List.tail_cons]; ring

def cv (o : Option A) : ℕ := if o.isSome then 1 else 0
def dvo (o : Option A) : ℕ := if oneA o then 1 else 0

lemma oneA_of_not_dig {o : Option A} (h : digA o = false) : oneA o = false := by
  simp only [digA, oneA, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h ⊢
  tauto

lemma dvo_head (l r : List A) (hr : digA r.head? = false) : dvo (l ++ r).head? = dtop l := by
  cases l with
  | nil => simp [dvo, dtop, oneA_of_not_dig hr]
  | cons a l =>
    simp only [dvo, dtop, List.cons_append, List.head?_cons]
    rcases Bool.eq_false_or_eq_true (oneA (some a)) with h | h <;> simp [h]

lemma dig_head (l r : List A) (hl : ∀ a ∈ l, digA (some a) = true) (hr : digA r.head? = false) :
    digA (l ++ r).head? = !l.isEmpty := by
  cases l with
  | nil => simpa using hr
  | cons a l => simpa using hl a List.mem_cons_self

lemma tail_pop (l r : List A) (hl : ∀ a ∈ l, digA (some a) = true) (hr : digA r.head? = false) :
    (if digA (l ++ r).head? = true then StackAct.pop else StackAct.keep).apply (l ++ r) =
      l.tail ++ r := by
  rw [dig_head l r hl hr]
  cases l with
  | nil => simp [StackAct.apply]
  | cons a l => simp [StackAct.apply]

/-- the comparison result as the top of the state stack. -/
def scRes (X Y : ℕ) (o : Option A) : Option A :=
  if X < Y then some (stSym true) else if Y < X then some (stSym false) else o

lemma scRes_step (X Y b1 b2 : ℕ) (hb1 : b1 < 2) (hb2 : b2 < 2) (o : Option A) :
    scRes (b1 + 2 * X) (b2 + 2 * Y) o =
      scRes X Y (if b1 % 2 = b2 % 2 then o else some (stSym (decide (b2 % 2 = 1)))) := by
  unfold scRes
  interval_cases b1 <;> interval_cases b2 <;> simp <;> split_ifs <;> first | rfl | omega

section Sum
variable {K : Type} [DecidableEq K]

def sumAct (X1 X2 Y1 Y2 C1 C2 St : K) (mk : A) (h : K → Option A) (k : K) : StackAct A :=
  if k = X1 ∨ k = X2 ∨ k = Y1 ∨ k = Y2 then (if digA (h k) then .pop else .keep)
  else if k = C1 then
    (if 2 ≤ dvo (h X1) + dvo (h X2) + cv (h C1) then (if (h C1).isSome then .keep else .push mk)
      else (if (h C1).isSome then .pop else .keep))
  else if k = C2 then
    (if 2 ≤ dvo (h Y1) + dvo (h Y2) + cv (h C2) then (if (h C2).isSome then .keep else .push mk)
      else (if (h C2).isSome then .pop else .keep))
  else if k = St then
    (if (dvo (h X1) + dvo (h X2) + cv (h C1)) % 2 = (dvo (h Y1) + dvo (h Y2) + cv (h C2)) % 2
      then .keep
      else .push (stSym (decide ((dvo (h Y1) + dvo (h Y2) + cv (h C2)) % 2 = 1))))
  else .keep

def sumTest (X1 X2 Y1 Y2 C1 C2 : K) (h : K → Option A) : Bool :=
  digA (h X1) || digA (h X2) || digA (h Y1) || digA (h Y2) || (h C1).isSome || (h C2).isSome

def sumLoop (X1 X2 Y1 Y2 C1 C2 St : K) (mk : A) : StackProg K A :=
  .loop (sumTest X1 X2 Y1 Y2 C1 C2) (.act (sumAct X1 X2 Y1 Y2 C1 C2 St mk))

def cst (mk : A) (b : Bool) : List A := if b then [mk] else []

lemma cv_cst (mk : A) (b : Bool) : cv (cst mk b).head? = b.toNat := by cases b <;> rfl

lemma carry_act (mk : A) (c : Bool) (v : ℕ) :
    (if 2 ≤ v + cv (cst mk c).head? then
        (if ((cst mk c).head?).isSome then StackAct.keep else .push mk)
      else (if ((cst mk c).head?).isSome then .pop else .keep)).apply (cst mk c) =
      cst mk (decide (2 ≤ v + c.toNat)) := by
  cases c <;> by_cases h : 2 ≤ v <;> by_cases h1 : 2 ≤ v + 1 <;>
    simp [cst, cv, StackAct.apply, h, h1]

/-- the state after one round of the sum-compare loop. -/
def sumNext (X1 X2 Y1 Y2 C1 C2 St : K) (mk : A) (s : K → List A) (l1 l2 l3 l4 r1 r2 r3 r4 : List A)
    (c1 c2 : Bool) : K → List A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s X1 (l1.tail ++ r1)) X2 (l2.tail ++ r2)) Y1
    (l3.tail ++ r3)) Y2 (l4.tail ++ r4)) C1 (cst mk (decide (2 ≤ dtop l1 + dtop l2 + c1.toNat))))
    C2 (cst mk (decide (2 ≤ dtop l3 + dtop l4 + c2.toNat)))) St
    ((if (dtop l1 + dtop l2 + c1.toNat) % 2 = (dtop l3 + dtop l4 + c2.toNat) % 2 then []
      else [stSym (decide ((dtop l3 + dtop l4 + c2.toNat) % 2 = 1))]) ++ s St)

set_option maxHeartbeats 2000000 in
lemma sum_act_eq (X1 X2 Y1 Y2 C1 C2 St : K)
    (h12 : X1 ≠ X2) (h13 : X1 ≠ Y1) (h14 : X1 ≠ Y2) (h15 : X1 ≠ C1) (h16 : X1 ≠ C2) (h17 : X1 ≠ St)
    (h23 : X2 ≠ Y1) (h24 : X2 ≠ Y2) (h25 : X2 ≠ C1) (h26 : X2 ≠ C2) (h27 : X2 ≠ St)
    (h34 : Y1 ≠ Y2) (h35 : Y1 ≠ C1) (h36 : Y1 ≠ C2) (h37 : Y1 ≠ St)
    (h45 : Y2 ≠ C1) (h46 : Y2 ≠ C2) (h47 : Y2 ≠ St)
    (h56 : C1 ≠ C2) (h57 : C1 ≠ St) (h67 : C2 ≠ St)
    (mk : A) (r1 r2 r3 r4 : List A)
    (hr1 : digA r1.head? = false) (hr2 : digA r2.head? = false)
    (hr3 : digA r3.head? = false) (hr4 : digA r4.head? = false)
    (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (s : K → List A)
    (hl1 : ∀ a ∈ l1, digA (some a) = true) (hl2 : ∀ a ∈ l2, digA (some a) = true)
    (hl3 : ∀ a ∈ l3, digA (some a) = true) (hl4 : ∀ a ∈ l4, digA (some a) = true)
    (hX1 : s X1 = l1 ++ r1) (hX2 : s X2 = l2 ++ r2) (hY1 : s Y1 = l3 ++ r3) (hY2 : s Y2 = l4 ++ r4)
    (hC1 : s C1 = cst mk c1) (hC2 : s C2 = cst mk c2) :
    StackProg.applyAct (sumAct X1 X2 Y1 Y2 C1 C2 St mk) s =
      sumNext X1 X2 Y1 Y2 C1 C2 St mk s l1 l2 l3 l4 r1 r2 r3 r4 c1 c2 := by
  have t1 : dvo (s X1).head? = dtop l1 := by rw [hX1]; exact dvo_head l1 r1 hr1
  have t2 : dvo (s X2).head? = dtop l2 := by rw [hX2]; exact dvo_head l2 r2 hr2
  have t3 : dvo (s Y1).head? = dtop l3 := by rw [hY1]; exact dvo_head l3 r3 hr3
  have t4 : dvo (s Y2).head? = dtop l4 := by rw [hY2]; exact dvo_head l4 r4 hr4
  have t5 : cv (s C1).head? = c1.toNat := by rw [hC1]; exact cv_cst mk c1
  have t6 : cv (s C2).head? = c2.toNat := by rw [hC2]; exact cv_cst mk c2
  funext k
  simp only [StackProg.applyAct, sumNext]
  by_cases k1 : k = X1
  · rw [k1]; simp only [sumAct, true_or, if_true]
    simp only [hX1]; rw [tail_pop l1 r1 hl1 hr1]; rw [Function.update_of_ne h17, Function.update_of_ne h16, Function.update_of_ne h15, Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12, Function.update_self]
  by_cases k2 : k = X2
  · rw [k2]; simp only [sumAct, true_or, or_true, if_true]
    simp only [hX2]; rw [tail_pop l2 r2 hl2 hr2]; rw [Function.update_of_ne h27, Function.update_of_ne h26, Function.update_of_ne h25, Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self]
  by_cases k3 : k = Y1
  · rw [k3]; simp only [sumAct, true_or, or_true, if_true]
    simp only [hY1]; rw [tail_pop l3 r3 hl3 hr3]; rw [Function.update_of_ne h37, Function.update_of_ne h36, Function.update_of_ne h35, Function.update_of_ne h34, Function.update_self]
  by_cases k4 : k = Y2
  · rw [k4]; simp only [sumAct, true_or, or_true, if_true]
    simp only [hY2]; rw [tail_pop l4 r4 hl4 hr4]; rw [Function.update_of_ne h47, Function.update_of_ne h46, Function.update_of_ne h45, Function.update_self]
  by_cases k5 : k = C1
  · rw [k5]
    simp only [sumAct, Ne.symm h15, Ne.symm h25, Ne.symm h35, Ne.symm h45, or_self, if_false,
      if_true]
    simp only [t1, t2, hC1]; rw [carry_act, Function.update_of_ne h57, Function.update_of_ne h56, Function.update_self]
  by_cases k6 : k = C2
  · rw [k6]
    simp only [sumAct, Ne.symm h16, Ne.symm h26, Ne.symm h36, Ne.symm h46, Ne.symm h56, or_self,
      if_false, if_true]
    simp only [t3, t4, hC2]; rw [carry_act, Function.update_of_ne h67, Function.update_self]
  by_cases k7 : k = St
  · rw [k7]
    simp only [sumAct, Ne.symm h17, Ne.symm h27, Ne.symm h37, Ne.symm h47, Ne.symm h57,
      Ne.symm h67, or_self, if_false, if_true]
    simp only [t1, t2, t3, t4, t5, t6, Function.update_self]
    split_ifs <;> simp [StackAct.apply]
  · simp [sumAct, k1, k2, k3, k4, k5, k6, k7, Function.update_apply, StackAct.apply]

set_option maxHeartbeats 2000000 in
lemma upd7_congr (X1 X2 Y1 Y2 C1 C2 St : K) (s s' : K → List A) (v1 v2 v3 v4 v5 v6 v7 w7 : List A)
    (h : ∀ k, k ≠ X1 → k ≠ X2 → k ≠ Y1 → k ≠ Y2 → k ≠ C1 → k ≠ C2 → k ≠ St → s k = s' k)
    (h7 : v7 = w7) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s X1 v1) X2 v2) Y1 v3) Y2 v4) C1 v5) C2 v6) St v7 =
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s' X1 v1) X2 v2) Y1 v3) Y2 v4) C1 v5) C2 v6) St w7 := by
  subst h7
  funext k
  by_cases k7 : k = St; · subst k7; simp
  by_cases k6 : k = C2; · subst k6; simp [k7]
  by_cases k5 : k = C1; · subst k5; simp [k7, k6]
  by_cases k4 : k = Y2; · subst k4; simp [k7, k6, k5]
  by_cases k3 : k = Y1; · subst k3; simp [k7, k6, k5, k4]
  by_cases k2 : k = X2; · subst k2; simp [k7, k6, k5, k4, k3]
  by_cases k1 : k = X1; · subst k1; simp [k7, k6, k5, k4, k3, k2]
  simp [Function.update_apply, k1, k2, k3, k4, k5, k6, k7, h k k1 k2 k3 k4 k5 k6 k7]

lemma dtop_le (l : List A) : dtop l ≤ 1 := by
  cases l with
  | nil => simp [dtop]
  | cons a l =>
    simp only [dtop]
    rcases Bool.eq_false_or_eq_true (oneA (some a)) with h | h <;> simp [h]

lemma val_step (l1 l2 : List A) (c : Bool) :
    dval l1 + dval l2 + c.toNat = (dtop l1 + dtop l2 + c.toNat) % 2 +
      2 * (dval l1.tail + dval l2.tail + (decide (2 ≤ dtop l1 + dtop l2 + c.toNat)).toNat) := by
  rw [dval_split l1, dval_split l2]
  have := dtop_le l1
  have := dtop_le l2
  have : c.toNat ≤ 1 := by cases c <;> simp
  by_cases h2 : 2 ≤ dtop l1 + dtop l2 + c.toNat <;> simp [h2] <;> omega

lemma fuel_step (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (m : ℕ)
    (hn : max (max l1.length l2.length) (max l3.length l4.length) + 1 ≤ m + 1 ∨
      (l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false))
    (hstop : ¬(l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false)) :
    max (max l1.tail.length l2.tail.length) (max l3.tail.length l4.tail.length) + 1 ≤ m ∨
      (l1.tail = [] ∧ l2.tail = [] ∧ l3.tail = [] ∧ l4.tail = [] ∧
        decide (2 ≤ dtop l1 + dtop l2 + c1.toNat) = false ∧
        decide (2 ≤ dtop l3 + dtop l4 + c2.toNat) = false) := by
  rcases hn with hn | hn
  · by_cases hall : l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = []
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hall
      right
      simp only [List.tail_nil, true_and, dtop, zero_add, decide_eq_false_iff_not]
      constructor <;> cases c1 <;> cases c2 <;> simp
    · left
      simp only [List.length_tail]
      have : 1 ≤ max (max l1.length l2.length) (max l3.length l4.length) := by
        by_contra hc
        apply hall
        simp only [not_le, Nat.lt_one_iff, Nat.max_eq_zero_iff, List.length_eq_zero_iff] at hc
        exact ⟨hc.1.1, hc.1.2, hc.2.1, hc.2.2⟩
      have hM : max (max (l1.length - 1) (l2.length - 1)) (max (l3.length - 1) (l4.length - 1)) ≤
          max (max l1.length l2.length) (max l3.length l4.length) - 1 :=
        max_le (max_le (Nat.sub_le_sub_right (le_trans (le_max_left _ _) (le_max_left _ _)) 1)
            (Nat.sub_le_sub_right (le_trans (le_max_right _ _) (le_max_left _ _)) 1))
          (max_le (Nat.sub_le_sub_right (le_trans (le_max_left _ _) (le_max_right _ _)) 1)
            (Nat.sub_le_sub_right (le_trans (le_max_right _ _) (le_max_right _ _)) 1))
      generalize max (max (l1.length - 1) (l2.length - 1)) (max (l3.length - 1) (l4.length - 1)) = K at hM ⊢
      generalize max (max l1.length l2.length) (max l3.length l4.length) = M at hM hn this
      omega
  · exact absurd hn hstop

lemma sum_test_true (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (mk : A)
    (h : ¬(l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false)) :
    (!l1.isEmpty || !l2.isEmpty || !l3.isEmpty || !l4.isEmpty || ((cst mk c1).head?).isSome ||
      ((cst mk c2).head?).isSome) = true := by
  cases l1 <;> cases l2 <;> cases l3 <;> cases l4 <;> cases c1 <;> cases c2 <;> simp_all [cst]

set_option maxHeartbeats 2000000 in
lemma exec_sum (X1 X2 Y1 Y2 C1 C2 St : K)
    (h12 : X1 ≠ X2) (h13 : X1 ≠ Y1) (h14 : X1 ≠ Y2) (h15 : X1 ≠ C1) (h16 : X1 ≠ C2) (h17 : X1 ≠ St)
    (h23 : X2 ≠ Y1) (h24 : X2 ≠ Y2) (h25 : X2 ≠ C1) (h26 : X2 ≠ C2) (h27 : X2 ≠ St)
    (h34 : Y1 ≠ Y2) (h35 : Y1 ≠ C1) (h36 : Y1 ≠ C2) (h37 : Y1 ≠ St)
    (h45 : Y2 ≠ C1) (h46 : Y2 ≠ C2) (h47 : Y2 ≠ St)
    (h56 : C1 ≠ C2) (h57 : C1 ≠ St) (h67 : C2 ≠ St)
    (mk : A) (r1 r2 r3 r4 : List A)
    (hr1 : digA r1.head? = false) (hr2 : digA r2.head? = false)
    (hr3 : digA r3.head? = false) (hr4 : digA r4.head? = false) :
    ∀ (n : ℕ) (l1 l2 l3 l4 : List A) (c1 c2 : Bool) (s : K → List A),
      (∀ a ∈ l1, digA (some a) = true) → (∀ a ∈ l2, digA (some a) = true) →
      (∀ a ∈ l3, digA (some a) = true) → (∀ a ∈ l4, digA (some a) = true) →
      s X1 = l1 ++ r1 → s X2 = l2 ++ r2 → s Y1 = l3 ++ r3 → s Y2 = l4 ++ r4 →
      s C1 = cst mk c1 → s C2 = cst mk c2 →
      (max (max l1.length l2.length) (max l3.length l4.length) + 1 ≤ n ∨
        (l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false)) →
      ∃ P t, t ≤ 3 * n + 1 ∧ P.length ≤ n ∧
        (sumLoop X1 X2 Y1 Y2 C1 C2 St mk).Exec s
          (Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update s X1 r1) X2 r2) Y1 r3) Y2 r4) C1 []) C2 [])
            St (P ++ s St)) t ∧
        (P ++ s St).head? = scRes (dval l1 + dval l2 + c1.toNat) (dval l3 + dval l4 + c2.toNat)
          (s St).head? := by
  have hstopcase : ∀ (n : ℕ) (s : K → List A), s X1 = [] ++ r1 → s X2 = [] ++ r2 →
      s Y1 = [] ++ r3 → s Y2 = [] ++ r4 → s C1 = cst mk false → s C2 = cst mk false →
      ∃ P t, t ≤ 3 * n + 1 ∧ P.length ≤ n ∧
        (sumLoop X1 X2 Y1 Y2 C1 C2 St mk).Exec s
          (Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update s X1 r1) X2 r2) Y1 r3) Y2 r4) C1 []) C2 [])
            St (P ++ s St)) t ∧
        (P ++ s St).head? = scRes (dval [] + dval [] + (false).toNat)
          (dval [] + dval [] + (false).toNat) (s St).head? := by
    intro n s hX1 hX2 hY1 hY2 hC1 hC2
    refine ⟨[], 1, by omega, by simp, ?_, by simp [scRes, dval, bval]⟩
    have hs : Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update s X1 r1) X2 r2) Y1 r3) Y2 r4) C1 []) C2 [])
        St ([] ++ s St) = s := by
      simp only [List.nil_append] at hX1 hX2 hY1 hY2
      funext k
      by_cases k7 : k = St; · subst k7; simp
      by_cases k6 : k = C2; · subst k6; simp [k7, hC2, cst]
      by_cases k5 : k = C1; · subst k5; simp [k7, k6, hC1, cst]
      by_cases k4 : k = Y2; · subst k4; simp [k7, k6, k5, hY2]
      by_cases k3 : k = Y1; · subst k3; simp [k7, k6, k5, k4, hY1]
      by_cases k2 : k = X2; · subst k2; simp [k7, k6, k5, k4, k3, hX2]
      by_cases k1 : k = X1; · subst k1; simp [k7, k6, k5, k4, k3, k2, hX1]
      simp [Function.update_apply, k1, k2, k3, k4, k5, k6, k7]
    rw [hs]
    refine StackProg.Exec.loopFalse ?_
    simp [sumTest, hX1, hX2, hY1, hY2, hC1, hC2, cst, hr1, hr2, hr3, hr4]
  intro n
  induction n with
  | zero =>
    intro l1 l2 l3 l4 c1 c2 s hl1 hl2 hl3 hl4 hX1 hX2 hY1 hY2 hC1 hC2 hn
    rcases hn with hn | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · omega
    exact hstopcase 0 s hX1 hX2 hY1 hY2 hC1 hC2
  | succ m ih =>
    intro l1 l2 l3 l4 c1 c2 s hl1 hl2 hl3 hl4 hX1 hX2 hY1 hY2 hC1 hC2 hn
    by_cases hstop : l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ c1 = false ∧ c2 = false
    · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hstop
      exact hstopcase (m + 1) s hX1 hX2 hY1 hY2 hC1 hC2
    have hact := sum_act_eq X1 X2 Y1 Y2 C1 C2 St h12 h13 h14 h15 h16 h17 h23 h24 h25 h26 h27
      h34 h35 h36 h37 h45 h46 h47 h56 h57 h67 mk r1 r2 r3 r4 hr1 hr2 hr3 hr4 l1 l2 l3 l4 c1 c2 s
      hl1 hl2 hl3 hl4 hX1 hX2 hY1 hY2 hC1 hC2
    set s' := sumNext X1 X2 Y1 Y2 C1 C2 St mk s l1 l2 l3 l4 r1 r2 r3 r4 c1 c2 with hs'
    obtain ⟨P, t, ht, hP, he, hhead⟩ := ih l1.tail l2.tail l3.tail l4.tail
      (decide (2 ≤ dtop l1 + dtop l2 + c1.toNat)) (decide (2 ≤ dtop l3 + dtop l4 + c2.toNat)) s'
      (fun a ha => hl1 a (List.mem_of_mem_tail ha))
      (fun a ha => hl2 a (List.mem_of_mem_tail ha)) (fun a ha => hl3 a (List.mem_of_mem_tail ha))
      (fun a ha => hl4 a (List.mem_of_mem_tail ha))
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h17, Function.update_of_ne h16, Function.update_of_ne h15, Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h27, Function.update_of_ne h26, Function.update_of_ne h25, Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h37, Function.update_of_ne h36, Function.update_of_ne h35, Function.update_of_ne h34, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h47, Function.update_of_ne h46, Function.update_of_ne h45, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h57, Function.update_of_ne h56, Function.update_self])
      (by simp only [hs', sumNext]; rw [Function.update_of_ne h67, Function.update_self]) (fuel_step l1 l2 l3 l4 c1 c2 m hn hstop)
    have htest : sumTest X1 X2 Y1 Y2 C1 C2 (fun k => (s k).head?) = true := by
      simp only [sumTest, hX1, hX2, hY1, hY2, hC1, hC2, dig_head l1 r1 hl1 hr1,
        dig_head l2 r2 hl2 hr2, dig_head l3 r3 hl3 hr3, dig_head l4 r4 hl4 hr4]
      exact sum_test_true l1 l2 l3 l4 c1 c2 mk hstop
    have hSt' : s' St = (if (dtop l1 + dtop l2 + c1.toNat) % 2 = (dtop l3 + dtop l4 + c2.toNat) % 2
        then [] else [stSym (decide ((dtop l3 + dtop l4 + c2.toNat) % 2 = 1))]) ++ s St := by
      simp only [hs', sumNext, Function.update_self]
    refine ⟨P ++ (if (dtop l1 + dtop l2 + c1.toNat) % 2 = (dtop l3 + dtop l4 + c2.toNat) % 2
        then [] else [stSym (decide ((dtop l3 + dtop l4 + c2.toNat) % 2 = 1))]),
      1 + 1 + 1 + t, by omega, ?_, ?_, ?_⟩
    · simp only [List.length_append]; split_ifs <;> simp <;> omega
    · have e1 := StackProg.Exec.act (sumAct X1 X2 Y1 Y2 C1 C2 St mk) s
      rw [hact] at e1
      refine StackProg.Exec.loopTrue htest e1 (exec_congrG he ?_)
      refine upd7_congr X1 X2 Y1 Y2 C1 C2 St s' s _ _ _ _ _ _ _ _ ?_ ?_
      · intro k k1 k2 k3 k4 k5 k6 k7
        simp only [hs', sumNext]
        rw [Function.update_of_ne k7, Function.update_of_ne k6, Function.update_of_ne k5,
          Function.update_of_ne k4, Function.update_of_ne k3, Function.update_of_ne k2,
          Function.update_of_ne k1]
      · rw [hSt', List.append_assoc]
    · rw [List.append_assoc, ← hSt', hhead, hSt', val_step l1 l2 c1, val_step l3 l4 c2,
        scRes_step _ _ _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
      simp only [Nat.mod_mod]
      split_ifs <;> simp

end Sum

/-! ### digit tokens of a natural number -/

lemma oneA_dg1 (b : Bool) : oneA (some (ι1 (dg b))) = b := by cases b <;> rfl
lemma oneA_dg2 (b : Bool) : oneA (some (ι2 (dg b))) = b := by cases b <;> rfl
lemma digA_dg1 (b : Bool) : digA (some (ι1 (dg b))) = true := by cases b <;> rfl
lemma digA_dg2 (b : Bool) : digA (some (ι2 (dg b))) = true := by cases b <;> rfl

lemma dval_bits1 (k : ℕ) : dval ((Nat.bits k).map (ι1 ∘ dg)) = k := by
  simp only [dval, List.map_map]
  have : ((fun a => oneA (some a)) ∘ ι1 ∘ dg) = id := by
    funext b; exact oneA_dg1 b
  rw [this, List.map_id, bval_bits]

lemma dval_bits2 (k : ℕ) : dval ((Nat.bits k).map (ι2 ∘ dg)) = k := by
  simp only [dval, List.map_map]
  have : ((fun a => oneA (some a)) ∘ ι2 ∘ dg) = id := by
    funext b; exact oneA_dg2 b
  rw [this, List.map_id, bval_bits]

lemma digs1 (k : ℕ) : ∀ a ∈ (Nat.bits k).map (ι1 ∘ dg), digA (some a) = true := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  exact digA_dg1 b

lemma digs2 (k : ℕ) : ∀ a ∈ (Nat.bits k).map (ι2 ∘ dg), digA (some a) = true := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  exact digA_dg2 b

lemma digA_sep1 : digA (some (ι1 .sep)) = false := rfl
lemma digA_sep2 : digA (some (ι2 .sep)) = false := rfl
lemma digA_minus : digA (some (ι1 .minus)) = false := rfl
lemma digA_none : digA (none : Option A) = false := rfl

end D0bfS

/-! ## Library part 4 (namespace D0bfU): a binary adder `X := X + Y` -/

namespace D0bfU
open D0bfL D0bfT D0bfS

def bitA (b : Bool) : A := ι1 (dg b)

lemma dval_cons_bit (b : Bool) (R : List A) : dval (bitA b :: R) = b.toNat + 2 * dval R := by
  unfold dval
  rw [List.map_cons, bval_cons, show oneA (some (bitA b)) = b from oneA_dg1 b]
  ring

lemma toNat_mod2 (x : ℕ) : (decide (x % 2 = 1)).toNat = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

section Add
variable {K : Type} [DecidableEq K]

def addAct (X Y C O : K) (mk : A) (h : K → Option A) (k : K) : StackAct A :=
  if k = X ∨ k = Y then (if digA (h k) then .pop else .keep)
  else if k = C then
    (if 2 ≤ dvo (h X) + dvo (h Y) + cv (h C) then (if (h C).isSome then .keep else .push mk)
      else (if (h C).isSome then .pop else .keep))
  else if k = O then .push (bitA (decide ((dvo (h X) + dvo (h Y) + cv (h C)) % 2 = 1)))
  else .keep

def addTest (X Y C : K) (h : K → Option A) : Bool := digA (h X) || digA (h Y) || (h C).isSome

def addLoop (X Y C O : K) (mk : A) : StackProg K A :=
  .loop (addTest X Y C) (.act (addAct X Y C O mk))

def addNext (X Y C O : K) (mk : A) (s : K → List A) (l1 l2 r1 r2 : List A) (c : Bool) :
    K → List A :=
  Function.update (Function.update (Function.update (Function.update s X (l1.tail ++ r1)) Y
    (l2.tail ++ r2)) C (cst mk (decide (2 ≤ dtop l1 + dtop l2 + c.toNat))))
    O (bitA (decide ((dtop l1 + dtop l2 + c.toNat) % 2 = 1)) :: s O)

set_option maxHeartbeats 1000000 in
lemma add_act_eq (X Y C O : K) (hXY : X ≠ Y) (hXC : X ≠ C) (hXO : X ≠ O) (hYC : Y ≠ C)
    (hYO : Y ≠ O) (hCO : C ≠ O)
    (mk : A) (r1 r2 : List A) (hr1 : digA r1.head? = false) (hr2 : digA r2.head? = false)
    (l1 l2 : List A) (c : Bool) (s : K → List A)
    (hl1 : ∀ a ∈ l1, digA (some a) = true) (hl2 : ∀ a ∈ l2, digA (some a) = true)
    (hX : s X = l1 ++ r1) (hY : s Y = l2 ++ r2) (hC : s C = cst mk c) :
    StackProg.applyAct (addAct X Y C O mk) s = addNext X Y C O mk s l1 l2 r1 r2 c := by
  have t1 : dvo (s X).head? = dtop l1 := by rw [hX]; exact dvo_head l1 r1 hr1
  have t2 : dvo (s Y).head? = dtop l2 := by rw [hY]; exact dvo_head l2 r2 hr2
  have t5 : cv (s C).head? = c.toNat := by rw [hC]; exact cv_cst mk c
  funext k
  simp only [StackProg.applyAct, addNext]
  by_cases k1 : k = X
  · rw [k1]; simp only [addAct, true_or, if_true]
    simp only [hX]; rw [tail_pop l1 r1 hl1 hr1]
    rw [Function.update_of_ne hXO, Function.update_of_ne hXC, Function.update_of_ne hXY,
      Function.update_self]
  by_cases k2 : k = Y
  · rw [k2]; simp only [addAct, true_or, or_true, if_true]
    simp only [hY]; rw [tail_pop l2 r2 hl2 hr2]
    rw [Function.update_of_ne hYO, Function.update_of_ne hYC, Function.update_self]
  by_cases k3 : k = C
  · rw [k3]
    simp only [addAct, Ne.symm hXC, Ne.symm hYC, or_self, if_false, if_true]
    simp only [t1, t2, hC]; rw [carry_act, Function.update_of_ne hCO, Function.update_self]
  by_cases k4 : k = O
  · rw [k4]
    simp only [addAct, Ne.symm hXO, Ne.symm hYO, Ne.symm hCO, or_self, if_false, if_true]
    simp only [t1, t2, t5, Function.update_self]
    simp [StackAct.apply]
  · simp [addAct, k1, k2, k3, k4, Function.update_apply, StackAct.apply]

set_option maxHeartbeats 1000000 in
lemma upd4_congr (X Y C O : K) (s s' : K → List A) (v1 v2 v3 v4 w4 : List A)
    (h : ∀ k, k ≠ X → k ≠ Y → k ≠ C → k ≠ O → s k = s' k) (h4 : v4 = w4) :
    Function.update (Function.update (Function.update (Function.update s X v1) Y v2) C v3) O v4 =
    Function.update (Function.update (Function.update (Function.update s' X v1) Y v2) C v3)
      O w4 := by
  subst h4
  funext k
  by_cases k4 : k = O; · subst k4; simp
  by_cases k3 : k = C; · subst k3; simp [k4]
  by_cases k2 : k = Y; · subst k2; simp [k4, k3]
  by_cases k1 : k = X; · subst k1; simp [k4, k3, k2]
  simp [Function.update_apply, k1, k2, k3, k4, h k k1 k2 k3 k4]

lemma add_fuel (l1 l2 : List A) (c : Bool) (m : ℕ)
    (hn : max l1.length l2.length + 1 ≤ m + 1 ∨ (l1 = [] ∧ l2 = [] ∧ c = false))
    (hst : ¬(l1 = [] ∧ l2 = [] ∧ c = false)) :
    max l1.tail.length l2.tail.length + 1 ≤ m ∨
      (l1.tail = [] ∧ l2.tail = [] ∧ decide (2 ≤ dtop l1 + dtop l2 + c.toNat) = false) := by
  rcases hn with hn | hn
  · by_cases hall : l1 = [] ∧ l2 = []
    · obtain ⟨rfl, rfl⟩ := hall
      right
      simp only [List.tail_nil, true_and, dtop, zero_add, decide_eq_false_iff_not]
      cases c <;> simp
    · left
      simp only [List.length_tail]
      have : 1 ≤ max l1.length l2.length := by
        by_contra hc
        apply hall
        simp only [not_le, Nat.lt_one_iff, Nat.max_eq_zero_iff, List.length_eq_zero_iff] at hc
        exact hc
      omega
  · exact absurd hn hst

set_option maxHeartbeats 2000000 in
lemma exec_add (X Y C O : K) (hXY : X ≠ Y) (hXC : X ≠ C) (hXO : X ≠ O) (hYC : Y ≠ C)
    (hYO : Y ≠ O) (hCO : C ≠ O)
    (mk : A) (r1 r2 : List A) (hr1 : digA r1.head? = false) (hr2 : digA r2.head? = false) :
    ∀ (n : ℕ) (l1 l2 : List A) (c : Bool) (s : K → List A),
      (∀ a ∈ l1, digA (some a) = true) → (∀ a ∈ l2, digA (some a) = true) →
      s X = l1 ++ r1 → s Y = l2 ++ r2 → s C = cst mk c →
      (max l1.length l2.length + 1 ≤ n ∨ (l1 = [] ∧ l2 = [] ∧ c = false)) →
      ∃ R t, t ≤ 3 * n + 1 ∧ R.length ≤ n ∧ (∀ a ∈ R, digA (some a) = true) ∧
        dval R = dval l1 + dval l2 + c.toNat ∧
        (addLoop X Y C O mk).Exec s
          (Function.update (Function.update (Function.update (Function.update s X r1) Y r2) C [])
            O (R.reverse ++ s O)) t := by
  have hstop : ∀ (n : ℕ) (s : K → List A), s X = [] ++ r1 → s Y = [] ++ r2 →
      s C = cst mk false →
      ∃ R t, t ≤ 3 * n + 1 ∧ R.length ≤ n ∧ (∀ a ∈ R, digA (some a) = true) ∧
        dval R = dval [] + dval [] + (false).toNat ∧
        (addLoop X Y C O mk).Exec s (Function.update (Function.update (Function.update
          (Function.update s X r1) Y r2) C []) O (R.reverse ++ s O)) t := by
    intro n s hX hY hC
    refine ⟨[], 1, by omega, by simp, by simp, by simp [dval, bval], ?_⟩
    have hs : Function.update (Function.update (Function.update (Function.update s X r1) Y r2)
        C []) O (([] : List A).reverse ++ s O) = s := by
      simp only [List.nil_append] at hX hY
      funext k
      by_cases k4 : k = O; · subst k4; simp
      by_cases k3 : k = C; · subst k3; simp [k4, hC, cst]
      by_cases k2 : k = Y; · subst k2; simp [k4, k3, hY]
      by_cases k1 : k = X; · subst k1; simp [k4, k3, k2, hX]
      simp [Function.update_apply, k1, k2, k3, k4]
    rw [hs]
    refine StackProg.Exec.loopFalse ?_
    simp [addTest, hX, hY, hC, cst, hr1, hr2]
  intro n
  induction n with
  | zero =>
    intro l1 l2 c s hl1 hl2 hX hY hC hn
    rcases hn with hn | ⟨rfl, rfl, rfl⟩
    · omega
    exact hstop 0 s hX hY hC
  | succ m ih =>
    intro l1 l2 c s hl1 hl2 hX hY hC hn
    by_cases hst : l1 = [] ∧ l2 = [] ∧ c = false
    · obtain ⟨rfl, rfl, rfl⟩ := hst
      exact hstop (m + 1) s hX hY hC
    have htest : addTest X Y C (fun k => (s k).head?) = true := by
      clear ih hn hstop
      simp only [addTest, hX, hY, hC, dig_head l1 r1 hl1 hr1, dig_head l2 r2 hl2 hr2]
      cases l1 <;> cases l2 <;> cases c <;> simp_all [cst]
    have hact := add_act_eq X Y C O hXY hXC hXO hYC hYO hCO mk r1 r2 hr1 hr2 l1 l2 c s hl1 hl2
      hX hY hC
    set s' := addNext X Y C O mk s l1 l2 r1 r2 c with hs'
    obtain ⟨R, t, ht, hR, hRd, hRv, he⟩ := ih l1.tail l2.tail
      (decide (2 ≤ dtop l1 + dtop l2 + c.toNat)) s'
      (fun a ha => hl1 a (List.mem_of_mem_tail ha)) (fun a ha => hl2 a (List.mem_of_mem_tail ha))
      (by simp only [hs', addNext]; rw [Function.update_of_ne hXO, Function.update_of_ne hXC,
        Function.update_of_ne hXY, Function.update_self])
      (by simp only [hs', addNext]; rw [Function.update_of_ne hYO, Function.update_of_ne hYC,
        Function.update_self])
      (by simp only [hs', addNext]; rw [Function.update_of_ne hCO, Function.update_self])
      (add_fuel l1 l2 c m hn hst)
    have hO' : s' O = bitA (decide ((dtop l1 + dtop l2 + c.toNat) % 2 = 1)) :: s O := by
      simp only [hs', addNext, Function.update_self]
    refine ⟨bitA (decide ((dtop l1 + dtop l2 + c.toNat) % 2 = 1)) :: R, 1 + 1 + 1 + t,
      by omega, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact digA_dg1 _
      · exact hRd a ha
    · rw [dval_cons_bit, hRv, val_step l1 l2 c, toNat_mod2]
    · have e1 := StackProg.Exec.act (addAct X Y C O mk) s
      rw [hact] at e1
      refine StackProg.Exec.loopTrue htest e1 (exec_congrG he ?_)
      refine upd4_congr X Y C O s' s _ _ _ _ _ ?_ ?_
      · intro k k1 k2 k3 k4
        simp only [hs', addNext]
        rw [Function.update_of_ne k4, Function.update_of_ne k3, Function.update_of_ne k2,
          Function.update_of_ne k1]
      · rw [hO', List.reverse_cons, List.append_assoc]; rfl

/-- `X := X + Y` for a digit-only accumulator `X` (then `Y` keeps its non-digit rest). -/
def addProg (X Y C O : K) (mk : A) : StackProg K A :=
  .seq (addLoop X Y C O mk) (transferProg O (fun k => decide (k = X)))

set_option maxHeartbeats 2000000 in
lemma exec_addP (X Y C O : K) (hXY : X ≠ Y) (hXC : X ≠ C) (hXO : X ≠ O) (hYC : Y ≠ C)
    (hYO : Y ≠ O) (hCO : C ≠ O) (mk : A) (r2 : List A) (hr2 : digA r2.head? = false)
    (n : ℕ) (l1 l2 : List A) (s : K → List A)
    (hl1 : ∀ a ∈ l1, digA (some a) = true) (hl2 : ∀ a ∈ l2, digA (some a) = true)
    (hX : s X = l1) (hY : s Y = l2 ++ r2) (hC : s C = []) (hO : s O = [])
    (hn : max l1.length l2.length + 1 ≤ n) :
    ∃ R t, t ≤ 6 * n + 3 ∧ R.length ≤ n ∧ (∀ a ∈ R, digA (some a) = true) ∧
      dval R = dval l1 + dval l2 ∧
      (addProg X Y C O mk).Exec s (Function.update (Function.update s X R) Y r2) t := by
  obtain ⟨R, t, ht, hR, hRd, hRv, he⟩ := exec_add X Y C O hXY hXC hXO hYC hYO hCO mk [] r2 rfl hr2
    n l1 l2 false s hl1 hl2 (by simp [hX]) hY (by simp [hC, cst]) (Or.inl hn)
  set s1 := Function.update (Function.update (Function.update (Function.update s X []) Y r2) C [])
    O (R.reverse ++ s O) with hs1
  obtain ⟨t2, ht2, e2⟩ := exec_transfer O (fun k => decide (k = X)) (R.reverse ++ s O) s1
    (by simp [hs1])
  refine ⟨R, t + 1 + t2, ?_, hR, hRd, by simpa using hRv, ?_⟩
  · simp only [List.length_append, List.length_reverse, hO, List.length_nil] at ht2; omega
  · refine exec_congrG (StackProg.Exec.seq he e2) ?_
    funext k
    by_cases k1 : k = O
    · rw [k1]; simp [transferStore, hs1, hO, Ne.symm hXO, Ne.symm hYO, Ne.symm hCO]
    · by_cases k2 : k = X
      · rw [k2]; simp [transferStore, hs1, hO, hXO, hXY, hXC]
      · by_cases k3 : k = C
        · rw [k3]; simp [transferStore, hs1, hC, Ne.symm hXC, Ne.symm hYC, hCO]
        · simp [transferStore, hs1, Function.update_apply, k1, k2, k3]

end Add

end D0bfU

/-! ## E_inv stack program (namespace D0bfC) -/

namespace D0bfC
open D0bfL D0bfT D0bfS D0bfU


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


/-! ### token helpers -/

lemma encInts_toks (c : List ℤ) : (encInts c).map ι1 = toksE ι1 (c.map digU) := by
  induction c with
  | nil => simp [encInts, toksE_nil]
  | cons z c ih =>
    rw [encInts_cons, encInt_eq_digU, List.map_cons, toksE_cons, ← ih]
    simp

lemma toksE_len_drop (e : BSym → A) (ts : List (List BSym)) (k : ℕ) :
    (toksE e (ts.drop k)).length ≤ (toksE e ts).length := by
  have h : toksE e ts = toksE e (ts.take k) ++ toksE e (ts.drop k) := by
    unfold toksE; rw [← List.flatten_append, ← List.map_append, List.take_append_drop]
  rw [h, List.length_append]; omega

lemma digU_one : digU 1 = [BSym.one] := by
  simp [digU]

lemma headFlag (cl : List ℤ) (p : ℕ) :
    ((cl.map digU).drop p).head? = some [BSym.one] ↔ cl.getD p 0 = 1 := by
  rw [List.head?_drop, List.getElem?_map, List.getD_eq_getElem?_getD]
  obtain ⟨o, ho⟩ : ∃ o, cl[p]? = o := ⟨_, rfl⟩
  rw [ho]
  cases o with
  | none => simp
  | some z =>
    simp only [Option.map_some, Option.some.injEq, Option.getD_some]
    constructor
    · intro hz; exact digU_inj (hz.trans digU_one.symm)
    · intro hz; rw [hz, digU_one]

lemma dropTok (d : List ℕ) (k : ℕ) (hk : k < d.length) :
    toksE ι2 ((d.map tokN).drop k) = (Nat.bits (d.getD k 0)).map (ι2 ∘ dg) ++
      ι2 .sep :: toksE ι2 ((d.map tokN).drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk), toksE_cons]
  simp [tokN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

lemma bits_len_le_toks (d : List ℕ) (k : ℕ) (hk : k < d.length) :
    (Nat.bits (d.getD k 0)).length ≤ (toksE ι2 (d.map tokN)).length := by
  have h1 := toksE_len_drop ι2 (d.map tokN) k
  rw [dropTok d k hk] at h1
  simp only [List.length_append, List.length_map, List.length_cons] at h1; omega

lemma digU_toks_nosep (cl : List ℤ) (p : ℕ) : ∀ t ∈ (cl.map digU).drop p, BSym.sep ∉ t := by
  intro t ht
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop ht)
  exact sep_not_mem_digU z

/-! ### the integer token at the head of `W` -/

/-- what follows the digits of the integer token at position `q`. -/
def Rw (cl : List ℤ) (q : ℕ) : List A :=
  if q < cl.length then ι1 .sep :: toksE ι1 ((cl.map digU).drop (q + 1)) else []

lemma W_split (cl : List ℤ) (q : ℕ) :
    toksE ι1 ((cl.map digU).drop q) = (digU (cl.getD q 0)).map ι1 ++ Rw cl q := by
  by_cases hq : q < cl.length
  · rw [List.drop_eq_getElem_cons (by simpa using hq), toksE_cons]
    simp [Rw, hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  · have h1 : (cl.map digU).drop q = [] := List.drop_eq_nil_of_le (by simp; omega)
    have h2 : cl.getD q 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h1, h2, toksE_nil]; simp [Rw, hq, digU]

lemma Rw_tail (cl : List ℤ) (q : ℕ) : (Rw cl q).tail = toksE ι1 ((cl.map digU).drop (q + 1)) := by
  unfold Rw; split_ifs with hq
  · rfl
  · rw [List.drop_eq_nil_of_le (by simp; omega), toksE_nil]; rfl

lemma Rw_head (cl : List ℤ) (q : ℕ) :
    (Rw cl q).head? = none ∨ (Rw cl q).head? = some (ι1 .sep) := by
  unfold Rw; split_ifs <;> simp

lemma Rw_dig (cl : List ℤ) (q : ℕ) : digA (Rw cl q).head? = false := by
  rcases Rw_head cl q with h | h <;> rw [h] <;> rfl

lemma digU_map (z : ℤ) : (digU z).map ι1 =
    (if z < 0 then [ι1 .minus] else []) ++ (Nat.bits z.natAbs).map (ι1 ∘ dg) := by
  unfold digU; rw [List.map_append, List.map_map]; split_ifs <;> rfl

lemma head_nonminus (k : ℕ) (cl : List ℤ) (q : ℕ) :
    ((Nat.bits k).map (ι1 ∘ dg) ++ Rw cl q).head? ≠ some (ι1 .minus) := by
  cases h : Nat.bits k with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    rcases Rw_head cl q with h' | h' <;> rw [h']
    · simp
    · intro hb; have := ι1_inj (Option.some.inj hb); cases this
  | cons b l =>
    simp only [List.map_cons, List.cons_append, List.head?_cons]
    intro hb; have := ι1_inj (Option.some.inj hb); cases b <;> cases this

lemma scRes_false (X Y : ℕ) : scRes X Y none = some (stSym false) ↔ Y < X := by
  unfold scRes
  split_ifs with h1 h2 <;> simp [stSym, ι1] <;> omega

lemma dval_nil : dval [] = 0 := rfl


/-! ### value splits of a token stream -/

lemma int_split (cl : List ℤ) (q : ℕ) : ∃ lp rp : List A,
    toksE ι1 ((cl.map digU).drop q) = lp ++ rp ∧ (∀ a ∈ lp, digA (some a) = true) ∧
    digA rp.head? = false ∧ dval lp = (cl.getD q 0).toNat := by
  rw [W_split, digU_map]
  by_cases hz : cl.getD q 0 < 0
  · refine ⟨[], ι1 .minus :: ((Nat.bits (cl.getD q 0).natAbs).map (ι1 ∘ dg) ++ Rw cl q), ?_,
      by simp, rfl, ?_⟩
    · rw [if_pos hz]; simp
    · rw [dval_nil, Int.toNat_of_nonpos hz.le]
  · rw [if_neg hz, List.nil_append]
    refine ⟨(Nat.bits (cl.getD q 0).natAbs).map (ι1 ∘ dg), Rw cl q, rfl, digs1 _, Rw_dig cl q, ?_⟩
    rw [dval_bits1]
    push Not at hz
    have h1 := Int.toNat_of_nonneg hz
    have h2 := Int.natAbs_of_nonneg hz
    omega

lemma nat_split (d : List ℕ) (q : ℕ) : ∃ lp rp : List A,
    toksE ι2 ((d.map tokN).drop q) = lp ++ rp ∧ (∀ a ∈ lp, digA (some a) = true) ∧
    digA rp.head? = false ∧ dval lp = d.getD q 0 := by
  by_cases hq : q < d.length
  · exact ⟨_, _, dropTok d q hq, digs2 _, digA_sep2, dval_bits2 _⟩
  · have h1 : (d.map tokN).drop q = [] := List.drop_eq_nil_of_le (by simp; omega)
    have h2 : d.getD q 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    exact ⟨[], [], by rw [h1, toksE_nil]; rfl, by simp, rfl, by rw [h2]; rfl⟩

lemma len_left (l r : List A) (L : ℕ) (h : (l ++ r).length ≤ L) : l.length ≤ L := by
  simp only [List.length_append] at h; omega

lemma len_right (l r : List A) (L : ℕ) (h : (l ++ r).length ≤ L) : r.length ≤ L := by
  simp only [List.length_append] at h; omega

/-! ### keys -/

inductive KI
  | ki | ko | sc | st | kc | kd | kC | kD | W0 | DD | N | Pp | Xs | Np | Cn | Mq | Kc | K | Ic | I
  | Jc | Wr | Wd | Wp | Tx | Tp | Cx | X1 | X2 | Y1 | Y2 | E | C1 | C2 | St | P | Q | Ca | O | Inf
  | Fl | Bd
  deriving DecidableEq

instance : Fintype KI := Fintype.ofList
  [KI.ki, KI.ko, KI.sc, KI.st, KI.kc, KI.kd, KI.kC, KI.kD, KI.W0, KI.DD, KI.N, KI.Pp, KI.Xs, KI.Np,
    KI.Cn, KI.Mq, KI.Kc, KI.K, KI.Ic, KI.I, KI.Jc, KI.Wr, KI.Wd, KI.Wp, KI.Tx, KI.Tp, KI.Cx, KI.X1,
    KI.X2, KI.Y1, KI.Y2, KI.E, KI.C1, KI.C2, KI.St, KI.P, KI.Q, KI.Ca, KI.O, KI.Inf, KI.Fl, KI.Bd]
  (by intro x; cases x <;> simp)

abbrev SP := StackProg KI A

lemma exec_congr {p : SP} {s t t' : KI → List A} {n : ℕ} (h : p.Exec s t n) (e : t = t') :
    p.Exec s t' n := e ▸ h

/-! ### the inclusion test: flag `Fl` iff `Tx + Tp < Wd (+ Wp)` -/

def testCore : SP :=
  .seq (copyProg KI.Wd KI.X1 KI.sc) (.seq (copyProg KI.Tx KI.Y1 KI.sc)
  (.seq (copyProg KI.Tp KI.Y2 KI.sc)
  (.seq (sumLoop KI.X1 KI.X2 KI.Y1 KI.Y2 KI.C1 KI.C2 KI.St mkA)
  (.seq (flagP KI.Fl (fun h => decide (h KI.St = some (stSym false))))
  (.seq (clearProg KI.X1) (.seq (clearProg KI.X2) (.seq (clearProg KI.Y1)
  (.seq (clearProg KI.Y2) (clearProg KI.St)))))))))

set_option maxHeartbeats 4000000 in
lemma exec_testCore (s : KI → List A) (ld rd l2 r2 lx rx lt rt : List A) (L : ℕ)
    (hWd : s KI.Wd = ld ++ rd) (hX2 : s KI.X2 = l2 ++ r2) (hTx : s KI.Tx = lx ++ rx)
    (hTp : s KI.Tp = lt ++ rt)
    (dld : ∀ a ∈ ld, digA (some a) = true) (dl2 : ∀ a ∈ l2, digA (some a) = true)
    (dlx : ∀ a ∈ lx, digA (some a) = true) (dlt : ∀ a ∈ lt, digA (some a) = true)
    (drd : digA rd.head? = false) (dr2 : digA r2.head? = false)
    (drx : digA rx.head? = false) (drt : digA rt.head? = false)
    (hX1 : s KI.X1 = []) (hY1 : s KI.Y1 = []) (hY2 : s KI.Y2 = []) (hSt : s KI.St = [])
    (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hsc : s KI.sc = []) (hFl : s KI.Fl = [])
    (hL1 : (ld ++ rd).length ≤ L) (hL2 : (l2 ++ r2).length ≤ L) (hL3 : (lx ++ rx).length ≤ L)
    (hL4 : (lt ++ rt).length ≤ L) :
    ∃ m ≤ 40 * (L + 1), testCore.Exec s (Function.update (Function.update s KI.X2 []) KI.Fl
      (if dval lx + dval lt < dval ld + dval l2 then [mkA] else [])) m := by
  obtain ⟨m1, hm1, e1⟩ := exec_copy KI.Wd KI.X1 KI.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s KI.X1 (s KI.Wd ++ s KI.X1) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_copy KI.Tx KI.Y1 KI.sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 KI.Y1 (s1 KI.Tx ++ s1 KI.Y1) with hs2
  obtain ⟨m3, hm3, e3⟩ := exec_copy KI.Tp KI.Y2 KI.sc (by decide) (by decide) (by decide) s2
    (by simp [hs1, hs2, hsc])
  set s3 := Function.update s2 KI.Y2 (s2 KI.Tp ++ s2 KI.Y2) with hs3
  have a1 := len_left ld rd L hL1
  have a2 := len_left l2 r2 L hL2
  have a3 := len_left lx rx L hL3
  have a4 := len_left lt rt L hL4
  obtain ⟨P, t4, ht4, hP, e4, hhd⟩ := exec_sum KI.X1 KI.X2 KI.Y1 KI.Y2 KI.C1 KI.C2 KI.St
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    mkA rd r2 rx rt drd dr2 drx drt (L + 1) ld l2 lx lt false false s3 dld dl2 dlx dlt
    (by simp [hs1, hs2, hs3, hWd, hX1]) (by first | exact hX2 | simp [hs1, hs2, hs3, hX2])
    (by simp [hs1, hs2, hs3, hTx, hY1]) (by simp [hs1, hs2, hs3, hTp, hY2])
    (by simp [hs1, hs2, hs3, hC1, cst]) (by simp [hs1, hs2, hs3, hC2, cst])
    (Or.inl (Nat.add_le_add_right (max_le (max_le a1 a2) (max_le a3 a4)) 1))
  have hs3St : s3 KI.St = [] := by simp [hs1, hs2, hs3, hSt]
  rw [hs3St, List.append_nil, List.head?_nil] at hhd
  simp only [Bool.toNat_false, add_zero] at hhd
  set s4 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s3 KI.X1 rd) KI.X2 r2) KI.Y1 rx) KI.Y2 rt) KI.C1 [])
    KI.C2 []) KI.St (P ++ s3 KI.St) with hs4
  have hs4St : s4 KI.St = P := by simp [hs4, hs3St]
  have hs4Fl : s4 KI.Fl = [] := by simp [hs4, hs3, hs2, hs1, hFl]
  have e5 := exec_congr (exec_flagP KI.Fl (fun h => decide (h KI.St = some (stSym false))) s4)
    (t' := Function.update s4 KI.Fl
      (if dval lx + dval lt < dval ld + dval l2 then [mkA] else [])) (by
      congr 1
      show (if decide ((s4 KI.St).head? = some (stSym false)) = true then mkA :: s4 KI.Fl
        else s4 KI.Fl) = _
      rw [hs4St, hs4Fl, hhd]
      by_cases hc : dval lx + dval lt < dval ld + dval l2
      · rw [if_pos hc, if_pos (decide_eq_true ((scRes_false _ _).2 hc))]
      · rw [if_neg hc, if_neg (fun h => hc ((scRes_false _ _).1 (of_decide_eq_true h)))])
  set s5 := Function.update s4 KI.Fl
    (if dval lx + dval lt < dval ld + dval l2 then [mkA] else []) with hs5
  obtain ⟨m6, hm6, e6⟩ := exec_clearG KI.X1 s5
  obtain ⟨m7, hm7, e7⟩ := exec_clearG KI.X2 (Function.update s5 KI.X1 [])
  obtain ⟨m8, hm8, e8⟩ := exec_clearG KI.Y1 (Function.update (Function.update s5 KI.X1 []) KI.X2 [])
  obtain ⟨m9, hm9, e9⟩ := exec_clearG KI.Y2 (Function.update (Function.update
    (Function.update s5 KI.X1 []) KI.X2 []) KI.Y1 [])
  obtain ⟨m10, hm10, e10⟩ := exec_clearG KI.St (Function.update (Function.update (Function.update
    (Function.update s5 KI.X1 []) KI.X2 []) KI.Y1 []) KI.Y2 [])
  have b1 := len_right ld rd L hL1
  have b2 := len_right l2 r2 L hL2
  have b3 := len_right lx rx L hL3
  have b4 := len_right lt rt L hL4
  have g1 : m1 ≤ 6 * L + 3 := by rw [hWd] at hm1; omega
  have g2 : m2 ≤ 6 * L + 3 := by
    have : (s1 KI.Tx).length = (lx ++ rx).length := by simp [hs1, hTx]
    omega
  have g3 : m3 ≤ 6 * L + 3 := by
    have : (s2 KI.Tp).length = (lt ++ rt).length := by simp [hs1, hs2, hTp]
    omega
  have g6 : m6 ≤ 3 * L + 1 := by
    have : (s5 KI.X1).length = rd.length := by simp [hs5, hs4]
    omega
  have g7 : m7 ≤ 3 * L + 1 := by
    have : ((Function.update s5 KI.X1 []) KI.X2).length = r2.length := by simp [hs5, hs4]
    omega
  have g8 : m8 ≤ 3 * L + 1 := by
    have : ((Function.update (Function.update s5 KI.X1 []) KI.X2 []) KI.Y1).length = rx.length := by
      simp [hs5, hs4]
    omega
  have g9 : m9 ≤ 3 * L + 1 := by
    have : ((Function.update (Function.update (Function.update s5 KI.X1 []) KI.X2 []) KI.Y1 [])
        KI.Y2).length = rt.length := by
      simp [hs5, hs4]
    omega
  have g10 : m10 ≤ 3 * (L + 1) + 1 := by
    have : ((Function.update (Function.update (Function.update (Function.update s5 KI.X1 [])
        KI.X2 []) KI.Y1 []) KI.Y2 []) KI.St).length = P.length := by
      simp [hs5, hs4, hs3St]
    omega
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (exec_congr e10 ?_)))))))))⟩
  · clear * - g1 g2 g3 ht4 g6 g7 g8 g9 g10 hL1 hL2 hL3 hL4 b1 b2 b3 b4
    omega
  · funext k
    cases k <;> first | rfl | simp [hs1, hs2, hs3, hs4, hs5, Function.update_apply, hX1, hY1, hY2, hSt, hC1, hC2]

def testProg (wp : Bool) : SP :=
  .seq (if wp then copyProg KI.Wp KI.X2 KI.sc else skipP) testCore

set_option maxHeartbeats 2000000 in
lemma exec_testProg (s : KI → List A) (wp : Bool) (ld rd lp rp lx rx lt rt : List A) (L : ℕ)
    (hWd : s KI.Wd = ld ++ rd) (hWp : s KI.Wp = lp ++ rp) (hTx : s KI.Tx = lx ++ rx)
    (hTp : s KI.Tp = lt ++ rt)
    (dld : ∀ a ∈ ld, digA (some a) = true) (dlp : ∀ a ∈ lp, digA (some a) = true)
    (dlx : ∀ a ∈ lx, digA (some a) = true) (dlt : ∀ a ∈ lt, digA (some a) = true)
    (drd : digA rd.head? = false) (drp : digA rp.head? = false)
    (drx : digA rx.head? = false) (drt : digA rt.head? = false)
    (hX1 : s KI.X1 = []) (hX2 : s KI.X2 = []) (hY1 : s KI.Y1 = []) (hY2 : s KI.Y2 = [])
    (hSt : s KI.St = []) (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hsc : s KI.sc = [])
    (hFl : s KI.Fl = [])
    (hL1 : (ld ++ rd).length ≤ L) (hL2 : (lp ++ rp).length ≤ L) (hL3 : (lx ++ rx).length ≤ L)
    (hL4 : (lt ++ rt).length ≤ L) :
    ∃ m ≤ 50 * (L + 1), (testProg wp).Exec s (Function.update s KI.Fl
      (if dval lx + dval lt < dval ld + (if wp then dval lp else 0) then [mkA] else [])) m := by
  have hX2s : Function.update s KI.X2 [] = s := Function.update_eq_self_iff.2 hX2.symm
  cases wp
  · have e0 := exec_skipP (K := KI) s
    obtain ⟨m, hm, e⟩ := exec_testCore s ld rd [] [] lx rx lt rt L hWd (by simp [hX2]) hTx hTp
      dld (by simp) dlx dlt drd digA_none drx drt hX1 hY1 hY2 hSt hC1 hC2 hsc hFl hL1 (by simp)
      hL3 hL4
    refine ⟨_, ?_, exec_congr (StackProg.Exec.seq e0 e) ?_⟩
    · omega
    · rw [hX2s]; simp [dval_nil]
  · obtain ⟨m0, hm0, e0⟩ := exec_copy KI.Wp KI.X2 KI.sc (by decide) (by decide) (by decide) s hsc
    set s0 := Function.update s KI.X2 (s KI.Wp ++ s KI.X2) with hs0
    obtain ⟨m, hm, e⟩ := exec_testCore s0 ld rd lp rp lx rx lt rt L (by first | exact hWd | simp [hs0, hWd])
      (by simp [hs0, hWp, hX2]) (by first | exact hTx | simp [hs0, hTx]) (by first | exact hTp | simp [hs0, hTp])
      dld dlp dlx dlt drd drp drx drt (by first | exact hX1 | simp [hs0, hX1]) (by first | exact hY1 | simp [hs0, hY1])
      (by first | exact hY2 | simp [hs0, hY2]) (by first | exact hSt | simp [hs0, hSt]) (by first | exact hC1 | simp [hs0, hC1]) (by first | exact hC2 | simp [hs0, hC2])
      (by simp [hs0, hsc]) (by first | exact hFl | simp [hs0, hFl]) hL1 hL2 hL3 hL4
    have hm0' : m0 ≤ 6 * L + 3 := by rw [hWp] at hm0; omega
    refine ⟨_, ?_, exec_congr (StackProg.Exec.seq e0 e) ?_⟩
    · omega
    · rw [hs0, Function.update_idem, hX2s]; simp

/-! ### one arm: test (unless `Inf`), then add the digits at the head of `Wr` to `Acc` -/

def arm (wp : Bool) (Acc : KI) : SP :=
  .seq (.branch (fun h => (h KI.Inf).isSome) skipP (testProg wp))
    (.seq (.branch (fun h => (h KI.Fl).isNone) (addProg Acc KI.Wr KI.Ca KI.O mkA) skipP)
      (clearProg KI.Fl))

set_option maxHeartbeats 4000000 in
lemma exec_arm (s : KI → List A) (wp : Bool) (Acc : KI) (hAW : Acc ≠ KI.Wr) (hAC : Acc ≠ KI.Ca)
    (hAO : Acc ≠ KI.O) (hAF : Acc ≠ KI.Fl)
    (inf : Bool) (a : ℕ) (ts : List (List BSym)) (la ld rd lp rp lx rx lt rt : List A) (L : ℕ)
    (hWr : s KI.Wr = (Nat.bits a).map (ι1 ∘ dg) ++ ι1 .sep :: toksE ι1 ts)
    (hInf : s KI.Inf = if inf then [mkA] else []) (hAcc : s Acc = la)
    (dla : ∀ x ∈ la, digA (some x) = true)
    (hWd : s KI.Wd = ld ++ rd) (hWp : s KI.Wp = lp ++ rp) (hTx : s KI.Tx = lx ++ rx)
    (hTp : s KI.Tp = lt ++ rt)
    (dld : ∀ a ∈ ld, digA (some a) = true) (dlp : ∀ a ∈ lp, digA (some a) = true)
    (dlx : ∀ a ∈ lx, digA (some a) = true) (dlt : ∀ a ∈ lt, digA (some a) = true)
    (drd : digA rd.head? = false) (drp : digA rp.head? = false)
    (drx : digA rx.head? = false) (drt : digA rt.head? = false)
    (hX1 : s KI.X1 = []) (hX2 : s KI.X2 = []) (hY1 : s KI.Y1 = []) (hY2 : s KI.Y2 = [])
    (hSt : s KI.St = []) (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hsc : s KI.sc = [])
    (hFl : s KI.Fl = []) (hCa : s KI.Ca = []) (hO : s KI.O = [])
    (hL1 : (ld ++ rd).length ≤ L) (hL2 : (lp ++ rp).length ≤ L) (hL3 : (lx ++ rx).length ≤ L)
    (hL4 : (lt ++ rt).length ≤ L) (hLa : (Nat.bits a).length ≤ L) (hla : la.length ≤ 2 * L) :
    ∃ la' m, m ≤ 70 * (L + 1) ∧ (∀ x ∈ la', digA (some x) = true) ∧
      la'.length ≤ max la.length L + 1 ∧
      dval la' = dval la + (if (inf = true ∨
        ¬(dval lx + dval lt < dval ld + (if wp then dval lp else 0))) then a else 0) ∧
      (arm wp Acc).Exec s (Function.update (Function.update s Acc la') KI.Wr
        (if (inf = true ∨ ¬(dval lx + dval lt < dval ld + (if wp then dval lp else 0)))
          then ι1 .sep :: toksE ι1 ts
          else (Nat.bits a).map (ι1 ∘ dg) ++ ι1 .sep :: toksE ι1 ts)) m := by
  set F : List A := if (inf = false ∧ dval lx + dval lt < dval ld + (if wp then dval lp else 0))
    then [mkA] else [] with hF
  -- step 1: the test (or nothing)
  have st1 : ∃ m1 ≤ 50 * (L + 1) + 2,
      (StackProg.branch (fun h => (h KI.Inf).isSome) skipP (testProg wp)).Exec s
        (Function.update s KI.Fl F) m1 := by
    cases inf
    · obtain ⟨m, hm, e⟩ := exec_testProg s wp ld rd lp rp lx rx lt rt L hWd hWp hTx hTp dld dlp
        dlx dlt drd drp drx drt hX1 hX2 hY1 hY2 hSt hC1 hC2 hsc hFl hL1 hL2 hL3 hL4
      refine ⟨1 + m, by omega, exec_congr (StackProg.Exec.branchFalse (by simp [hInf]) e) ?_⟩
      simp [hF]
    · refine ⟨1 + 1, by omega, exec_congr (StackProg.Exec.branchTrue (by simp [hInf])
        (exec_skipP s)) ?_⟩
      have hFs : Function.update s KI.Fl [] = s := Function.update_eq_self_iff.2 hFl.symm
      rw [hF, if_neg (by simp)]; exact hFs.symm
  obtain ⟨m1, hm1, e1⟩ := st1
  set s1 := Function.update s KI.Fl F with hs1
  have hdig : ∀ x ∈ (Nat.bits a).map (ι1 ∘ dg), digA (some x) = true := digs1 a
  by_cases hinc : (inf = true ∨ ¬(dval lx + dval lt < dval ld + (if wp then dval lp else 0)))
  · have hF0 : F = [] := by
      rw [hF, if_neg]; rintro ⟨h1, h2⟩
      rcases hinc with h | h
      · rw [h] at h1; cases h1
      · exact h h2
    obtain ⟨R, t2, ht2, hR, hRd, hRv, e2⟩ := exec_addP Acc KI.Wr KI.Ca KI.O hAW hAC hAO
      (by decide) (by decide) (by decide) mkA (ι1 .sep :: toksE ι1 ts) digA_sep1
      (max la.length (Nat.bits a).length + 1) la ((Nat.bits a).map (ι1 ∘ dg)) s1 dla hdig
      (by simp [hs1, hAF, hAcc]) (by first | exact hWr | simp [hs1, hWr]) (by first | exact hCa | simp [hs1, hCa])
      (by first | exact hO | simp [hs1, hO]) (by simp)
    set s2 := Function.update (Function.update s1 Acc R) KI.Wr (ι1 .sep :: toksE ι1 ts) with hs2
    obtain ⟨m3, hm3, e3⟩ := exec_clearG KI.Fl s2
    refine ⟨R, _, ?_, hRd, ?_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq
      (StackProg.Exec.branchTrue (by first | exact hF0 | simp [hs1, hF0]) e2) (exec_congr e3 ?_))⟩
    · have : (s2 KI.Fl).length = 0 := by simp [hs2, hs1, hF0, hAF, Ne.symm hAF, Function.update_apply]
      have hmx : max la.length (Nat.bits a).length ≤ 2 * L := max_le hla (by omega)
      omega
    · have : (Nat.bits a).length ≤ L := hLa
      have : max la.length (Nat.bits a).length ≤ max la.length L := max_le_max le_rfl hLa
      omega
    · rw [hRv, if_pos hinc, dval_bits1]
    · rw [if_pos hinc, hs2, hs1, hF0]
      funext k
      by_cases k1 : k = KI.Fl
      · rw [k1]; simp [Function.update_apply, hAF, Ne.symm hAF, hFl]
      · simp [Function.update_apply, k1]
  · have hF1 : F = [mkA] := by
      rw [hF, if_pos]; push Not at hinc
      exact ⟨by simpa using hinc.1, hinc.2⟩
    have e2 := exec_skipP (K := KI) s1
    obtain ⟨m3, hm3, e3⟩ := exec_clearG KI.Fl s1
    refine ⟨la, _, ?_, dla, by omega, by rw [if_neg hinc]; simp, StackProg.Exec.seq e1
      (StackProg.Exec.seq (StackProg.Exec.branchFalse (by first | exact hF1 | simp [hs1, hF1]) e2)
        (exec_congr e3 ?_))⟩
    · have : (s1 KI.Fl).length = 1 := by simp [hs1, hF1]
      omega
    · rw [if_neg hinc, hs1]
      funext k
      by_cases k1 : k = KI.Fl
      · rw [k1]; simp [Function.update_apply, hFl, hAF, Ne.symm hAF]
      · by_cases k2 : k = KI.Wr
        · rw [k2]; simp [hWr]
        · by_cases k3 : k = Acc
          · rw [k3]; simp [Function.update_apply, hAcc, hAF, hAW]
          · simp [Function.update_apply, k1, k2, k3]

/-! ### the contribution of one resource entry -/

/-- the summand of the inventory: `z` if the entry is counted (always in mode `inf`). -/
def fz (inf : Bool) (z : ℤ) (dt pt T : ℕ) : ℤ :=
  if (inf = true ∨ (z < 0 ∧ dt ≤ T) ∨ (0 < z ∧ dt + pt ≤ T)) then z else 0

lemma fz_neg (inf : Bool) (z : ℤ) (dt pt T : ℕ) (hz : z < 0) :
    fz inf z dt pt T = if (inf = true ∨ ¬(T < dt + (if false = true then pt else 0))) then z
      else 0 := by
  have e : (inf = true ∨ (z < 0 ∧ dt ≤ T) ∨ (0 < z ∧ dt + pt ≤ T)) ↔
      (inf = true ∨ ¬(T < dt + (if false = true then pt else 0))) := by
    simp only [Bool.false_eq_true, if_false, add_zero, not_lt]
    constructor
    · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (by omega)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hz, h⟩)
  unfold fz
  by_cases h : inf = true ∨ ¬(T < dt + (if false = true then pt else 0))
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

lemma fz_pos (inf : Bool) (z : ℤ) (dt pt T : ℕ) (hz : 0 < z) :
    fz inf z dt pt T = if (inf = true ∨ ¬(T < dt + (if true = true then pt else 0))) then z
      else 0 := by
  have e : (inf = true ∨ (z < 0 ∧ dt ≤ T) ∨ (0 < z ∧ dt + pt ≤ T)) ↔
      (inf = true ∨ ¬(T < dt + (if true = true then pt else 0))) := by
    simp only [if_true, not_lt]
    constructor
    · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
      · exact Or.inl h
      · exact absurd h (by omega)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hz, h⟩)
  unfold fz
  by_cases h : inf = true ∨ ¬(T < dt + (if true = true then pt else 0))
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

lemma fz_zero (inf : Bool) (dt pt T : ℕ) : fz inf 0 dt pt T = 0 := by
  unfold fz; split_ifs <;> rfl

/-! ### skipping `k` tokens when fewer may be present -/

lemma exec_skipToks' (cnt W : KI) (hcW : cnt ≠ W) (e : BSym → A) (he : Function.Injective e)
    (k : ℕ) (ts : List (List BSym)) (s : KI → List A) (hts : ∀ t ∈ ts, BSym.sep ∉ t)
    (hc : s cnt = List.replicate k mkA) (hW : s W = toksE e ts) :
    ∃ m ≤ k * (3 * (toksE e ts).length + 7) + 1, (skipToks cnt W e).Exec s
      (Function.update (Function.update s cnt []) W (toksE e (ts.drop k))) m := by
  have key := exec_for cnt (.seq (popProg cnt) (skipOne W e)) mkA
    (fun t s' => s' = Function.update (Function.update s cnt (List.replicate (k - t) mkA)) W
      (toksE e (ts.drop t))) k (3 * (toksE e ts).length + 5) ?_ s ?_ hc
  · obtain ⟨s', m, hm, he', hs'⟩ := key
    refine ⟨m, by omega, ?_⟩
    rw [hs', Nat.sub_self, List.replicate_zero] at he'; exact he'
  · intro t ht s' hs' _
    subst hs'
    set S := Function.update (Function.update s cnt (List.replicate (k - t) mkA)) W
      (toksE e (ts.drop t)) with hS
    have e1 := exec_pop cnt S
    obtain ⟨m2, hm2, e2⟩ := exec_skipOne' W e he (ts.drop t) (Function.update S cnt (S cnt).tail)
      (fun x hx => hts x (List.mem_of_mem_drop hx)) (by simp [hS, Function.update_apply, hcW.symm])
    have hl := toksE_len_drop e ts t
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 e2, ?_, ?_⟩
    · simp [hS, Function.update_apply, hcW.symm] at hm2; omega
    · funext x
      by_cases h1 : x = W
      · subst h1; simp [hS, List.tail_drop]
      · by_cases h2 : x = cnt
        · subst h2; simp [hS, Function.update_apply, h1, List.tail_replicate, Nat.sub_sub]
        · simp [hS, Function.update_apply, h1, h2]
    · simp [hS, Function.update_apply, hcW, List.tail_replicate, Nat.sub_sub]
  · funext x
    by_cases h1 : x = W
    · subst h1; simp [hW]
    · by_cases h2 : x = cnt
      · subst h2; simp [Function.update_apply, h1, hc]
      · simp [Function.update_apply, h1, h2]

lemma drop_add' (l : List (List BSym)) (a b : ℕ) : (l.drop a).drop b = l.drop (a + b) := by
  simp [List.drop_drop, Nat.add_comm]

lemma getD_ge (cl : List ℤ) (q : ℕ) (h : cl.length ≤ q) : cl.getD q 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

lemma Rw_lt (cl : List ℤ) (q : ℕ) (hq : q < cl.length) :
    Rw cl q = ι1 .sep :: toksE ι1 ((cl.map digU).drop (q + 1)) := by
  unfold Rw; rw [if_pos hq]

lemma toksE_tok (k : ℕ) (ts : List (List BSym)) :
    toksE ι1 (tokN k :: ts) = (Nat.bits k).map (ι1 ∘ dg) ++ ι1 .sep :: toksE ι1 ts := by
  rw [toksE_cons, tokN, List.map_map]

lemma toksE_emp (ts : List (List BSym)) : toksE ι1 ([] :: ts) = ι1 .sep :: toksE ι1 ts := by
  rw [toksE_cons]; rfl

/-! ### one round over `i'`: add the entry `r_{i'k}` (if counted), advance the cursors -/

/-- the branch part of `invBody` -/
def invBr : SP :=
  .branch (fun h => decide (h KI.Wr = some (ι1 .minus)))
      (.seq (popProg KI.Wr) (arm false KI.Q))
      (.branch (fun h => digA (h KI.Wr)) (arm true KI.P) skipP)

set_option maxHeartbeats 8000000 in
lemma exec_invBr (s : KI → List A) (cl : List ℤ) (d : List ℕ) (inf : Bool) (q t m L : ℕ)
    (lP lQ lx rx lt rt : List A)
    (hWr : s KI.Wr = toksE ι1 ((cl.map digU).drop q))
    (hWd : s KI.Wd = toksE ι2 ((d.map tokN).drop t))
    (hWp : s KI.Wp = toksE ι1 ((cl.map digU).drop (2 + t)))
    (hTx : s KI.Tx = lx ++ rx) (hTp : s KI.Tp = lt ++ rt)
    (dlx : ∀ a ∈ lx, digA (some a) = true) (dlt : ∀ a ∈ lt, digA (some a) = true)
    (drx : digA rx.head? = false) (drt : digA rt.head? = false)
    (hInf : s KI.Inf = if inf then [mkA] else [])
    (hP : s KI.P = lP) (hQ : s KI.Q = lQ)
    (dlP : ∀ a ∈ lP, digA (some a) = true) (dlQ : ∀ a ∈ lQ, digA (some a) = true)
    (hm : 1 ≤ m)
    (hX1 : s KI.X1 = []) (hX2 : s KI.X2 = []) (hY1 : s KI.Y1 = []) (hY2 : s KI.Y2 = [])
    (hSt : s KI.St = []) (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hsc : s KI.sc = [])
    (hFl : s KI.Fl = []) (hCa : s KI.Ca = []) (hO : s KI.O = [])
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L)
    (hL3 : (lx ++ rx).length ≤ L) (hL4 : (lt ++ rt).length ≤ L)
    (hlP : lP.length ≤ 2 * L) (hlQ : lQ.length ≤ 2 * L) :
    ∃ (lP' lQ' : List A) (W' : List (List BSym)) (m2 : ℕ), m2 ≤ 80 * (L + 1) ∧ (∀ x ∈ W', BSym.sep ∉ x) ∧
      W'.drop m = (cl.map digU).drop (q + m) ∧ (toksE ι1 W').length ≤ L ∧
      (∀ a ∈ lP', digA (some a) = true) ∧ (∀ a ∈ lQ', digA (some a) = true) ∧
      lP'.length ≤ max lP.length L + 1 ∧ lQ'.length ≤ max lQ.length L + 1 ∧
      (dval lP' : ℤ) - dval lQ' = dval lP - dval lQ +
        fz inf (cl.getD q 0) (d.getD t 0) (cl.getD (2 + t) 0).toNat (dval lx + dval lt) ∧
      invBr.Exec s (Function.update (Function.update (Function.update s KI.Wr (toksE ι1 W'))
        KI.P lP') KI.Q lQ') m2 := by
  obtain ⟨ld, rd, hd1, dld, drd, hdv⟩ := nat_split d t
  obtain ⟨lp, rp, hp1, dlp, drp, hpv⟩ := int_split cl (2 + t)
  have hL1 : (ld ++ rd).length ≤ L := by
    rw [← hd1]; exact le_trans (toksE_len_drop ι2 _ t) hLd
  have hL2 : (lp ++ rp).length ≤ L := by
    rw [← hp1]; exact le_trans (toksE_len_drop ι1 _ (2 + t)) hLc
  have hWq : (toksE ι1 ((cl.map digU).drop q)).length ≤ L := le_trans (toksE_len_drop ι1 _ q) hLc
  have hWs := W_split cl q
  rw [digU_map] at hWs
  obtain ⟨z, hz⟩ : ∃ z, cl.getD q 0 = z := ⟨_, rfl⟩
  rw [hz] at hWs ⊢
  rw [← hdv, ← hpv]
  rcases lt_trichotomy z 0 with hneg | hzero | hpos
  · -- a negative entry
    have hq : q < cl.length := by
      by_contra h; have := getD_ge cl q (by omega); omega
    rw [if_pos hneg, Rw_lt cl q hq, List.singleton_append] at hWs
    have hWr' : s KI.Wr = ι1 .minus :: ((Nat.bits z.natAbs).map (ι1 ∘ dg) ++
        ι1 .sep :: toksE ι1 ((cl.map digU).drop (q + 1))) := by rw [hWr, hWs, List.cons_append]
    have hWl := hWq
    rw [hWs] at hWl
    simp only [List.length_cons, List.length_append, List.length_map] at hWl
    have hbl : (Nat.bits z.natAbs).length ≤ L := by omega
    have e1 := exec_pop KI.Wr s
    set s1 := Function.update s KI.Wr (s KI.Wr).tail with hs1
    obtain ⟨la', m2, hm2, dla', hla', hval, e2⟩ := exec_arm s1 false KI.Q (by decide) (by decide)
      (by decide) (by decide) inf z.natAbs ((cl.map digU).drop (q + 1)) lQ ld rd lp rp lx rx lt rt L
      (by simp [hs1, hWr']) (by first | exact hInf | simp [hs1, hInf]) (by first | exact hQ | simp [hs1, hQ]) dlQ
      (by simp [hs1, hWd, hd1]) (by simp [hs1, hWp, hp1]) (by first | exact hTx | simp [hs1, hTx]) (by first | exact hTp | simp [hs1, hTp])
      dld dlp dlx dlt drd drp drx drt (by first | exact hX1 | simp [hs1, hX1]) (by first | exact hX2 | simp [hs1, hX2])
      (by first | exact hY1 | simp [hs1, hY1]) (by first | exact hY2 | simp [hs1, hY2]) (by first | exact hSt | simp [hs1, hSt]) (by first | exact hC1 | simp [hs1, hC1])
      (by first | exact hC2 | simp [hs1, hC2]) (by simp [hs1, hsc]) (by first | exact hFl | simp [hs1, hFl]) (by first | exact hCa | simp [hs1, hCa])
      (by first | exact hO | simp [hs1, hO]) hL1 hL2 hL3 hL4 hbl hlQ
    have habs : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hneg.le
    have hdrop : ∀ x : List BSym, (x :: (cl.map digU).drop (q + 1)).drop m =
        (cl.map digU).drop (q + m) := by
      intro x
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [List.drop_succ_cons, drop_add']; congr 1; omega
    have hns := digU_toks_nosep cl (q + 1)
    rw [fz_neg inf z _ _ _ hneg]
    by_cases hc : (inf = true ∨ ¬(dval lx + dval lt < dval ld + (if false = true then dval lp else 0)))
    · rw [if_pos hc] at hval e2
      rw [if_pos hc]
      refine ⟨lP, la', [] :: (cl.map digU).drop (q + 1), _, by omega,
        fun x hx => ?_, hdrop _, ?_, dlP, dla', by omega, hla', ?_,
        exec_congr (StackProg.Exec.branchTrue (by simp [hWr']) (StackProg.Exec.seq e1 e2)) ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · simp
        · exact hns x hx
      · rw [toksE_emp]; simp only [List.length_cons]; omega
      · rw [hval, Nat.cast_add]; omega
      · funext k
        by_cases hk1 : k = KI.Wr
        · rw [hk1]; simp [toksE_emp]
        · by_cases hk2 : k = KI.Q
          · rw [hk2]; simp
          · by_cases hk3 : k = KI.P
            · rw [hk3]; simp [hs1, hP]
            · simp [Function.update_apply, hk1, hk2, hk3, hs1]
    · rw [if_neg hc] at hval e2
      rw [if_neg hc]
      refine ⟨lP, la', tokN z.natAbs :: (cl.map digU).drop (q + 1), _, by omega,
        fun x hx => ?_, hdrop _, ?_, dlP, dla', by omega, hla', ?_,
        exec_congr (StackProg.Exec.branchTrue (by simp [hWr']) (StackProg.Exec.seq e1 e2)) ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact tokN_no_sep _
        · exact hns x hx
      · rw [toksE_tok]; simp only [List.length_cons, List.length_append, List.length_map]; omega
      · rw [hval, Nat.cast_add]; omega
      · funext k
        by_cases hk1 : k = KI.Wr
        · rw [hk1]; simp [toksE_tok]
        · by_cases hk2 : k = KI.Q
          · rw [hk2]; simp
          · by_cases hk3 : k = KI.P
            · rw [hk3]; simp [hs1, hP]
            · simp [Function.update_apply, hk1, hk2, hk3, hs1]
  · -- a zero entry
    subst hzero
    rw [if_neg (lt_irrefl 0)] at hWs
    simp only [Int.natAbs_zero, Nat.zero_bits, List.map_nil, List.nil_append] at hWs
    have hWr' : s KI.Wr = Rw cl q := by rw [hWr, hWs]
    have hnm : decide ((s KI.Wr).head? = some (ι1 .minus)) = false := by
      rw [hWr']
      rcases Rw_head cl q with h | h <;> rw [h]
      · simp
      · simp only [decide_eq_false_iff_not]; intro hb
        have := ι1_inj (Option.some.inj hb); cases this
    have hnd : digA (s KI.Wr).head? = false := by rw [hWr']; exact Rw_dig cl q
    have e1 := exec_skipP (K := KI) s
    refine ⟨lP, lQ, (cl.map digU).drop q, _, by omega, digU_toks_nosep cl q, drop_add' _ _ _,
      hWq, dlP, dlQ, by omega, by omega, by rw [fz_zero]; ring,
      exec_congr (StackProg.Exec.branchFalse hnm (StackProg.Exec.branchFalse hnd e1)) ?_⟩
    funext k
    by_cases hk1 : k = KI.Wr
    · rw [hk1]; simp [hWr]
    · by_cases hk2 : k = KI.Q
      · rw [hk2]; simp [hQ]
      · by_cases hk3 : k = KI.P
        · rw [hk3]; simp [hP]
        · simp [Function.update_apply, hk1, hk2, hk3]
  · -- a positive entry
    have hq : q < cl.length := by
      by_contra h; have := getD_ge cl q (by omega); omega
    rw [if_neg (by omega), Rw_lt cl q hq, List.nil_append] at hWs
    have hWr' : s KI.Wr = (Nat.bits z.natAbs).map (ι1 ∘ dg) ++
        ι1 .sep :: toksE ι1 ((cl.map digU).drop (q + 1)) := by rw [hWr, hWs]
    have hWl := hWq
    rw [hWs] at hWl
    simp only [List.length_cons, List.length_append, List.length_map] at hWl
    have hbl : (Nat.bits z.natAbs).length ≤ L := by omega
    obtain ⟨b, l, hbits⟩ : ∃ b l, Nat.bits z.natAbs = b :: l := by
      cases h : Nat.bits z.natAbs with
      | nil => exact absurd (show z.natAbs = 0 by rw [← bval_bits z.natAbs, h]; rfl) (by omega)
      | cons b l => exact ⟨b, l, rfl⟩
    have hnm : decide ((s KI.Wr).head? = some (ι1 .minus)) = false := by
      rw [hWr', hbits]; simp only [decide_eq_false_iff_not, List.map_cons, List.cons_append,
        List.head?_cons]
      intro hb; have := ι1_inj (Option.some.inj hb); cases b <;> cases this
    have hnd : digA (s KI.Wr).head? = true := by
      rw [hWr', hbits]; simp only [List.map_cons, List.cons_append, List.head?_cons]
      exact digA_dg1 b
    obtain ⟨la', m2, hm2, dla', hla', hval, e2⟩ := exec_arm s true KI.P (by decide) (by decide)
      (by decide) (by decide) inf z.natAbs ((cl.map digU).drop (q + 1)) lP ld rd lp rp lx rx lt rt L
      hWr' hInf hP dlP (by rw [hWd, hd1]) (by rw [hWp, hp1]) hTx hTp
      dld dlp dlx dlt drd drp drx drt hX1 hX2 hY1 hY2 hSt hC1 hC2 hsc hFl hCa hO
      hL1 hL2 hL3 hL4 hbl hlP
    have habs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hpos.le
    have hdrop : ∀ x : List BSym, (x :: (cl.map digU).drop (q + 1)).drop m =
        (cl.map digU).drop (q + m) := by
      intro x
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [List.drop_succ_cons, drop_add']; congr 1; omega
    have hns := digU_toks_nosep cl (q + 1)
    rw [fz_pos inf z _ _ _ hpos]
    by_cases hc : (inf = true ∨ ¬(dval lx + dval lt < dval ld + (if true = true then dval lp else 0)))
    · rw [if_pos hc] at hval e2
      rw [if_pos hc]
      refine ⟨la', lQ, [] :: (cl.map digU).drop (q + 1), _, by omega,
        fun x hx => ?_, hdrop _, ?_, dla', dlQ, hla', by omega, ?_,
        exec_congr (StackProg.Exec.branchFalse hnm (StackProg.Exec.branchTrue hnd e2)) ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · simp
        · exact hns x hx
      · rw [toksE_emp]; simp only [List.length_cons]; omega
      · rw [hval, Nat.cast_add]; omega
      · funext k
        by_cases hk1 : k = KI.Wr
        · rw [hk1]; simp [toksE_emp]
        · by_cases hk2 : k = KI.Q
          · rw [hk2]; simp [hQ]
          · by_cases hk3 : k = KI.P
            · rw [hk3]; simp
            · simp [Function.update_apply, hk1, hk2, hk3]
    · rw [if_neg hc] at hval e2
      rw [if_neg hc]
      refine ⟨la', lQ, tokN z.natAbs :: (cl.map digU).drop (q + 1), _, by omega,
        fun x hx => ?_, hdrop _, ?_, dla', dlQ, hla', by omega, ?_,
        exec_congr (StackProg.Exec.branchFalse hnm (StackProg.Exec.branchTrue hnd e2)) ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact tokN_no_sep _
        · exact hns x hx
      · rw [toksE_tok]; simp only [List.length_cons, List.length_append, List.length_map]; omega
      · rw [hval, Nat.cast_add]; omega
      · funext k
        by_cases hk1 : k = KI.Wr
        · rw [hk1]; simp [toksE_tok]
        · by_cases hk2 : k = KI.Q
          · rw [hk2]; simp [hQ]
          · by_cases hk3 : k = KI.P
            · rw [hk3]; simp
            · simp [Function.update_apply, hk1, hk2, hk3]

/-! ### one round over `i'` -/

def invBody : SP :=
  .seq (popProg KI.Jc) (.seq invBr (.seq (copyProg KI.Mq KI.Cx KI.sc)
    (.seq (skipToks KI.Cx KI.Wr ι1) (.seq (skipOne KI.Wd ι2) (skipOne KI.Wp ι1)))))

lemma tokN_nosep_drop (d : List ℕ) (t : ℕ) : ∀ x ∈ (d.map tokN).drop t, BSym.sep ∉ x := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop hx)
  exact tokN_no_sep a

lemma poly_q (L : ℕ) : L * (3 * L + 7) + 99 * L + 100 ≤ 100 * ((L + 1) * (L + 1)) := by
  nlinarith [Nat.zero_le (L * L)]

set_option maxHeartbeats 8000000 in
lemma exec_invBody (s : KI → List A) (cl : List ℤ) (d : List ℕ) (inf : Bool) (q t m L : ℕ)
    (lP lQ lx rx lt rt : List A)
    (hWr : s KI.Wr = toksE ι1 ((cl.map digU).drop q))
    (hWd : s KI.Wd = toksE ι2 ((d.map tokN).drop t))
    (hWp : s KI.Wp = toksE ι1 ((cl.map digU).drop (2 + t)))
    (hTx : s KI.Tx = lx ++ rx) (hTp : s KI.Tp = lt ++ rt)
    (dlx : ∀ a ∈ lx, digA (some a) = true) (dlt : ∀ a ∈ lt, digA (some a) = true)
    (drx : digA rx.head? = false) (drt : digA rt.head? = false)
    (hInf : s KI.Inf = if inf then [mkA] else [])
    (hP : s KI.P = lP) (hQ : s KI.Q = lQ)
    (dlP : ∀ a ∈ lP, digA (some a) = true) (dlQ : ∀ a ∈ lQ, digA (some a) = true)
    (hMq : s KI.Mq = List.replicate m mkA) (hm : 1 ≤ m) (hmL : m ≤ L)
    (hX1 : s KI.X1 = []) (hX2 : s KI.X2 = []) (hY1 : s KI.Y1 = []) (hY2 : s KI.Y2 = [])
    (hSt : s KI.St = []) (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hsc : s KI.sc = [])
    (hFl : s KI.Fl = []) (hCa : s KI.Ca = []) (hO : s KI.O = []) (hCx : s KI.Cx = [])
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L)
    (hL3 : (lx ++ rx).length ≤ L) (hL4 : (lt ++ rt).length ≤ L)
    (hlP : lP.length ≤ 2 * L) (hlQ : lQ.length ≤ 2 * L) :
    ∃ (lP' lQ' : List A) (m' : ℕ), m' ≤ 100 * ((L + 1) * (L + 1)) ∧
      (∀ a ∈ lP', digA (some a) = true) ∧ (∀ a ∈ lQ', digA (some a) = true) ∧
      lP'.length ≤ max lP.length L + 1 ∧ lQ'.length ≤ max lQ.length L + 1 ∧
      (dval lP' : ℤ) - dval lQ' = dval lP - dval lQ +
        fz inf (cl.getD q 0) (d.getD t 0) (cl.getD (2 + t) 0).toNat (dval lx + dval lt) ∧
      invBody.Exec s (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update s KI.Jc (s KI.Jc).tail)
        KI.Wr (toksE ι1 ((cl.map digU).drop (q + m))))
        KI.Wd (toksE ι2 ((d.map tokN).drop (t + 1))))
        KI.Wp (toksE ι1 ((cl.map digU).drop (2 + t + 1)))) KI.P lP') KI.Q lQ') m' := by
  have e1 := exec_pop KI.Jc s
  set s1 := Function.update s KI.Jc (s KI.Jc).tail with hs1
  obtain ⟨lP', lQ', W', m2, hm2, hW'1, hW'2, hW'3, dP', dQ', hlP', hlQ', hval, e2⟩ :=
    exec_invBr s1 cl d inf q t m L lP lQ lx rx lt rt (by first | exact hWr | simp [hs1, hWr]) (by first | exact hWd | simp [hs1, hWd])
      (by first | exact hWp | simp [hs1, hWp]) (by first | exact hTx | simp [hs1, hTx]) (by first | exact hTp | simp [hs1, hTp]) dlx dlt drx drt
      (by first | exact hInf | simp [hs1, hInf]) (by first | exact hP | simp [hs1, hP]) (by first | exact hQ | simp [hs1, hQ]) dlP dlQ hm
      (by first | exact hX1 | simp [hs1, hX1]) (by first | exact hX2 | simp [hs1, hX2]) (by first | exact hY1 | simp [hs1, hY1]) (by first | exact hY2 | simp [hs1, hY2])
      (by first | exact hSt | simp [hs1, hSt]) (by first | exact hC1 | simp [hs1, hC1]) (by first | exact hC2 | simp [hs1, hC2]) (by simp [hs1, hsc])
      (by first | exact hFl | simp [hs1, hFl]) (by first | exact hCa | simp [hs1, hCa]) (by first | exact hO | simp [hs1, hO]) hLc hLd hL3 hL4 hlP hlQ
  set s2 := Function.update (Function.update (Function.update s1 KI.Wr (toksE ι1 W'))
    KI.P lP') KI.Q lQ' with hs2
  obtain ⟨m3, hm3, e3⟩ := exec_copy KI.Mq KI.Cx KI.sc (by decide) (by decide) (by decide) s2
    (by simp [hs2, hs1, hsc])
  set s3 := Function.update s2 KI.Cx (s2 KI.Mq ++ s2 KI.Cx) with hs3
  obtain ⟨m4, hm4, e4⟩ := exec_skipToks' KI.Cx KI.Wr (by decide) ι1 ι1_inj m W' s3 hW'1
    (by simp [hs3, hs2, hs1, hMq, hCx]) (by simp [hs3, hs2])
  rw [hW'2] at e4
  set s4 := Function.update (Function.update s3 KI.Cx []) KI.Wr
    (toksE ι1 ((cl.map digU).drop (q + m))) with hs4
  obtain ⟨m5, hm5, e5⟩ := exec_skipOne' KI.Wd ι2 ι2_inj ((d.map tokN).drop t) s4
    (tokN_nosep_drop d t) (by first | exact hWd | simp [hs4, hs3, hs2, hs1, hWd])
  rw [List.tail_drop] at e5
  set s5 := Function.update s4 KI.Wd (toksE ι2 ((d.map tokN).drop (t + 1))) with hs5
  obtain ⟨m6, hm6, e6⟩ := exec_skipOne' KI.Wp ι1 ι1_inj ((cl.map digU).drop (2 + t)) s5
    (digU_toks_nosep cl (2 + t)) (by first | exact hWp | simp [hs5, hs4, hs3, hs2, hs1, hWp])
  rw [List.tail_drop] at e6
  have g3 : m3 ≤ 6 * L + 3 := by
    have : (s2 KI.Mq).length = m := by simp [hs2, hs1, hMq]
    omega
  have g4 : m4 ≤ L * (3 * L + 7) + 1 := by
    have : m * (3 * (toksE ι1 W').length + 7) ≤ L * (3 * L + 7) :=
      Nat.mul_le_mul hmL (by omega)
    omega
  have g5 : m5 ≤ 3 * L + 3 := by
    have h1 : (s4 KI.Wd).length ≤ L := by
      simp only [hs4, hs3, hs2, hs1, Function.update_apply]; simp only [reduceCtorEq, if_false]
      rw [hWd]; exact le_trans (toksE_len_drop ι2 _ t) hLd
    omega
  have g6 : m6 ≤ 3 * L + 3 := by
    have h1 : (s5 KI.Wp).length ≤ L := by
      simp only [hs5, hs4, hs3, hs2, hs1, Function.update_apply]; simp only [reduceCtorEq, if_false]
      rw [hWp]; exact le_trans (toksE_len_drop ι1 _ (2 + t)) hLc
    omega
  have hq := poly_q L
  refine ⟨lP', lQ', _, ?_, dP', dQ', hlP', hlQ', hval, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
    (StackProg.Exec.seq e3 (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (exec_congr e6 ?_)))))⟩
  · omega
  · funext k
    cases k <;> first | rfl | simp [hs1, hs2, hs3, hs4, hs5, Function.update_apply, hCx]

/-! ### the loop over `i'` -/

def invLoop : SP := .loop (fun h => (h KI.Jc).isSome) invBody

set_option maxHeartbeats 8000000 in
lemma exec_invLoop (s0 : KI → List A) (cl : List ℤ) (d : List ℕ) (inf : Bool) (q0 Nn m L : ℕ)
    (lx rx lt rt : List A)
    (hWr : s0 KI.Wr = toksE ι1 ((cl.map digU).drop q0))
    (hWd : s0 KI.Wd = toksE ι2 (d.map tokN))
    (hWp : s0 KI.Wp = toksE ι1 ((cl.map digU).drop 2))
    (hTx : s0 KI.Tx = lx ++ rx) (hTp : s0 KI.Tp = lt ++ rt)
    (dlx : ∀ a ∈ lx, digA (some a) = true) (dlt : ∀ a ∈ lt, digA (some a) = true)
    (drx : digA rx.head? = false) (drt : digA rt.head? = false)
    (hInf : s0 KI.Inf = if inf then [mkA] else [])
    (hP : s0 KI.P = []) (hQ : s0 KI.Q = []) (hJc : s0 KI.Jc = List.replicate Nn mkA)
    (hMq : s0 KI.Mq = List.replicate m mkA) (hm : 1 ≤ m) (hmL : m ≤ L) (hNL : Nn ≤ L)
    (hX1 : s0 KI.X1 = []) (hX2 : s0 KI.X2 = []) (hY1 : s0 KI.Y1 = []) (hY2 : s0 KI.Y2 = [])
    (hSt : s0 KI.St = []) (hC1 : s0 KI.C1 = []) (hC2 : s0 KI.C2 = []) (hsc : s0 KI.sc = [])
    (hFl : s0 KI.Fl = []) (hCa : s0 KI.Ca = []) (hO : s0 KI.O = []) (hCx : s0 KI.Cx = [])
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L)
    (hL3 : (lx ++ rx).length ≤ L) (hL4 : (lt ++ rt).length ≤ L) :
    ∃ s' m', m' ≤ Nn * (100 * ((L + 1) * (L + 1)) + 2) + 1 ∧ invLoop.Exec s0 s' m' ∧
      ∃ lP lQ : List A, (∀ a ∈ lP, digA (some a) = true) ∧ (∀ a ∈ lQ, digA (some a) = true) ∧
        lP.length ≤ L + Nn ∧ lQ.length ≤ L + Nn ∧
        (dval lP : ℤ) - dval lQ = ∑ i ∈ Finset.range Nn,
          fz inf (cl.getD (q0 + i * m) 0) (d.getD i 0) (cl.getD (2 + i) 0).toNat
            (dval lx + dval lt) ∧
        s' = Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update s0 KI.Jc [])
          KI.Wr (toksE ι1 ((cl.map digU).drop (q0 + Nn * m))))
          KI.Wd (toksE ι2 ((d.map tokN).drop Nn)))
          KI.Wp (toksE ι1 ((cl.map digU).drop (2 + Nn)))) KI.P lP) KI.Q lQ := by
  have key := exec_for KI.Jc invBody mkA
    (fun t s => ∃ lP lQ : List A, (∀ a ∈ lP, digA (some a) = true) ∧
      (∀ a ∈ lQ, digA (some a) = true) ∧ lP.length ≤ L + t ∧ lQ.length ≤ L + t ∧
      (dval lP : ℤ) - dval lQ = ∑ i ∈ Finset.range t,
          fz inf (cl.getD (q0 + i * m) 0) (d.getD i 0) (cl.getD (2 + i) 0).toNat
            (dval lx + dval lt) ∧
      s = Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update s0 KI.Jc (List.replicate (Nn - t) mkA))
          KI.Wr (toksE ι1 ((cl.map digU).drop (q0 + t * m))))
          KI.Wd (toksE ι2 ((d.map tokN).drop t)))
          KI.Wp (toksE ι1 ((cl.map digU).drop (2 + t)))) KI.P lP) KI.Q lQ)
    Nn (100 * ((L + 1) * (L + 1))) ?_ s0 ⟨[], [], by simp, by simp, by simp, by simp, by simp, ?_⟩ hJc
  · obtain ⟨s', m', hm', he, lP, lQ, d1, d2, l1, l2, hv, hs'⟩ := key
    refine ⟨s', m', hm', he, lP, lQ, d1, d2, l1, l2, hv, ?_⟩
    rw [hs']; simp
  · intro t ht s ⟨lP, lQ, d1, d2, l1, l2, hv, hs⟩ _
    obtain ⟨lP', lQ', m', hm', dP', dQ', hlP', hlQ', hval, e⟩ := exec_invBody s cl d inf
      (q0 + t * m) t m L lP lQ lx rx lt rt
      (by rw [hs]; simp) (by rw [hs]; simp) (by rw [hs]; simp) (by rw [hs]; first | exact hTx | simp [hTx])
      (by rw [hs]; first | exact hTp | simp [hTp]) dlx dlt drx drt (by rw [hs]; first | exact hInf | simp [hInf]) (by rw [hs]; simp)
      (by rw [hs]; simp) d1 d2 (by rw [hs]; first | exact hMq | simp [hMq]) hm hmL
      (by rw [hs]; first | exact hX1 | simp [hX1]) (by rw [hs]; first | exact hX2 | simp [hX2]) (by rw [hs]; first | exact hY1 | simp [hY1])
      (by rw [hs]; first | exact hY2 | simp [hY2]) (by rw [hs]; first | exact hSt | simp [hSt]) (by rw [hs]; first | exact hC1 | simp [hC1])
      (by rw [hs]; first | exact hC2 | simp [hC2]) (by rw [hs]; first | exact hsc | simp [hsc]) (by rw [hs]; first | exact hFl | simp [hFl])
      (by rw [hs]; first | exact hCa | simp [hCa]) (by rw [hs]; first | exact hO | simp [hO]) (by rw [hs]; first | exact hCx | simp [hCx])
      hLc hLd hL3 hL4 (by omega) (by omega)
    refine ⟨_, m', hm', e, ⟨lP', lQ', dP', dQ', ?_, ?_, ?_, ?_⟩, ?_⟩
    · have : max lP.length L ≤ L + t := max_le l1 (by omega)
      omega
    · have : max lQ.length L ≤ L + t := max_le l2 (by omega)
      omega
    · rw [Finset.sum_range_succ, ← hv, hval]
    · have e1 : q0 + t * m + m = q0 + (t + 1) * m := by ring
      have e2 : 2 + t + 1 = 2 + (t + 1) := by ring
      rw [e1, e2, hs]
      funext k
      cases k <;> (try simp only [Function.update_apply, List.tail_replicate, Nat.sub_sub, reduceCtorEq, eq_self_iff_true, ↓reduceIte]) <;> first | rfl | simp [Function.update_apply, List.tail_replicate, Nat.sub_sub]
    · rw [hs]; simp [List.tail_replicate, Nat.sub_sub]
  · funext k; cases k <;> (try simp only [Function.update_apply, hJc, hWr, hWd, hWp, hP, hQ, reduceCtorEq, eq_self_iff_true, ↓reduceIte]) <;> first | rfl | simp [Function.update_apply, hJc, hWr, hWd, hWp, hP, hQ]

/-! ### the bound checks: flag `Bd` unless `Lk ≤ P - Q` (lo) / `P - Q ≤ Uk` (up) -/

def sumBrG (lo : Bool) : SP :=
  .branch (fun h => decide (h KI.Wr = some (ι1 .minus)))
    (.seq (popProg KI.Wr) (if lo then sumLoop KI.X1 KI.E KI.Y1 KI.Wr KI.C1 KI.C2 KI.St mkA
      else sumLoop KI.X1 KI.Wr KI.Y1 KI.E KI.C1 KI.C2 KI.St mkA))
    (if lo then sumLoop KI.X1 KI.Wr KI.Y1 KI.E KI.C1 KI.C2 KI.St mkA
      else sumLoop KI.X1 KI.E KI.Y1 KI.Wr KI.C1 KI.C2 KI.St mkA)

set_option maxHeartbeats 8000000 in
lemma exec_sumBrG (s : KI → List A) (lo : Bool) (cl : List ℤ) (q L : ℕ) (la ra lb rb : List A)
    (hX : s KI.X1 = la ++ ra) (hY : s KI.Y1 = lb ++ rb)
    (dla : ∀ a ∈ la, digA (some a) = true) (dlb : ∀ a ∈ lb, digA (some a) = true)
    (dra : digA ra.head? = false) (drb : digA rb.head? = false)
    (hW : s KI.Wr = toksE ι1 ((cl.map digU).drop q)) (hE : s KI.E = [])
    (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hSt : s KI.St = [])
    (ha : la.length ≤ L) (hb : lb.length ≤ L)
    (hLw : (toksE ι1 ((cl.map digU).drop q)).length ≤ L) :
    ∃ P t, t ≤ 3 * L + 10 ∧ P.length ≤ L + 1 ∧
      (sumBrG lo).Exec s (Function.update (Function.update (Function.update (Function.update s
        KI.Wr (Rw cl q)) KI.X1 ra) KI.Y1 rb) KI.St P) t ∧
      (P.head? = some (stSym false) ↔ ¬(if lo then cl.getD q 0 ≤ (dval lb : ℤ) - dval la
        else (dval la : ℤ) - dval lb ≤ cl.getD q 0)) := by
  obtain ⟨z, hz⟩ : ∃ z, cl.getD q 0 = z := ⟨_, rfl⟩
  have hWs := W_split cl q
  rw [hz, digU_map] at hWs
  have hlz : (Nat.bits z.natAbs).length ≤ L := by
    have h := hLw
    rw [hWs] at h
    simp only [List.length_append, List.length_map] at h
    omega
  have hW'' : s KI.Wr = (if z < 0 then [ι1 .minus] else []) ++
      ((Nat.bits z.natAbs).map (ι1 ∘ dg) ++ Rw cl q) := by
    rw [hW, hWs, List.append_assoc]
  have hdig := Rw_dig cl q
  rw [hz]
  by_cases hneg : z < 0
  · rw [if_pos hneg, List.singleton_append] at hW''
    have habs : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hneg.le
    have e1 := exec_pop KI.Wr s
    set s1 := Function.update s KI.Wr (s KI.Wr).tail with hs1
    have hs1St : s1 KI.St = [] := by simp [hs1, hSt]
    cases lo
    · obtain ⟨P, t, ht, hP, e2, hhd⟩ := exec_sum KI.X1 KI.Wr KI.Y1 KI.E KI.C1 KI.C2 KI.St
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        mkA ra (Rw cl q) rb [] dra hdig drb digA_none
        (L + 1) la ((Nat.bits z.natAbs).map (ι1 ∘ dg)) lb [] false false s1 dla (digs1 _) dlb
        (by simp) (by first | exact hX | simp [hs1, hX]) (by simp [hs1, hW'']) (by first | exact hY | simp [hs1, hY]) (by first | exact hE | simp [hs1, hE])
        (by simp [hs1, hC1, cst]) (by simp [hs1, hC2, cst])
        (Or.inl (Nat.add_le_add_right (max_le (max_le ha (by simpa using hlz))
          (max_le hb (Nat.zero_le _))) 1))
      rw [hs1St, List.append_nil, dval_bits1, dval_nil] at hhd
      simp only [Bool.toNat_false, add_zero, List.head?_nil] at hhd
      refine ⟨P, _, ?_, hP, exec_congr (StackProg.Exec.branchTrue ?_
        (StackProg.Exec.seq e1 e2)) ?_, ?_⟩
      · omega
      · show decide ((s KI.Wr).head? = some (ι1 .minus)) = true
        rw [hW'']; simp
      · funext k
        cases k <;> (try simp only [hs1, Function.update_apply, hE, hC1, hC2, hSt, reduceCtorEq, eq_self_iff_true, ↓reduceIte]) <;> first | rfl | simp [hs1, Function.update_apply, hE, hC1, hC2, hSt]
      · rw [hhd, scRes_false, if_neg Bool.false_ne_true]; omega
    · obtain ⟨P, t, ht, hP, e2, hhd⟩ := exec_sum KI.X1 KI.E KI.Y1 KI.Wr KI.C1 KI.C2 KI.St
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        mkA ra [] rb (Rw cl q) dra digA_none drb hdig
        (L + 1) la [] lb ((Nat.bits z.natAbs).map (ι1 ∘ dg)) false false s1 dla (by simp) dlb
        (digs1 _) (by first | exact hX | simp [hs1, hX]) (by first | exact hE | simp [hs1, hE]) (by first | exact hY | simp [hs1, hY]) (by simp [hs1, hW''])
        (by simp [hs1, hC1, cst]) (by simp [hs1, hC2, cst])
        (Or.inl (Nat.add_le_add_right (max_le (max_le ha (Nat.zero_le _))
          (max_le hb (by simpa using hlz))) 1))
      rw [hs1St, List.append_nil, dval_bits1, dval_nil] at hhd
      simp only [Bool.toNat_false, add_zero, List.head?_nil] at hhd
      refine ⟨P, _, ?_, hP, exec_congr (StackProg.Exec.branchTrue ?_
        (StackProg.Exec.seq e1 e2)) ?_, ?_⟩
      · omega
      · show decide ((s KI.Wr).head? = some (ι1 .minus)) = true
        rw [hW'']; simp
      · funext k
        cases k <;> (try simp only [hs1, Function.update_apply, hE, hC1, hC2, hSt, reduceCtorEq, eq_self_iff_true, ↓reduceIte]) <;> first | rfl | simp [hs1, Function.update_apply, hE, hC1, hC2, hSt]
      · rw [hhd, scRes_false, if_pos rfl]; omega
  · rw [if_neg hneg, List.nil_append] at hW''
    have habs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg (by omega)
    have hnm : decide ((s KI.Wr).head? = some (ι1 .minus)) = false := by
      rw [hW'']; exact decide_eq_false (head_nonminus _ cl q)
    cases lo
    · obtain ⟨P, t, ht, hP, e2, hhd⟩ := exec_sum KI.X1 KI.E KI.Y1 KI.Wr KI.C1 KI.C2 KI.St
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        mkA ra [] rb (Rw cl q) dra digA_none drb hdig
        (L + 1) la [] lb ((Nat.bits z.natAbs).map (ι1 ∘ dg)) false false s dla (by simp) dlb
        (digs1 _) (by simp [hX]) (by simp [hE]) (by simp [hY]) (by simp [hW''])
        (by simp [hC1, cst]) (by simp [hC2, cst])
        (Or.inl (Nat.add_le_add_right (max_le (max_le ha (Nat.zero_le _))
          (max_le hb (by simpa using hlz))) 1))
      rw [hSt, List.append_nil, dval_bits1, dval_nil] at hhd
      simp only [Bool.toNat_false, add_zero, List.head?_nil] at hhd
      refine ⟨P, _, ?_, hP, exec_congr (StackProg.Exec.branchFalse hnm e2) ?_, ?_⟩
      · omega
      · funext k
        cases k <;> (try simp only [Function.update_apply, hE, hC1, hC2, hSt, reduceCtorEq, eq_self_iff_true, ↓reduceIte]) <;> first | rfl | simp [Function.update_apply, hE, hC1, hC2, hSt]
      · rw [hhd, scRes_false, if_neg Bool.false_ne_true]; omega
    · obtain ⟨P, t, ht, hP, e2, hhd⟩ := exec_sum KI.X1 KI.Wr KI.Y1 KI.E KI.C1 KI.C2 KI.St
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        mkA ra (Rw cl q) rb [] dra hdig drb digA_none
        (L + 1) la ((Nat.bits z.natAbs).map (ι1 ∘ dg)) lb [] false false s dla (digs1 _) dlb
        (by simp) (by simp [hX]) (by simp [hW'']) (by simp [hY]) (by simp [hE])
        (by simp [hC1, cst]) (by simp [hC2, cst])
        (Or.inl (Nat.add_le_add_right (max_le (max_le ha (by simpa using hlz))
          (max_le hb (Nat.zero_le _))) 1))
      rw [hSt, List.append_nil, dval_bits1, dval_nil] at hhd
      simp only [Bool.toNat_false, add_zero, List.head?_nil] at hhd
      refine ⟨P, _, ?_, hP, exec_congr (StackProg.Exec.branchFalse hnm e2) ?_, ?_⟩
      · omega
      · funext k
        cases k <;> (try simp only [Function.update_apply, hE, hC1, hC2, hSt, reduceCtorEq, eq_self_iff_true, ↓reduceIte]) <;> first | rfl | simp [Function.update_apply, hE, hC1, hC2, hSt]
      · rw [hhd, scRes_false, if_pos rfl]; omega

def chkG (lo : Bool) (Aa Bb : KI) : SP :=
  .seq (copyProg Aa KI.X1 KI.sc) (.seq (copyProg Bb KI.Y1 KI.sc) (.seq (sumBrG lo)
  (.seq (flagP KI.Bd (fun h => decide (h KI.St = some (stSym false))))
  (.seq (clearProg KI.X1) (.seq (clearProg KI.Y1) (clearProg KI.St))))))

set_option maxHeartbeats 8000000 in
lemma exec_chkG (s : KI → List A) (lo : Bool) (Aa Bb : KI)
    (hA1 : Aa ≠ KI.X1) (hA2 : Aa ≠ KI.sc) (hB1 : Bb ≠ KI.Y1) (hB2 : Bb ≠ KI.sc)
    (hB3 : Bb ≠ KI.X1)
    (cl : List ℤ) (q L : ℕ) (la lb : List A) (hA : s Aa = la) (hB : s Bb = lb)
    (dla : ∀ a ∈ la, digA (some a) = true) (dlb : ∀ a ∈ lb, digA (some a) = true)
    (hW : s KI.Wr = toksE ι1 ((cl.map digU).drop q)) (hX1 : s KI.X1 = []) (hY1 : s KI.Y1 = [])
    (hE : s KI.E = []) (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hSt : s KI.St = [])
    (hsc : s KI.sc = [])
    (ha : la.length ≤ L) (hb : lb.length ≤ L)
    (hLw : (toksE ι1 ((cl.map digU).drop q)).length ≤ L) :
    ∃ m ≤ 40 * (L + 1), (chkG lo Aa Bb).Exec s (Function.update (Function.update s KI.Wr (Rw cl q))
      KI.Bd (if (if lo then cl.getD q 0 ≤ (dval lb : ℤ) - dval la
        else (dval la : ℤ) - dval lb ≤ cl.getD q 0) then s KI.Bd else mkA :: s KI.Bd)) m := by
  obtain ⟨m1, hm1, e1⟩ := exec_copy Aa KI.X1 KI.sc hA1 hA2 (by decide) s hsc
  set s1 := Function.update s KI.X1 (s Aa ++ s KI.X1) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_copy Bb KI.Y1 KI.sc hB1 hB2 (by decide) s1 (by simp [hs1, hsc])
  set s2 := Function.update s1 KI.Y1 (s1 Bb ++ s1 KI.Y1) with hs2
  have h2X : s2 KI.X1 = la ++ [] := by simp [hs2, hs1, hA, hX1]
  have h2Y : s2 KI.Y1 = lb ++ [] := by
    rw [hs2, Function.update_self, hs1, Function.update_of_ne hB3, Function.update_of_ne (by decide),
      hB, hY1]
  obtain ⟨P, t3, ht3, hP, e3, hPh⟩ := exec_sumBrG s2 lo cl q L la [] lb [] h2X h2Y dla dlb
    digA_none digA_none (by first | exact hW | simp [hs2, hs1, hW]) (by first | exact hE | simp [hs2, hs1, hE]) (by first | exact hC1 | simp [hs2, hs1, hC1])
    (by first | exact hC2 | simp [hs2, hs1, hC2]) (by first | exact hSt | simp [hs2, hs1, hSt]) ha hb hLw
  set s3 := Function.update (Function.update (Function.update (Function.update s2
    KI.Wr (Rw cl q)) KI.X1 []) KI.Y1 []) KI.St P with hs3
  have hs3St : s3 KI.St = P := by simp [hs3]
  have hs3Bd : s3 KI.Bd = s KI.Bd := by simp [hs3, hs2, hs1]
  have e4 := exec_congr (exec_flagP KI.Bd (fun h => decide (h KI.St = some (stSym false))) s3)
    (t' := Function.update s3 KI.Bd
      (if (if lo then cl.getD q 0 ≤ (dval lb : ℤ) - dval la
        else (dval la : ℤ) - dval lb ≤ cl.getD q 0) then s KI.Bd else mkA :: s KI.Bd)) (by
      congr 1
      show (if decide ((s3 KI.St).head? = some (stSym false)) = true then mkA :: s3 KI.Bd
        else s3 KI.Bd) = _
      rw [hs3St, hs3Bd]
      by_cases hc : (if lo then cl.getD q 0 ≤ (dval lb : ℤ) - dval la
        else (dval la : ℤ) - dval lb ≤ cl.getD q 0)
      · rw [if_pos hc, if_neg (fun h => (hPh.1 (of_decide_eq_true h)) hc)]
      · rw [if_neg hc, if_pos (decide_eq_true (hPh.2 hc))])
  set s4 := Function.update s3 KI.Bd
      (if (if lo then cl.getD q 0 ≤ (dval lb : ℤ) - dval la
        else (dval la : ℤ) - dval lb ≤ cl.getD q 0) then s KI.Bd else mkA :: s KI.Bd) with hs4
  obtain ⟨m5, hm5, e5⟩ := exec_clearG KI.X1 s4
  obtain ⟨m6, hm6, e6⟩ := exec_clearG KI.Y1 (Function.update s4 KI.X1 [])
  obtain ⟨m7, hm7, e7⟩ := exec_clearG KI.St (Function.update (Function.update s4 KI.X1 []) KI.Y1 [])
  have g1 : m1 ≤ 6 * L + 3 := by rw [hA] at hm1; omega
  have g2 : m2 ≤ 6 * L + 3 := by
    have : (s1 Bb).length = lb.length := by rw [hs1, Function.update_of_ne hB3, hB]
    omega
  have g5 : m5 ≤ 1 := by
    have : (s4 KI.X1).length = 0 := by simp [hs4, hs3]
    omega
  have g6 : m6 ≤ 1 := by
    have : ((Function.update s4 KI.X1 []) KI.Y1).length = 0 := by simp [hs4, hs3]
    omega
  have g7 : m7 ≤ 3 * (L + 1) + 1 := by
    have : ((Function.update (Function.update s4 KI.X1 []) KI.Y1 []) KI.St).length = P.length := by
      simp [hs4, hs3]
    omega
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (exec_congr e7 ?_))))))⟩
  · omega
  · funext k
    cases k <;> first | rfl | simp [hs1, hs2, hs3, hs4, Function.update_apply, hX1, hY1, hSt]

/-! ### the rest of a consumed token, as a token stream -/

lemma Rw_toks (cl : List ℤ) (q m : ℕ) (hm : 1 ≤ m) : ∃ W : List (List BSym),
    (∀ x ∈ W, BSym.sep ∉ x) ∧ toksE ι1 W = Rw cl q ∧ W.drop m = (cl.map digU).drop (q + m) ∧
    (toksE ι1 W).length ≤ (toksE ι1 ((cl.map digU).drop q)).length := by
  by_cases hq : q < cl.length
  · refine ⟨[] :: (cl.map digU).drop (q + 1), ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact digU_toks_nosep cl (q + 1) x hx
    · rw [toksE_emp, Rw_lt cl q hq]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [List.drop_succ_cons, drop_add']; congr 1; omega
    · rw [toksE_emp, W_split cl q, Rw_lt cl q hq]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega
  · refine ⟨[], by simp, ?_, ?_, by simp [toksE_nil]⟩
    · unfold Rw; rw [if_neg hq, toksE_nil]
    · rw [List.drop_nil, List.drop_eq_nil_of_le (by simp; omega)]


/-! ### one inventory check: `Lk ≤ Σ fz ≤ Uk` for the `k`-th resource -/

/-- the inventory sum of resource `k` at the time `T` (all entries in mode `inf`). -/
def invS (cl : List ℤ) (d : List ℕ) (inf : Bool) (k Nn m T : ℕ) : ℤ :=
  ∑ i ∈ Finset.range Nn,
    fz inf (cl.getD (k + Xv Nn + i * m) 0) (d.getD i 0) (cl.getD (2 + i) 0).toNat T

lemma xv_le (Nn L : ℕ) (h : Nn ≤ L) : Xv Nn ≤ 2 * L * L + L + 2 := by
  unfold Xv; nlinarith

lemma poly_c1 (L : ℕ) : (2 * L * L + 2 * L + 2) * (3 * L + 7) + L * (100 * ((L + 1) * (L + 1)) + 2) +
      L * (3 * L + 7) + 12 * L * L + 300 * L + 300 ≤ 3000 * ((L + 1) * (L + 1) * (L + 1)) := by
  nlinarith [Nat.zero_le (L * L * L), Nat.zero_le (L * L)]

lemma poly_c2 (L : ℕ) : 2 * (L * (3 * L + 7)) + 4 * L * L + 60 * L + 60 +
    6000 * ((L + 1) * (L + 1) * (L + 1)) ≤ 7000 * ((L + 1) * (L + 1) * (L + 1)) := by
  nlinarith [Nat.zero_le (L * L * L), Nat.zero_le (L * L)]

/-- set up the cursors `Wr` (resource `k`, activity 0), `Wd`, `Wp` and the counter `Jc`. -/
def setupP : SP :=
  .seq (copyProg KI.W0 KI.Wr KI.sc) (.seq (copyProg KI.Xs KI.Cx KI.sc)
  (.seq (copyProg KI.K KI.Cx KI.sc) (.seq (skipToks KI.Cx KI.Wr ι1)
  (.seq (copyProg KI.DD KI.Wd KI.sc) (.seq (copyProg KI.W0 KI.Wp KI.sc)
  (.seq (pushProg KI.Cx mkA) (.seq (pushProg KI.Cx mkA) (.seq (skipToks KI.Cx KI.Wp ι1)
  (copyProg KI.N KI.Jc KI.sc)))))))))

set_option maxHeartbeats 8000000 in
lemma exec_setupP (s : KI → List A) (cl : List ℤ) (d : List ℕ) (k Nn L : ℕ)
    (hW0 : s KI.W0 = toksE ι1 (cl.map digU)) (hDD : s KI.DD = toksE ι2 (d.map tokN))
    (hXs : s KI.Xs = List.replicate (Xv Nn) mkA) (hK : s KI.K = List.replicate k mkA)
    (hN : s KI.N = List.replicate Nn mkA)
    (hWr : s KI.Wr = []) (hWd : s KI.Wd = []) (hWp : s KI.Wp = []) (hCx : s KI.Cx = [])
    (hJc : s KI.Jc = []) (hsc : s KI.sc = [])
    (hNL : Nn ≤ L) (hkL : k ≤ L)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L) :
    ∃ m' ≤ (2 * L * L + 2 * L + 2) * (3 * L + 7) + 12 * L * L + 60 * L + 60,
      setupP.Exec s (Function.update (Function.update (Function.update (Function.update s
        KI.Wr (toksE ι1 ((cl.map digU).drop (k + Xv Nn))))
        KI.Wd (toksE ι2 (d.map tokN))) KI.Wp (toksE ι1 ((cl.map digU).drop 2)))
        KI.Jc (List.replicate Nn mkA)) m' := by
  have hsep0 : ∀ x ∈ cl.map digU, BSym.sep ∉ x := by simpa using digU_toks_nosep cl 0
  obtain ⟨m1, hm1, e1⟩ := exec_copy KI.W0 KI.Wr KI.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s KI.Wr (s KI.W0 ++ s KI.Wr) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_copy KI.Xs KI.Cx KI.sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 KI.Cx (s1 KI.Xs ++ s1 KI.Cx) with hs2
  obtain ⟨m3, hm3, e3⟩ := exec_copy KI.K KI.Cx KI.sc (by decide) (by decide) (by decide) s2
    (by simp [hs1, hs2, hsc])
  set s3 := Function.update s2 KI.Cx (s2 KI.K ++ s2 KI.Cx) with hs3
  obtain ⟨m4, hm4, e4⟩ := exec_skipToks' KI.Cx KI.Wr (by decide) ι1 ι1_inj (k + Xv Nn)
    (cl.map digU) s3 hsep0
    (by simp [hs1, hs2, hs3, hK, hXs, hCx, List.replicate_append_replicate])
    (by simp [hs1, hs2, hs3, hW0, hWr])
  -- normalize
  set t4 := Function.update s KI.Wr (toksE ι1 ((cl.map digU).drop (k + Xv Nn))) with ht4
  have n4 : Function.update (Function.update s3 KI.Cx []) KI.Wr
      (toksE ι1 ((cl.map digU).drop (k + Xv Nn))) = t4 := by
    funext k'
    by_cases h1 : k' = KI.Wr; · subst h1; simp [ht4]
    by_cases h2 : k' = KI.Cx; · subst h2; simp [ht4, hCx]
    simp [hs1, hs2, hs3, ht4, Function.update_apply, h1, h2]
  rw [n4] at e4
  obtain ⟨m5, hm5, e5⟩ := exec_copy KI.DD KI.Wd KI.sc (by decide) (by decide) (by decide) t4
    (by simp [ht4, hsc])
  set s5 := Function.update t4 KI.Wd (t4 KI.DD ++ t4 KI.Wd) with hs5
  obtain ⟨m6, hm6, e6⟩ := exec_copy KI.W0 KI.Wp KI.sc (by decide) (by decide) (by decide) s5
    (by simp [ht4, hs5, hsc])
  set s6 := Function.update s5 KI.Wp (s5 KI.W0 ++ s5 KI.Wp) with hs6
  have e7 := exec_pushG KI.Cx mkA s6
  have e8 := exec_pushG KI.Cx mkA (Function.update s6 KI.Cx (mkA :: s6 KI.Cx))
  set s8 := Function.update (Function.update s6 KI.Cx (mkA :: s6 KI.Cx)) KI.Cx
    (mkA :: (Function.update s6 KI.Cx (mkA :: s6 KI.Cx)) KI.Cx) with hs8
  obtain ⟨m9, hm9, e9⟩ := exec_skipToks' KI.Cx KI.Wp (by decide) ι1 ι1_inj 2 (cl.map digU) s8 hsep0
    (by simp [ht4, hs5, hs6, hs8, hCx, List.replicate_succ])
    (by simp [ht4, hs5, hs6, hs8, hW0, hWp])
  set s9 := Function.update (Function.update s8 KI.Cx []) KI.Wp
    (toksE ι1 ((cl.map digU).drop 2)) with hs9
  obtain ⟨m10, hm10, e10⟩ := exec_copy KI.N KI.Jc KI.sc (by decide) (by decide) (by decide) s9
    (by simp [ht4, hs5, hs6, hs8, hs9, hsc])
  have hXv := xv_le Nn L hNL
  have g1 : m1 ≤ 6 * L + 3 := by rw [hW0] at hm1; omega
  have g2 : m2 ≤ 6 * (2 * L * L + L + 2) + 3 := by
    have : (s1 KI.Xs).length = Xv Nn := by simp [hs1, hXs]
    omega
  have g3 : m3 ≤ 6 * L + 3 := by
    have : (s2 KI.K).length = k := by simp [hs1, hs2, hK]
    omega
  have g4 : m4 ≤ (2 * L * L + 2 * L + 2) * (3 * L + 7) + 1 := by
    have : (k + Xv Nn) * (3 * (toksE ι1 (cl.map digU)).length + 7) ≤
        (2 * L * L + 2 * L + 2) * (3 * L + 7) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have g5 : m5 ≤ 6 * L + 3 := by
    have : (t4 KI.DD).length = (toksE ι2 (d.map tokN)).length := by simp [ht4, hDD]
    omega
  have g6 : m6 ≤ 6 * L + 3 := by
    have : (s5 KI.W0).length = (toksE ι1 (cl.map digU)).length := by simp [ht4, hs5, hW0]
    omega
  have g9 : m9 ≤ 2 * (3 * L + 7) + 1 := by omega
  have g10 : m10 ≤ 6 * L + 3 := by
    have : (s9 KI.N).length = Nn := by simp [ht4, hs5, hs6, hs8, hs9, hN]
    omega
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (exec_congr e10 ?_)))))))))⟩
  · have : 6 * (2 * L * L + L + 2) = 12 * L * L + 6 * L + 12 := by ring
    clear * - g1 g2 g3 g4 g5 g6 g9 g10 this
    omega
  · funext k'
    by_cases h1 : k' = KI.Wr; · subst h1; simp [ht4, hs5, hs6, hs8, hs9]
    by_cases h2 : k' = KI.Cx; · subst h2; simp [ht4, hs5, hs6, hs8, hs9, hCx]
    by_cases h3 : k' = KI.Wd; · subst h3; simp [ht4, hs5, hs6, hs8, hs9, hDD, hWd]
    by_cases h4 : k' = KI.Wp; · subst h4; simp [ht4, hs5, hs6, hs8, hs9]
    by_cases h5 : k' = KI.Jc; · subst h5; simp [ht4, hs5, hs6, hs8, hs9, hN, hJc]
    simp [ht4, hs5, hs6, hs8, hs9, Function.update_apply, h1, h2, h3, h4, h5]

/-- the two bound checks, `Wr` moving from `Lk` to `Uk`. -/
def checkP : SP :=
  .seq (chkG true KI.Q KI.P) (.seq (copyProg KI.Mq KI.Cx KI.sc) (.seq (skipToks KI.Cx KI.Wr ι1)
    (chkG false KI.P KI.Q)))

set_option maxHeartbeats 8000000 in
lemma exec_checkP (r : KI → List A) (cl : List ℤ) (qL m L : ℕ) (lP lQ : List A)
    (hWr : r KI.Wr = toksE ι1 ((cl.map digU).drop qL)) (hP : r KI.P = lP) (hQ : r KI.Q = lQ)
    (dP : ∀ a ∈ lP, digA (some a) = true) (dQ : ∀ a ∈ lQ, digA (some a) = true)
    (hMq : r KI.Mq = List.replicate m mkA) (hm : 1 ≤ m) (hmL : m ≤ L)
    (hX1 : r KI.X1 = []) (hY1 : r KI.Y1 = []) (hE : r KI.E = []) (hC1 : r KI.C1 = [])
    (hC2 : r KI.C2 = []) (hSt : r KI.St = []) (hsc : r KI.sc = []) (hCx : r KI.Cx = [])
    (hlP : lP.length ≤ 2 * L) (hlQ : lQ.length ≤ 2 * L)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) :
    ∃ b m', m' ≤ L * (3 * L + 7) + 200 * L + 100 ∧
      checkP.Exec r (Function.update (Function.update r KI.Wr (Rw cl (qL + m))) KI.Bd b) m' ∧
      (b = [] ↔ (r KI.Bd = [] ∧ (cl.getD qL 0 ≤ (dval lP : ℤ) - dval lQ ∧
        (dval lP : ℤ) - dval lQ ≤ cl.getD (qL + m) 0))) := by
  have hLwL : (toksE ι1 ((cl.map digU).drop qL)).length ≤ 2 * L :=
    le_trans (toksE_len_drop ι1 _ qL) (by omega)
  obtain ⟨m1, hm1, e1⟩ := exec_chkG r true KI.Q KI.P (by decide) (by decide) (by decide)
    (by decide) (by decide) cl qL (2 * L) lQ lP hQ hP dQ dP hWr hX1 hY1 hE hC1 hC2 hSt hsc
    hlQ hlP hLwL
  simp only [eq_self_iff_true, if_true] at e1
  set c1 : Prop := cl.getD qL 0 ≤ (dval lP : ℤ) - dval lQ with hc1
  set B1 : List A := if c1 then r KI.Bd else mkA :: r KI.Bd with hB1
  set r1 := Function.update (Function.update r KI.Wr (Rw cl qL)) KI.Bd B1 with hr1
  obtain ⟨m2, hm2, e2⟩ := exec_copy KI.Mq KI.Cx KI.sc (by decide) (by decide) (by decide) r1
    (by simp [hr1, hsc])
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := Rw_toks cl qL m hm
  obtain ⟨m3, hm3, e3⟩ := exec_skipToks' KI.Cx KI.Wr (by decide) ι1 ι1_inj m W
    (Function.update r1 KI.Cx (r1 KI.Mq ++ r1 KI.Cx)) hW1 (by simp [hr1, hMq, hCx])
    (by simp [hr1, hW2])
  rw [hW3] at e3
  set r3 := Function.update (Function.update r KI.Wr (toksE ι1 ((cl.map digU).drop (qL + m))))
    KI.Bd B1 with hr3
  have n3 : Function.update (Function.update (Function.update r1 KI.Cx (r1 KI.Mq ++ r1 KI.Cx))
      KI.Cx []) KI.Wr (toksE ι1 ((cl.map digU).drop (qL + m))) = r3 := by
    funext k'
    by_cases h1 : k' = KI.Wr; · subst h1; simp [hr3]
    by_cases h2 : k' = KI.Cx; · subst h2; simp [hr1, hr3, hCx]
    simp [hr1, hr3, Function.update_apply, h1, h2]
  rw [n3] at e3
  have hLwU : (toksE ι1 ((cl.map digU).drop (qL + m))).length ≤ 2 * L :=
    le_trans (toksE_len_drop ι1 _ (qL + m)) (by omega)
  obtain ⟨m4, hm4, e4⟩ := exec_chkG r3 false KI.P KI.Q (by decide) (by decide) (by decide)
    (by decide) (by decide) cl (qL + m) (2 * L) lP lQ (by simp [hr3, hP]) (by simp [hr3, hQ])
    dP dQ (by simp [hr3]) (by simp [hr3, hX1]) (by simp [hr3, hY1]) (by simp [hr3, hE])
    (by simp [hr3, hC1]) (by simp [hr3, hC2]) (by simp [hr3, hSt]) (by simp [hr3, hsc])
    hlP hlQ hLwU
  simp only [Bool.false_eq_true, if_false] at e4
  set c2 : Prop := (dval lP : ℤ) - dval lQ ≤ cl.getD (qL + m) 0 with hc2
  have g2 : m2 ≤ 6 * L + 3 := by
    have : (r1 KI.Mq).length = m := by simp [hr1, hMq]
    omega
  have g3 : m3 ≤ L * (3 * L + 7) + 1 := by
    have : m * (3 * (toksE ι1 W).length + 7) ≤ L * (3 * L + 7) := by
      have : (toksE ι1 W).length ≤ L := le_trans hW4 (le_trans (toksE_len_drop ι1 _ qL) hLc)
      exact Nat.mul_le_mul hmL (by omega)
    omega
  have hBd3 : r3 KI.Bd = B1 := by simp [hr3]
  refine ⟨if c2 then B1 else mkA :: B1, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
    (StackProg.Exec.seq e3 (exec_congr e4 ?_))), ?_⟩
  · omega
  · rw [hBd3, hr3]
    funext k'
    by_cases h1 : k' = KI.Wr; · subst h1; simp
    by_cases h2 : k' = KI.Bd; · subst h2; simp [hc2]
    simp [Function.update_apply, h1, h2]
  · rw [hB1]
    by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp [h1, h2] <;> tauto

/-- clear the cursors and the accumulators. -/
def cleanP : SP :=
  .seq (clearProg KI.Wr) (.seq (clearProg KI.Wd) (.seq (clearProg KI.Wp)
    (.seq (clearProg KI.P) (clearProg KI.Q))))

lemma exec_cleanP (r : KI → List A) (L : ℕ) (h1 : (r KI.Wr).length ≤ L) (h2 : (r KI.Wd).length ≤ L)
    (h3 : (r KI.Wp).length ≤ L) (h4 : (r KI.P).length ≤ L) (h5 : (r KI.Q).length ≤ L) :
    ∃ m' ≤ 15 * L + 15, cleanP.Exec r (Function.update (Function.update (Function.update
      (Function.update (Function.update r KI.Wr []) KI.Wd []) KI.Wp []) KI.P []) KI.Q []) m' := by
  obtain ⟨m1, hm1, e1⟩ := exec_clearG KI.Wr r
  obtain ⟨m2, hm2, e2⟩ := exec_clearG KI.Wd (Function.update r KI.Wr [])
  obtain ⟨m3, hm3, e3⟩ := exec_clearG KI.Wp (Function.update (Function.update r KI.Wr []) KI.Wd [])
  obtain ⟨m4, hm4, e4⟩ := exec_clearG KI.P (Function.update (Function.update
    (Function.update r KI.Wr []) KI.Wd []) KI.Wp [])
  obtain ⟨m5, hm5, e5⟩ := exec_clearG KI.Q (Function.update (Function.update (Function.update
    (Function.update r KI.Wr []) KI.Wd []) KI.Wp []) KI.P [])
  simp only [Function.update_apply, reduceCtorEq, if_false] at hm2 hm3 hm4 hm5
  exact ⟨_, by omega, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 e5)))⟩

def invRoutine : SP := .seq setupP (.seq invLoop (.seq checkP cleanP))

set_option maxHeartbeats 8000000 in
lemma exec_invRoutine (s : KI → List A) (cl : List ℤ) (d : List ℕ) (inf : Bool) (k Nn m L : ℕ)
    (lx rx lt rt : List A)
    (hW0 : s KI.W0 = toksE ι1 (cl.map digU)) (hDD : s KI.DD = toksE ι2 (d.map tokN))
    (hXs : s KI.Xs = List.replicate (Xv Nn) mkA) (hK : s KI.K = List.replicate k mkA)
    (hN : s KI.N = List.replicate Nn mkA) (hMq : s KI.Mq = List.replicate m mkA)
    (hTx : s KI.Tx = lx ++ rx) (hTp : s KI.Tp = lt ++ rt)
    (dlx : ∀ a ∈ lx, digA (some a) = true) (dlt : ∀ a ∈ lt, digA (some a) = true)
    (drx : digA rx.head? = false) (drt : digA rt.head? = false)
    (hInf : s KI.Inf = if inf then [mkA] else [])
    (hWr : s KI.Wr = []) (hWd : s KI.Wd = []) (hWp : s KI.Wp = []) (hCx : s KI.Cx = [])
    (hJc : s KI.Jc = []) (hP : s KI.P = []) (hQ : s KI.Q = [])
    (hX1 : s KI.X1 = []) (hX2 : s KI.X2 = []) (hY1 : s KI.Y1 = []) (hY2 : s KI.Y2 = [])
    (hE : s KI.E = [])
    (hSt : s KI.St = []) (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hsc : s KI.sc = [])
    (hFl : s KI.Fl = []) (hCa : s KI.Ca = []) (hO : s KI.O = [])
    (hm : 1 ≤ m) (hmL : m ≤ L) (hNL : Nn ≤ L) (hkL : k ≤ L)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L)
    (hL3 : (lx ++ rx).length ≤ L) (hL4 : (lt ++ rt).length ≤ L) :
    ∃ b m', m' ≤ 3000 * ((L + 1) * (L + 1) * (L + 1)) ∧
      invRoutine.Exec s (Function.update s KI.Bd b) m' ∧
      (b = [] ↔ (s KI.Bd = [] ∧
        (cl.getD (k + Xv Nn + Nn * m) 0 ≤ invS cl d inf k Nn m (dval lx + dval lt) ∧
          invS cl d inf k Nn m (dval lx + dval lt) ≤ cl.getD (k + Xv Nn + Nn * m + m) 0))) := by
  obtain ⟨m1, hm1, e1⟩ := exec_setupP s cl d k Nn L hW0 hDD hXs hK hN hWr hWd hWp hCx hJc hsc
    hNL hkL hLc hLd
  set t1 := Function.update (Function.update (Function.update (Function.update s
    KI.Wr (toksE ι1 ((cl.map digU).drop (k + Xv Nn))))
    KI.Wd (toksE ι2 (d.map tokN))) KI.Wp (toksE ι1 ((cl.map digU).drop 2)))
    KI.Jc (List.replicate Nn mkA) with ht1
  obtain ⟨s2, m2, hm2, e2, lP, lQ, dP, dQ, hlP, hlQ, hval, hs2⟩ := exec_invLoop t1 cl d inf
    (k + Xv Nn) Nn m L lx rx lt rt (by simp [ht1]) (by simp [ht1]) (by simp [ht1])
    (by first | exact hTx | simp [ht1, hTx]) (by first | exact hTp | simp [ht1, hTp]) dlx dlt drx drt (by first | exact hInf | simp [ht1, hInf])
    (by first | exact hP | simp [ht1, hP]) (by first | exact hQ | simp [ht1, hQ]) (by simp [ht1]) (by first | exact hMq | simp [ht1, hMq]) hm hmL hNL
    (by first | exact hX1 | simp [ht1, hX1]) (by first | exact hX2 | simp [ht1, hX2]) (by first | exact hY1 | simp [ht1, hY1]) (by first | exact hY2 | simp [ht1, hY2])
    (by first | exact hSt | simp [ht1, hSt]) (by first | exact hC1 | simp [ht1, hC1]) (by first | exact hC2 | simp [ht1, hC2]) (by simp [ht1, hsc])
    (by first | exact hFl | simp [ht1, hFl]) (by first | exact hCa | simp [ht1, hCa]) (by first | exact hO | simp [ht1, hO]) (by first | exact hCx | simp [ht1, hCx])
    hLc hLd hL3 hL4
  set qL := k + Xv Nn + Nn * m with hqL
  set t2 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s KI.Wr (toksE ι1 ((cl.map digU).drop qL)))
    KI.Wd (toksE ι2 ((d.map tokN).drop Nn))) KI.Wp (toksE ι1 ((cl.map digU).drop (2 + Nn))))
    KI.Jc []) KI.P lP) KI.Q lQ with ht2
  have n2 : s2 = t2 := by
    rw [hs2, ht1, ht2]
    funext k'
    by_cases h1 : k' = KI.Wr; · subst h1; simp [hqL]
    by_cases h2 : k' = KI.Wd; · subst h2; simp
    by_cases h3 : k' = KI.Wp; · subst h3; simp
    by_cases h4 : k' = KI.Jc; · subst h4; simp
    simp [Function.update_apply, h1, h2, h3, h4]
  rw [n2] at e2
  obtain ⟨b, m3, hm3, e3, hb⟩ := exec_checkP t2 cl qL m L lP lQ (by simp [ht2]) (by simp [ht2])
    (by simp [ht2]) dP dQ (by first | exact hMq | simp [ht2, hMq]) hm hmL (by first | exact hX1 | simp [ht2, hX1]) (by first | exact hY1 | simp [ht2, hY1])
    (by first | exact hE | simp [ht2, hE]) (by first | exact hC1 | simp [ht2, hC1]) (by first | exact hC2 | simp [ht2, hC2]) (by first | exact hSt | simp [ht2, hSt])
    (by simp [ht2, hsc]) (by first | exact hCx | simp [ht2, hCx]) (by omega) (by omega) hLc
  set t3 := Function.update (Function.update t2 KI.Wr (Rw cl (qL + m))) KI.Bd b with ht3
  have hRw : (Rw cl (qL + m)).length ≤ L := by
    have h3 := toksE_len_drop ι1 (cl.map digU) (qL + m)
    rw [W_split] at h3; simp only [List.length_append] at h3; omega
  obtain ⟨m4, hm4, e4⟩ := exec_cleanP t3 (2 * L)
    (by simp [ht3]; omega)
    (by simp [ht3, ht2]; exact le_trans (toksE_len_drop ι2 _ Nn) (by omega))
    (by simp [ht3, ht2]; exact le_trans (toksE_len_drop ι1 _ (2 + Nn)) (by omega))
    (by simp [ht3, ht2]; omega) (by simp [ht3, ht2]; omega)
  have g2 : m2 ≤ L * (100 * ((L + 1) * (L + 1)) + 2) + 1 := by
    have : Nn * (100 * ((L + 1) * (L + 1)) + 2) ≤ L * (100 * ((L + 1) * (L + 1)) + 2) :=
      Nat.mul_le_mul_right _ hNL
    omega
  have hcube := poly_c1 L
  refine ⟨b, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (exec_congr e4 ?_))), ?_⟩
  · omega
  · rw [ht3, ht2]
    funext k'
    by_cases h1 : k' = KI.Wr; · subst h1; simp [hWr]
    by_cases h2 : k' = KI.Wd; · subst h2; simp [hWd]
    by_cases h3 : k' = KI.Wp; · subst h3; simp [hWp]
    by_cases h4 : k' = KI.Jc; · subst h4; simp [hJc]
    by_cases h5 : k' = KI.P; · subst h5; simp [hP]
    by_cases h6 : k' = KI.Q; · subst h6; simp [hQ]
    by_cases h7 : k' = KI.Bd; · subst h7; simp
    simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7]
  · have hS : invS cl d inf k Nn m (dval lx + dval lt) = (dval lP : ℤ) - dval lQ := by
      rw [hval]; rfl
    have hBd2 : t2 KI.Bd = s KI.Bd := by simp [ht2]
    rw [hS, ← hBd2]
    exact hb
def buildProg : SP :=
  .seq (pushProg KI.Xs mkA) (.seq (pushProg KI.Xs mkA) (.seq (copyProg KI.N KI.Xs KI.sc)
  (.seq (copyProg KI.N KI.Cn KI.sc) (.seq (copyProg KI.N KI.Cn KI.sc)
  (.seq (rcLoop KI.N KI.Xs KI.Cn KI.sc) (.seq (copyProg KI.N KI.Np KI.sc)
  (.seq (pushProg KI.Np mkA) (pushProg KI.Np mkA))))))))

lemma xv_rep (N : ℕ) : List.replicate (Xv N) mkA =
    List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]) := by
  have e : Xv N = (N + N) * N + N + 2 := by unfold Xv; ring
  rw [e, List.replicate_add, List.replicate_add, List.append_assoc]; rfl

lemma rep2 (N : ℕ) : List.replicate (N + 2) mkA = mkA :: mkA :: List.replicate N mkA := rfl

lemma exec_build (s : KI → List A) (N : ℕ) (hN : s KI.N = List.replicate N mkA) (hX : s KI.Xs = [])
    (hCn : s KI.Cn = []) (hNp : s KI.Np = []) (hsc : s KI.sc = []) :
    ∃ n ≤ 12 * N * N + 40 * N + 30, buildProg.Exec s
      (Function.update (Function.update s KI.Xs (List.replicate (Xv N) mkA)) KI.Np
        (List.replicate (N + 2) mkA)) n := by
  have e1 : (pushProg KI.Xs mkA).Exec s (Function.update s KI.Xs [mkA]) 1 :=
    exec_congr (exec_pushG KI.Xs mkA s) (by funext k; cases k <;> first | rfl | simp [Function.update_apply, hX])
  have e2 : (pushProg KI.Xs mkA).Exec (Function.update s KI.Xs [mkA])
      (Function.update s KI.Xs [mkA, mkA]) 1 :=
    exec_congr (exec_pushG KI.Xs mkA _) (by funext k; cases k <;> first | rfl | simp [Function.update_apply])
  obtain ⟨n3, hn3, e3⟩ := exec_copy KI.N KI.Xs KI.sc (by decide) (by decide) (by decide)
    (Function.update s KI.Xs [mkA, mkA]) (by simp [Function.update_apply, hsc])
  have e3' := exec_congr e3 (t' := Function.update s KI.Xs (List.replicate N mkA ++ [mkA, mkA]))
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply, hN])
  have hn3' : n3 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn3
  obtain ⟨n4, hn4, e4⟩ := exec_copy KI.N KI.Cn KI.sc (by decide) (by decide) (by decide)
    (Function.update s KI.Xs (List.replicate N mkA ++ [mkA, mkA]))
    (by simp [Function.update_apply, hsc])
  have e4' := exec_congr e4 (t' := Function.update (Function.update s KI.Xs
      (List.replicate N mkA ++ [mkA, mkA])) KI.Cn (List.replicate N mkA))
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply, hN, hCn])
  have hn4' : n4 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn4
  obtain ⟨n5, hn5, e5⟩ := exec_copy KI.N KI.Cn KI.sc (by decide) (by decide) (by decide)
    (Function.update (Function.update s KI.Xs (List.replicate N mkA ++ [mkA, mkA])) KI.Cn
      (List.replicate N mkA)) (by simp [Function.update_apply, hsc])
  have e5' := exec_congr e5 (t' := Function.update (Function.update s KI.Xs
      (List.replicate N mkA ++ [mkA, mkA])) KI.Cn (List.replicate N mkA ++ List.replicate N mkA))
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply, hN])
  have hn5' : n5 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn5
  obtain ⟨n6, hn6, e6⟩ := exec_rc KI.N KI.Xs KI.Cn KI.sc (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) mkA N (N + N)
    (Function.update (Function.update s KI.Xs (List.replicate N mkA ++ [mkA, mkA])) KI.Cn
      (List.replicate N mkA ++ List.replicate N mkA))
    (by simp [Function.update_apply]) (by simp [Function.update_apply, hN])
    (by simp [Function.update_apply, hsc])
  have e6' := exec_congr e6 (t' := Function.update s KI.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA])))
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply, hCn])
  obtain ⟨n7, hn7, e7⟩ := exec_copy KI.N KI.Np KI.sc (by decide) (by decide) (by decide)
    (Function.update s KI.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA])))
    (by simp [Function.update_apply, hsc])
  have e7' := exec_congr e7 (t' := Function.update (Function.update s KI.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KI.Np
      (List.replicate N mkA))
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply, hN, hNp])
  have hn7' : n7 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn7
  have e8 := exec_congr (exec_pushG KI.Np mkA (Function.update (Function.update s KI.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KI.Np
      (List.replicate N mkA))) (t' := Function.update (Function.update s KI.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KI.Np
      (mkA :: List.replicate N mkA))
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply])
  have e9 := exec_congr (exec_pushG KI.Np mkA (Function.update (Function.update s KI.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KI.Np
      (mkA :: List.replicate N mkA))) (t' := Function.update (Function.update s KI.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KI.Np
      (mkA :: mkA :: List.replicate N mkA))
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply])
  rw [xv_rep N, rep2 N]
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3'
    (StackProg.Exec.seq e4' (StackProg.Exec.seq e5' (StackProg.Exec.seq e6'
    (StackProg.Exec.seq e7' (StackProg.Exec.seq e8 e9)))))))⟩
  have h6 : (N + N) * (6 * N + 8) = 12 * N * N + 16 * N := by ring
  rw [h6] at hn6
  omega

/-! ### the two event times of activity `i` -/

/-- the check of resource `k` at time `T`. -/
def okAt (cl : List ℤ) (d : List ℕ) (inf : Bool) (k Nn m T : ℕ) : Prop :=
  cl.getD (k + Xv Nn + Nn * m) 0 ≤ invS cl d inf k Nn m T ∧
    invS cl d inf k Nn m T ≤ cl.getD (k + Xv Nn + Nn * m + m) 0

def evProg : SP :=
  .seq (copyProg KI.DD KI.Tx KI.sc) (.seq (copyProg KI.I KI.Cx KI.sc)
  (.seq (skipToks KI.Cx KI.Tx ι2) (.seq invRoutine
  (.seq (copyProg KI.W0 KI.Tp KI.sc) (.seq (copyProg KI.I KI.Cx KI.sc) (.seq (pushProg KI.Cx mkA)
  (.seq (pushProg KI.Cx mkA) (.seq (skipToks KI.Cx KI.Tp ι1)
  (.seq invRoutine (.seq (clearProg KI.Tp) (clearProg KI.Tx)))))))))))

set_option maxHeartbeats 16000000 in
lemma exec_evProg (s : KI → List A) (cl : List ℤ) (d : List ℕ) (k i Nn m L : ℕ)
    (hW0 : s KI.W0 = toksE ι1 (cl.map digU)) (hDD : s KI.DD = toksE ι2 (d.map tokN))
    (hXs : s KI.Xs = List.replicate (Xv Nn) mkA) (hK : s KI.K = List.replicate k mkA)
    (hN : s KI.N = List.replicate Nn mkA) (hMq : s KI.Mq = List.replicate m mkA)
    (hI : s KI.I = List.replicate i mkA) (hTx : s KI.Tx = []) (hTp : s KI.Tp = [])
    (hInf : s KI.Inf = [])
    (hWr : s KI.Wr = []) (hWd : s KI.Wd = []) (hWp : s KI.Wp = []) (hCx : s KI.Cx = [])
    (hJc : s KI.Jc = []) (hP : s KI.P = []) (hQ : s KI.Q = [])
    (hX1 : s KI.X1 = []) (hX2 : s KI.X2 = []) (hY1 : s KI.Y1 = []) (hY2 : s KI.Y2 = [])
    (hE : s KI.E = [])
    (hSt : s KI.St = []) (hC1 : s KI.C1 = []) (hC2 : s KI.C2 = []) (hsc : s KI.sc = [])
    (hFl : s KI.Fl = []) (hCa : s KI.Ca = []) (hO : s KI.O = [])
    (hm : 1 ≤ m) (hmL : m ≤ L) (hNL : Nn ≤ L) (hkL : k ≤ L) (hiL : i ≤ L)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L) :
    ∃ b m', m' ≤ 7000 * ((L + 1) * (L + 1) * (L + 1)) ∧
      evProg.Exec s (Function.update s KI.Bd b) m' ∧
      (b = [] ↔ (s KI.Bd = [] ∧ okAt cl d false k Nn m (d.getD i 0) ∧
        okAt cl d false k Nn m (d.getD i 0 + (cl.getD (i + 2) 0).toNat))) := by
  obtain ⟨m1, hm1, e1⟩ := exec_copy KI.DD KI.Tx KI.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s KI.Tx (s KI.DD ++ s KI.Tx) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_copy KI.I KI.Cx KI.sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 KI.Cx (s1 KI.I ++ s1 KI.Cx) with hs2
  obtain ⟨m3, hm3, e3⟩ := exec_skipToks' KI.Cx KI.Tx (by decide) ι2 ι2_inj i (d.map tokN) s2
    (by simpa using tokN_nosep_drop d 0) (by simp [hs1, hs2, hI, hCx])
    (by simp [hs1, hs2, hDD, hTx])
  set t3 := Function.update s KI.Tx (toksE ι2 ((d.map tokN).drop i)) with ht3
  have n3 : Function.update (Function.update s2 KI.Cx []) KI.Tx
      (toksE ι2 ((d.map tokN).drop i)) = t3 := by
    funext k'
    by_cases h1 : k' = KI.Tx; · subst h1; simp [ht3]
    by_cases h2 : k' = KI.Cx; · subst h2; simp [ht3, hCx]
    simp [hs1, hs2, ht3, Function.update_apply, h1, h2]
  rw [n3] at e3
  obtain ⟨ld, rd, hd1, dld, drd, hdv⟩ := nat_split d i
  have hLx : (ld ++ rd).length ≤ L := by rw [← hd1]; exact le_trans (toksE_len_drop ι2 _ i) hLd
  obtain ⟨b1, m4, hm4, e4, hb1⟩ := exec_invRoutine t3 cl d false k Nn m L ld rd [] []
    (by first | exact hW0 | simp [ht3, hW0]) (by first | exact hDD | simp [ht3, hDD]) (by first | exact hXs | simp [ht3, hXs])
    (by first | exact hK | simp [ht3, hK]) (by first | exact hN | simp [ht3, hN]) (by first | exact hMq | simp [ht3, hMq])
    (by simp [ht3, hd1]) (by first | exact hTp | simp [ht3, hTp]) dld (by simp) drd digA_none
    (by first | exact hInf | simp [ht3, hInf]) (by first | exact hWr | simp [ht3, hWr]) (by first | exact hWd | simp [ht3, hWd])
    (by first | exact hWp | simp [ht3, hWp]) (by first | exact hCx | simp [ht3, hCx]) (by first | exact hJc | simp [ht3, hJc])
    (by first | exact hP | simp [ht3, hP]) (by first | exact hQ | simp [ht3, hQ]) (by first | exact hX1 | simp [ht3, hX1])
    (by first | exact hX2 | simp [ht3, hX2]) (by first | exact hY1 | simp [ht3, hY1]) (by first | exact hY2 | simp [ht3, hY2])
    (by first | exact hE | simp [ht3, hE]) (by first | exact hSt | simp [ht3, hSt]) (by first | exact hC1 | simp [ht3, hC1])
    (by first | exact hC2 | simp [ht3, hC2]) (by simp [ht3, hsc]) (by first | exact hFl | simp [ht3, hFl])
    (by first | exact hCa | simp [ht3, hCa]) (by first | exact hO | simp [ht3, hO]) hm hmL hNL hkL hLc hLd hLx
    (by simp)
  set s4 := Function.update t3 KI.Bd b1 with hs4
  obtain ⟨m5, hm5, e5⟩ := exec_copy KI.W0 KI.Tp KI.sc (by decide) (by decide) (by decide) s4
    (by simp [ht3, hs4, hsc])
  set s5 := Function.update s4 KI.Tp (s4 KI.W0 ++ s4 KI.Tp) with hs5
  obtain ⟨m6, hm6, e6⟩ := exec_copy KI.I KI.Cx KI.sc (by decide) (by decide) (by decide) s5
    (by simp [ht3, hs4, hs5, hsc])
  set s6 := Function.update s5 KI.Cx (s5 KI.I ++ s5 KI.Cx) with hs6
  have e7 := exec_pushG KI.Cx mkA s6
  have e8 := exec_pushG KI.Cx mkA (Function.update s6 KI.Cx (mkA :: s6 KI.Cx))
  set s8 := Function.update (Function.update s6 KI.Cx (mkA :: s6 KI.Cx)) KI.Cx
    (mkA :: (Function.update s6 KI.Cx (mkA :: s6 KI.Cx)) KI.Cx) with hs8
  obtain ⟨m9, hm9, e9⟩ := exec_skipToks' KI.Cx KI.Tp (by decide) ι1 ι1_inj (i + 2) (cl.map digU) s8
    (by simpa using digU_toks_nosep cl 0)
    (by simp [ht3, hs4, hs5, hs6, hs8, hI, hCx, List.replicate_succ])
    (by simp [ht3, hs4, hs5, hs6, hs8, hW0, hTp])
  set t9 := Function.update (Function.update t3 KI.Bd b1) KI.Tp
    (toksE ι1 ((cl.map digU).drop (i + 2))) with ht9
  have n9 : Function.update (Function.update s8 KI.Cx []) KI.Tp
      (toksE ι1 ((cl.map digU).drop (i + 2))) = t9 := by
    funext k'
    by_cases h1 : k' = KI.Tp; · subst h1; simp [ht9]
    by_cases h2 : k' = KI.Cx; · subst h2; simp [ht9, ht3, hCx]
    simp [hs4, hs5, hs6, hs8, ht9, Function.update_apply, h1, h2]
  rw [n9] at e9
  obtain ⟨lp, rp, hp1, dlp, drp, hpv⟩ := int_split cl (i + 2)
  have hLp : (lp ++ rp).length ≤ L := by
    rw [← hp1]; exact le_trans (toksE_len_drop ι1 _ (i + 2)) hLc
  obtain ⟨b2, m10, hm10, e10, hb2⟩ := exec_invRoutine t9 cl d false k Nn m L ld rd lp rp
    (by first | exact hW0 | simp [ht9, ht3, hW0]) (by first | exact hDD | simp [ht9, ht3, hDD]) (by first | exact hXs | simp [ht9, ht3, hXs])
    (by first | exact hK | simp [ht9, ht3, hK]) (by first | exact hN | simp [ht9, ht3, hN]) (by first | exact hMq | simp [ht9, ht3, hMq])
    (by simp [ht9, ht3, hd1]) (by simp [ht9, hp1]) dld dlp drd drp
    (by first | exact hInf | simp [ht9, ht3, hInf]) (by first | exact hWr | simp [ht9, ht3, hWr]) (by first | exact hWd | simp [ht9, ht3, hWd])
    (by first | exact hWp | simp [ht9, ht3, hWp]) (by first | exact hCx | simp [ht9, ht3, hCx]) (by first | exact hJc | simp [ht9, ht3, hJc])
    (by first | exact hP | simp [ht9, ht3, hP]) (by first | exact hQ | simp [ht9, ht3, hQ]) (by first | exact hX1 | simp [ht9, ht3, hX1])
    (by first | exact hX2 | simp [ht9, ht3, hX2]) (by first | exact hY1 | simp [ht9, ht3, hY1]) (by first | exact hY2 | simp [ht9, ht3, hY2])
    (by first | exact hE | simp [ht9, ht3, hE]) (by first | exact hSt | simp [ht9, ht3, hSt]) (by first | exact hC1 | simp [ht9, ht3, hC1])
    (by first | exact hC2 | simp [ht9, ht3, hC2]) (by simp [ht9, ht3, hsc]) (by first | exact hFl | simp [ht9, ht3, hFl])
    (by first | exact hCa | simp [ht9, ht3, hCa]) (by first | exact hO | simp [ht9, ht3, hO]) hm hmL hNL hkL hLc hLd hLx hLp
  obtain ⟨m11, hm11, e11⟩ := exec_clearG KI.Tp (Function.update t9 KI.Bd b2)
  obtain ⟨m12, hm12, e12⟩ := exec_clearG KI.Tx (Function.update (Function.update t9 KI.Bd b2)
    KI.Tp [])
  have g1 : m1 ≤ 6 * L + 3 := by rw [hDD] at hm1; omega
  have g2 : m2 ≤ 6 * L + 3 := by
    have : (s1 KI.I).length = i := by simp [hs1, hI]
    omega
  have g3 : m3 ≤ L * (3 * L + 7) + 1 := by
    have : i * (3 * (toksE ι2 (d.map tokN)).length + 7) ≤ L * (3 * L + 7) :=
      Nat.mul_le_mul hiL (by omega)
    omega
  have g5 : m5 ≤ 6 * L + 3 := by
    have : (s4 KI.W0).length = (toksE ι1 (cl.map digU)).length := by simp [ht3, hs4, hW0]
    omega
  have g6 : m6 ≤ 6 * L + 3 := by
    have : (s5 KI.I).length = i := by simp [ht3, hs4, hs5, hI]
    omega
  have g9 : m9 ≤ (L + 2) * (3 * L + 7) + 1 := by
    have : (i + 2) * (3 * (toksE ι1 (cl.map digU)).length + 7) ≤ (L + 2) * (3 * L + 7) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have g11 : m11 ≤ 3 * L + 1 := by
    have : ((Function.update t9 KI.Bd b2) KI.Tp).length =
        (toksE ι1 ((cl.map digU).drop (i + 2))).length := by simp [ht9]
    have := toksE_len_drop ι1 (cl.map digU) (i + 2)
    omega
  have g12 : m12 ≤ 3 * L + 1 := by
    have : ((Function.update (Function.update t9 KI.Bd b2) KI.Tp []) KI.Tx).length =
        (toksE ι2 ((d.map tokN).drop i)).length := by simp [ht9, ht3]
    have := toksE_len_drop ι2 (d.map tokN) i
    omega
  have hcube := poly_c2 L
  have hl2 : (L + 2) * (3 * L + 7) = L * (3 * L + 7) + 6 * L + 14 := by ring
  refine ⟨b2, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10 (StackProg.Exec.seq e11
    (exec_congr e12 ?_))))))))))), ?_⟩
  · clear * - g1 g2 g3 hm4 g5 g6 g9 hm10 g11 g12 hcube hl2
    linarith
  · rw [ht9, ht3]
    funext k'
    by_cases h1 : k' = KI.Tx; · subst h1; simp [hTx]
    by_cases h2 : k' = KI.Tp; · subst h2; simp [hTp]
    by_cases h3 : k' = KI.Bd; · subst h3; simp
    simp [Function.update_apply, h1, h2, h3]
  · have hBd9 : t9 KI.Bd = b1 := by simp [ht9]
    have hBd3 : t3 KI.Bd = s KI.Bd := by simp [ht3]
    rw [hBd9] at hb2
    rw [hBd3] at hb1
    rw [hdv, dval_nil, add_zero] at hb1
    rw [hdv, hpv] at hb2
    unfold okAt
    rw [hb2, hb1]
    exact and_assoc


/-! ### the loop over activities `i` -/

def iBody : SP := .seq (popProg KI.Ic) (.seq evProg (pushProg KI.I mkA))

def iLoop : SP := .loop (fun h => (h KI.Ic).isSome) iBody

set_option maxHeartbeats 8000000 in
lemma exec_iLoop (s0 : KI → List A) (cl : List ℤ) (d : List ℕ) (k Nn m L : ℕ)
    (hW0 : s0 KI.W0 = toksE ι1 (cl.map digU)) (hDD : s0 KI.DD = toksE ι2 (d.map tokN))
    (hXs : s0 KI.Xs = List.replicate (Xv Nn) mkA) (hK : s0 KI.K = List.replicate k mkA)
    (hN : s0 KI.N = List.replicate Nn mkA) (hMq : s0 KI.Mq = List.replicate m mkA)
    (hIc : s0 KI.Ic = List.replicate Nn mkA)
    (hI : s0 KI.I = []) (hTx : s0 KI.Tx = []) (hTp : s0 KI.Tp = []) (hInf : s0 KI.Inf = [])
    (hWr : s0 KI.Wr = []) (hWd : s0 KI.Wd = []) (hWp : s0 KI.Wp = []) (hCx : s0 KI.Cx = [])
    (hJc : s0 KI.Jc = []) (hP : s0 KI.P = []) (hQ : s0 KI.Q = [])
    (hX1 : s0 KI.X1 = []) (hX2 : s0 KI.X2 = []) (hY1 : s0 KI.Y1 = []) (hY2 : s0 KI.Y2 = [])
    (hE : s0 KI.E = [])
    (hSt : s0 KI.St = []) (hC1 : s0 KI.C1 = []) (hC2 : s0 KI.C2 = []) (hsc : s0 KI.sc = [])
    (hFl : s0 KI.Fl = []) (hCa : s0 KI.Ca = []) (hO : s0 KI.O = [])
    (hm : 1 ≤ m) (hmL : m ≤ L) (hNL : Nn ≤ L) (hkL : k ≤ L)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L) :
    ∃ s' m', m' ≤ Nn * (7000 * ((L + 1) * (L + 1) * (L + 1)) + 6) + 1 ∧ iLoop.Exec s0 s' m' ∧
      ∃ b, s' = Function.update (Function.update (Function.update s0 KI.Ic []) KI.I
        (List.replicate Nn mkA)) KI.Bd b ∧
      (b = [] ↔ (s0 KI.Bd = [] ∧ ∀ i < Nn, okAt cl d false k Nn m (d.getD i 0) ∧
        okAt cl d false k Nn m (d.getD i 0 + (cl.getD (i + 2) 0).toNat))) := by
  have key := exec_for KI.Ic iBody mkA
    (fun t s => ∃ b, s = Function.update (Function.update (Function.update s0 KI.Ic
        (List.replicate (Nn - t) mkA)) KI.I (List.replicate t mkA)) KI.Bd b ∧
      (b = [] ↔ (s0 KI.Bd = [] ∧ ∀ i < t, okAt cl d false k Nn m (d.getD i 0) ∧
        okAt cl d false k Nn m (d.getD i 0 + (cl.getD (i + 2) 0).toNat))))
    Nn (7000 * ((L + 1) * (L + 1) * (L + 1)) + 4) ?_ s0 ⟨s0 KI.Bd, ?_, by simp⟩ hIc
  · obtain ⟨s', m', hm', he, b, hs', hb⟩ := key
    refine ⟨s', m', hm', he, b, ?_, hb⟩
    rw [hs']; simp
  · intro t ht s ⟨b, hs, hb⟩ _
    have e1 := exec_pop KI.Ic s
    set s1 := Function.update s KI.Ic (s KI.Ic).tail with hs1
    obtain ⟨b', m2, hm2, e2, hb'⟩ := exec_evProg s1 cl d k t Nn m L
      (by rw [hs1, hs]; first | exact hW0 | simp [hW0]) (by rw [hs1, hs]; first | exact hDD | simp [hDD]) (by rw [hs1, hs]; first | exact hXs | simp [hXs])
      (by rw [hs1, hs]; first | exact hK | simp [hK]) (by rw [hs1, hs]; first | exact hN | simp [hN]) (by rw [hs1, hs]; first | exact hMq | simp [hMq])
      (by rw [hs1, hs]; simp) (by rw [hs1, hs]; first | exact hTx | simp [hTx]) (by rw [hs1, hs]; first | exact hTp | simp [hTp])
      (by rw [hs1, hs]; first | exact hInf | simp [hInf]) (by rw [hs1, hs]; first | exact hWr | simp [hWr]) (by rw [hs1, hs]; first | exact hWd | simp [hWd])
      (by rw [hs1, hs]; first | exact hWp | simp [hWp]) (by rw [hs1, hs]; first | exact hCx | simp [hCx]) (by rw [hs1, hs]; first | exact hJc | simp [hJc])
      (by rw [hs1, hs]; first | exact hP | simp [hP]) (by rw [hs1, hs]; first | exact hQ | simp [hQ]) (by rw [hs1, hs]; first | exact hX1 | simp [hX1])
      (by rw [hs1, hs]; first | exact hX2 | simp [hX2]) (by rw [hs1, hs]; first | exact hY1 | simp [hY1]) (by rw [hs1, hs]; first | exact hY2 | simp [hY2])
      (by rw [hs1, hs]; first | exact hE | simp [hE]) (by rw [hs1, hs]; first | exact hSt | simp [hSt]) (by rw [hs1, hs]; first | exact hC1 | simp [hC1])
      (by rw [hs1, hs]; first | exact hC2 | simp [hC2]) (by rw [hs1, hs]; first | exact hsc | simp [hsc]) (by rw [hs1, hs]; first | exact hFl | simp [hFl])
      (by rw [hs1, hs]; first | exact hCa | simp [hCa]) (by rw [hs1, hs]; first | exact hO | simp [hO]) hm hmL hNL hkL (by omega) hLc hLd
    have e3 := exec_pushG KI.I mkA (Function.update s1 KI.Bd b')
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3), ⟨b', ?_, ?_⟩, ?_⟩
    · omega
    · rw [hs1, hs]
      funext k'
      cases k' <;> first | rfl | simp [Function.update_apply, List.tail_replicate, Nat.sub_sub, List.replicate_succ]
    · have hBd : s1 KI.Bd = b := by rw [hs1, hs]; simp
      rw [hb', hBd, hb]
      constructor
      · rintro ⟨⟨h0, h1⟩, h2⟩
        refine ⟨h0, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · exact h2
      · rintro ⟨h0, h1⟩
        exact ⟨⟨h0, fun i hi => h1 i (by omega)⟩, h1 t (by omega)⟩
    · rw [hs1, hs]; simp [Function.update_apply, List.tail_replicate, Nat.sub_sub]
  · funext k'; cases k' <;> first | rfl | simp [Function.update_apply, hIc, hI]

/-! ### the loop over resources `k` -/

def kBody : SP :=
  .seq (popProg KI.Kc) (.seq (pushProg KI.Inf mkA) (.seq invRoutine (.seq (popProg KI.Inf)
  (.seq (copyProg KI.N KI.Ic KI.sc) (.seq iLoop (.seq (clearProg KI.I) (pushProg KI.K mkA)))))))

def kLoop : SP := .loop (fun h => (h KI.Kc).isSome) kBody

/-- everything checked for resource `k`. -/
def okK (cl : List ℤ) (d : List ℕ) (k Nn m : ℕ) : Prop :=
  okAt cl d true k Nn m 0 ∧ ∀ i < Nn, okAt cl d false k Nn m (d.getD i 0) ∧
    okAt cl d false k Nn m (d.getD i 0 + (cl.getD (i + 2) 0).toNat)

set_option maxHeartbeats 16000000 in
lemma exec_kLoop (s0 : KI → List A) (cl : List ℤ) (d : List ℕ) (Nn m L : ℕ)
    (hW0 : s0 KI.W0 = toksE ι1 (cl.map digU)) (hDD : s0 KI.DD = toksE ι2 (d.map tokN))
    (hXs : s0 KI.Xs = List.replicate (Xv Nn) mkA) (hK : s0 KI.K = [])
    (hN : s0 KI.N = List.replicate Nn mkA) (hMq : s0 KI.Mq = List.replicate m mkA)
    (hKc : s0 KI.Kc = List.replicate m mkA) (hIc : s0 KI.Ic = [])
    (hI : s0 KI.I = []) (hTx : s0 KI.Tx = []) (hTp : s0 KI.Tp = []) (hInf : s0 KI.Inf = [])
    (hWr : s0 KI.Wr = []) (hWd : s0 KI.Wd = []) (hWp : s0 KI.Wp = []) (hCx : s0 KI.Cx = [])
    (hJc : s0 KI.Jc = []) (hP : s0 KI.P = []) (hQ : s0 KI.Q = [])
    (hX1 : s0 KI.X1 = []) (hX2 : s0 KI.X2 = []) (hY1 : s0 KI.Y1 = []) (hY2 : s0 KI.Y2 = [])
    (hE : s0 KI.E = [])
    (hSt : s0 KI.St = []) (hC1 : s0 KI.C1 = []) (hC2 : s0 KI.C2 = []) (hsc : s0 KI.sc = [])
    (hFl : s0 KI.Fl = []) (hCa : s0 KI.Ca = []) (hO : s0 KI.O = [])
    (hmL : m ≤ L) (hNL : Nn ≤ L)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hLd : (toksE ι2 (d.map tokN)).length ≤ L) :
    ∃ s' m', m' ≤ m * (L * (7000 * ((L + 1) * (L + 1) * (L + 1)) + 6) +
        3000 * ((L + 1) * (L + 1) * (L + 1)) + 20 * L + 40) + 1 ∧ kLoop.Exec s0 s' m' ∧
      ∃ b, s' = Function.update (Function.update (Function.update s0 KI.Kc []) KI.K
        (List.replicate m mkA)) KI.Bd b ∧
      (b = [] ↔ (s0 KI.Bd = [] ∧ ∀ k < m, okK cl d k Nn m)) := by
  have key := exec_for KI.Kc kBody mkA
    (fun t s => ∃ b, s = Function.update (Function.update (Function.update s0 KI.Kc
        (List.replicate (m - t) mkA)) KI.K (List.replicate t mkA)) KI.Bd b ∧
      (b = [] ↔ (s0 KI.Bd = [] ∧ ∀ k < t, okK cl d k Nn m)))
    m (L * (7000 * ((L + 1) * (L + 1) * (L + 1)) + 6) +
        3000 * ((L + 1) * (L + 1) * (L + 1)) + 20 * L + 38) ?_ s0 ⟨s0 KI.Bd, ?_, by simp⟩ hKc
  · obtain ⟨s', m', hm', he, b, hs', hb⟩ := key
    refine ⟨s', m', hm', he, b, ?_, hb⟩
    rw [hs']; simp
  · intro t ht s ⟨b, hs, hb⟩ _
    have hsf : ∀ k, k ≠ KI.Kc → k ≠ KI.K → k ≠ KI.Bd → s k = s0 k := by
      intro k h1 h2 h3; rw [hs]; simp [Function.update_apply, h1, h2, h3]
    have hsKc : s KI.Kc = List.replicate (m - t) mkA := by rw [hs]; simp
    have hsK : s KI.K = List.replicate t mkA := by rw [hs]; simp
    have hsBd : s KI.Bd = b := by rw [hs]; simp
    have e1 := exec_pop KI.Kc s
    set s1 := Function.update s KI.Kc (s KI.Kc).tail with hs1
    have e2 := exec_pushG KI.Inf mkA s1
    set s2 := Function.update s1 KI.Inf (mkA :: s1 KI.Inf) with hs2
    obtain ⟨b1, m3, hm3, e3, hb1⟩ := exec_invRoutine s2 cl d true t Nn m L [] [] [] []
      ((hsf KI.W0 (by decide) (by decide) (by decide)).trans hW0)
      ((hsf KI.DD (by decide) (by decide) (by decide)).trans hDD)
      ((hsf KI.Xs (by decide) (by decide) (by decide)).trans hXs)
      (by simp [hs2, hs1, hsK])
      ((hsf KI.N (by decide) (by decide) (by decide)).trans hN)
      ((hsf KI.Mq (by decide) (by decide) (by decide)).trans hMq)
      ((hsf KI.Tx (by decide) (by decide) (by decide)).trans hTx)
      ((hsf KI.Tp (by decide) (by decide) (by decide)).trans hTp) (by simp) (by simp)
      digA_none digA_none (by simp [hs2, hs1, hsf KI.Inf (by decide) (by decide) (by decide), hInf])
      ((hsf KI.Wr (by decide) (by decide) (by decide)).trans hWr)
      ((hsf KI.Wd (by decide) (by decide) (by decide)).trans hWd)
      ((hsf KI.Wp (by decide) (by decide) (by decide)).trans hWp)
      ((hsf KI.Cx (by decide) (by decide) (by decide)).trans hCx)
      ((hsf KI.Jc (by decide) (by decide) (by decide)).trans hJc)
      ((hsf KI.P (by decide) (by decide) (by decide)).trans hP)
      ((hsf KI.Q (by decide) (by decide) (by decide)).trans hQ)
      ((hsf KI.X1 (by decide) (by decide) (by decide)).trans hX1)
      ((hsf KI.X2 (by decide) (by decide) (by decide)).trans hX2)
      ((hsf KI.Y1 (by decide) (by decide) (by decide)).trans hY1)
      ((hsf KI.Y2 (by decide) (by decide) (by decide)).trans hY2)
      ((hsf KI.E (by decide) (by decide) (by decide)).trans hE)
      ((hsf KI.St (by decide) (by decide) (by decide)).trans hSt)
      ((hsf KI.C1 (by decide) (by decide) (by decide)).trans hC1)
      ((hsf KI.C2 (by decide) (by decide) (by decide)).trans hC2)
      ((hsf KI.sc (by decide) (by decide) (by decide)).trans hsc)
      ((hsf KI.Fl (by decide) (by decide) (by decide)).trans hFl)
      ((hsf KI.Ca (by decide) (by decide) (by decide)).trans hCa)
      ((hsf KI.O (by decide) (by decide) (by decide)).trans hO)
      (by omega) hmL hNL (by omega) hLc hLd (by simp) (by simp)
    have e4 := exec_pop KI.Inf (Function.update s2 KI.Bd b1)
    set t4 := Function.update (Function.update s KI.Kc (List.replicate (m - t - 1) mkA)) KI.Bd b1
      with ht4
    have n4 : Function.update (Function.update s2 KI.Bd b1) KI.Inf
        ((Function.update s2 KI.Bd b1) KI.Inf).tail = t4 := by
      funext k'
      by_cases h1 : k' = KI.Inf
      · subst h1; simp [ht4, hs2, hs1, hsf KI.Inf (by decide) (by decide) (by decide), hInf]
      by_cases h2 : k' = KI.Kc
      · subst h2; simp [ht4, hs2, hs1, hsKc, List.tail_replicate, Nat.sub_sub]
      by_cases h3 : k' = KI.Bd; · subst h3; simp [ht4]
      simp [ht4, hs2, hs1, Function.update_apply, h1, h2, h3]
    rw [n4] at e4
    obtain ⟨m5, hm5, e5⟩ := exec_copy KI.N KI.Ic KI.sc (by decide) (by decide) (by decide) t4
      ((hsf KI.sc (by decide) (by decide) (by decide)).trans hsc)
    set t5 := Function.update t4 KI.Ic (t4 KI.N ++ t4 KI.Ic) with ht5
    obtain ⟨s6, m6, hm6, e6, b2, hs6, hb2⟩ := exec_iLoop t5 cl d t Nn m L
      ((hsf KI.W0 (by decide) (by decide) (by decide)).trans hW0)
      ((hsf KI.DD (by decide) (by decide) (by decide)).trans hDD)
      ((hsf KI.Xs (by decide) (by decide) (by decide)).trans hXs)
      (by simp [ht5, ht4, hsK])
      ((hsf KI.N (by decide) (by decide) (by decide)).trans hN)
      ((hsf KI.Mq (by decide) (by decide) (by decide)).trans hMq)
      (by simp [ht5, ht4, hsf KI.N (by decide) (by decide) (by decide), hN,
        hsf KI.Ic (by decide) (by decide) (by decide), hIc])
      ((hsf KI.I (by decide) (by decide) (by decide)).trans hI)
      ((hsf KI.Tx (by decide) (by decide) (by decide)).trans hTx)
      ((hsf KI.Tp (by decide) (by decide) (by decide)).trans hTp)
      ((hsf KI.Inf (by decide) (by decide) (by decide)).trans hInf)
      ((hsf KI.Wr (by decide) (by decide) (by decide)).trans hWr)
      ((hsf KI.Wd (by decide) (by decide) (by decide)).trans hWd)
      ((hsf KI.Wp (by decide) (by decide) (by decide)).trans hWp)
      ((hsf KI.Cx (by decide) (by decide) (by decide)).trans hCx)
      ((hsf KI.Jc (by decide) (by decide) (by decide)).trans hJc)
      ((hsf KI.P (by decide) (by decide) (by decide)).trans hP)
      ((hsf KI.Q (by decide) (by decide) (by decide)).trans hQ)
      ((hsf KI.X1 (by decide) (by decide) (by decide)).trans hX1)
      ((hsf KI.X2 (by decide) (by decide) (by decide)).trans hX2)
      ((hsf KI.Y1 (by decide) (by decide) (by decide)).trans hY1)
      ((hsf KI.Y2 (by decide) (by decide) (by decide)).trans hY2)
      ((hsf KI.E (by decide) (by decide) (by decide)).trans hE)
      ((hsf KI.St (by decide) (by decide) (by decide)).trans hSt)
      ((hsf KI.C1 (by decide) (by decide) (by decide)).trans hC1)
      ((hsf KI.C2 (by decide) (by decide) (by decide)).trans hC2)
      ((hsf KI.sc (by decide) (by decide) (by decide)).trans hsc)
      ((hsf KI.Fl (by decide) (by decide) (by decide)).trans hFl)
      ((hsf KI.Ca (by decide) (by decide) (by decide)).trans hCa)
      ((hsf KI.O (by decide) (by decide) (by decide)).trans hO)
      (by omega) hmL hNL (by omega) hLc hLd
    obtain ⟨m7, hm7, e7⟩ := exec_clearG KI.I s6
    have e8 := exec_pushG KI.K mkA (Function.update s6 KI.I [])
    have g5 : m5 ≤ 6 * L + 3 := by
      have : (t4 KI.N).length = Nn := by
        simp [ht4, hsf KI.N (by decide) (by decide) (by decide), hN]
      omega
    have g7 : m7 ≤ 3 * L + 1 := by
      have : (s6 KI.I).length = Nn := by rw [hs6]; simp
      omega
    have g6 : m6 ≤ L * (7000 * ((L + 1) * (L + 1) * (L + 1)) + 6) + 1 :=
      le_trans hm6 (Nat.add_le_add_right (Nat.mul_le_mul_right _ hNL) 1)
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6
      (StackProg.Exec.seq e7 e8)))))), ⟨b2, ?_, ?_⟩, ?_⟩
    · generalize (L + 1) * (L + 1) * (L + 1) = C3 at hm3 g6 ⊢
      generalize L * (7000 * C3 + 6) = X at g6 ⊢
      omega
    · rw [hs6]
      funext k'
      by_cases h1 : k' = KI.Kc
      · subst h1; simp [ht5, ht4, Nat.sub_sub]
      by_cases h2 : k' = KI.K; · subst h2; simp [ht5, ht4, hsK, List.replicate_succ]
      by_cases h3 : k' = KI.Bd; · subst h3; simp
      by_cases h4 : k' = KI.Ic
      · subst h4; simp [hsf KI.Ic (by decide) (by decide) (by decide), hIc]
      by_cases h5 : k' = KI.I
      · subst h5; simp [hsf KI.I (by decide) (by decide) (by decide), hI]
      simp [ht5, ht4, Function.update_apply, h1, h2, h3, h4, h5, hsf k' h1 h2 h3]
    · have hBd5 : t5 KI.Bd = b1 := by simp [ht5, ht4]
      have hBd2 : s2 KI.Bd = b := by simp [hs2, hs1, hsBd]
      rw [hBd5] at hb2
      rw [hBd2, hb] at hb1
      rw [hb2, hb1]
      unfold okK
      simp only [dval_nil, add_zero] at *
      constructor
      · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
        refine ⟨h0, fun k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact h1 k hk
        · exact ⟨h2, h3⟩
      · rintro ⟨h0, h1⟩
        exact ⟨⟨⟨h0, fun k hk => h1 k (by omega)⟩, (h1 t (by omega)).1⟩, (h1 t (by omega)).2⟩
    · rw [hs6]; simp [ht5, ht4, Nat.sub_sub]
  · funext k'; cases k' <;> first | rfl | simp [Function.update_apply, hKc, hK]

/-! ### phase B: decode, compute `N`, `Xv N`, `M`, run the resource loop, clear `ko` on a
violation -/

/-- the number of resources read off the lengths: `⌈(|c| - Xv N) / (N + 2)⌉`. -/
def Mof (cl : List ℤ) (d : List ℕ) : ℕ :=
  (cl.length - Xv (d.length / 2) + (d.length / 2 + 2) - 1) / (d.length / 2 + 2)

/-- everything the machine checks. -/
def MC (cl : List ℤ) (d : List ℕ) : Prop :=
  ∀ k < Mof cl d, okK cl d k (d.length / 2) (Mof cl d)

def phaseB : SP :=
  .seq (transferProg KI.kC (fun k => decide (k = KI.W0)))
  (.seq (transferProg KI.kD (fun k => decide (k = KI.DD)))
  (.seq (halveProg KI.kd KI.N KI.Pp mkA)
  (.seq buildProg
  (.seq (copyProg KI.Xs KI.Cn KI.sc)
  (.seq (syncPopProg KI.kc KI.Cn)
  (.seq (clearProg KI.Cn)
  (.seq (divLoop KI.kc KI.Np KI.X1 KI.Mq KI.X2 KI.sc mkA)
  (.seq (clearProg KI.X2)
  (.seq (copyProg KI.Mq KI.Kc KI.sc)
  (.seq kLoop (.branch (fun h => (h KI.Bd).isNone) skipP (clearProg KI.ko))))))))))))

lemma ceil_le (r D : ℕ) (hD : 1 ≤ D) : (r + D - 1) / D ≤ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [Nat.div_eq_of_lt (by omega)]
  · apply Nat.div_le_of_le_mul
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    have : (D' + 1) * (r' + 1) = D' * r' + D' + r' + 1 := by ring
    omega

lemma poly_c5 (L : ℕ) : L * (L * (7000 * ((L + 1) * (L + 1) * (L + 1)) + 6) +
    3000 * ((L + 1) * (L + 1) * (L + 1)) + 20 * L + 40) + L * (12 * L + 36) + 40 * (L * L) +
    200 * L + 200 ≤ 20000 * ((L + 1) * (L + 1) * (L + 1) * (L + 1) * (L + 1)) := by
  nlinarith [Nat.zero_le (L * L * L * L * L), Nat.zero_le (L * L * L * L), Nat.zero_le (L * L * L),
    Nat.zero_le (L * L)]

lemma encNats_eq_encInts (d : List ℕ) : encNats d = encInts (d.map (fun k : ℕ => (k : ℤ))) := by
  induction d with
  | nil => simp [encNats, encInts]
  | cons k d ih =>
    rw [encNats_cons, List.map_cons, encInts_cons, ih]
    congr 1

lemma map_ι1_inj {l l' : List BSym} (h : l.map ι1 = l'.map ι1) : l = l' :=
  List.map_injective_iff.mpr ι1_inj h

lemma map_ι2_inj {l l' : List BSym} (h : l.map ι2 = l'.map ι2) : l = l' :=
  List.map_injective_iff.mpr ι2_inj h

lemma encNats_inj {d d' : List ℕ} (h : encNats d = encNats d') : d = d' := by
  rw [encNats_eq_encInts, encNats_eq_encInts] at h
  have := encInts_inj _ _ h
  exact List.map_injective_iff.mpr (fun a b hab => by exact_mod_cast hab) this

lemma len_encInts' (c : List ℤ) : c.length ≤ (encInts c).length := by
  induction c with
  | nil => simp [encInts]
  | cons z c ih =>
    rw [encInts_cons, List.length_append, List.length_cons, encInt_eq_digU]
    simp only [List.length_append, List.length_singleton]; omega

set_option maxHeartbeats 16000000 in
lemma exec_phaseB (s : KI → List A) (c : List ℤ) (d : List ℕ) (L : ℕ)
    (hkC : s KI.kC = ((encInts c).map ι1).reverse) (hkD : s KI.kD = ((encNats d).map ι2).reverse)
    (hkd : s KI.kd = List.replicate d.length mkA) (hkc : s KI.kc = List.replicate c.length mkA)
    (he : ∀ k, k ≠ KI.ki → k ≠ KI.ko → k ≠ KI.st → k ≠ KI.kc → k ≠ KI.kd → k ≠ KI.kC →
      k ≠ KI.kD → s k = [])
    (hLc : (encInts c).length ≤ L) (hLd : (encNats d).length ≤ L) (hdl : d.length ≤ L)
    (hcl : c.length ≤ L) (hko : (s KI.ko).length ≤ L) :
    ∃ t m, m ≤ 20000 * ((L + 1) * (L + 1) * (L + 1) * (L + 1) * (L + 1)) + 10 * L + 10 ∧
      phaseB.Exec s t m ∧ (MC c d → t KI.ko = s KI.ko) ∧ (¬MC c d → t KI.ko = []) := by
  set n := d.length / 2 with hn
  have hTC : (encInts c).map ι1 = toksE ι1 (c.map digU) := encInts_toks c
  have hTD : (encNats d).map ι2 = toksE ι2 (d.map tokN) := encNats_toks ι2 d
  have hlc : (toksE ι1 (c.map digU)).length ≤ L := by rw [← hTC]; simpa using hLc
  have hld : (toksE ι2 (d.map tokN)).length ≤ L := by rw [← hTD]; simpa using hLd
  have hW0 := he KI.W0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hDD := he KI.DD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hN := he KI.N (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hPp := he KI.Pp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hXs := he KI.Xs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hNp := he KI.Np (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hCn := he KI.Cn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hMq := he KI.Mq (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hKc := he KI.Kc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hX1 := he KI.X1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hX2 := he KI.X2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsc := he KI.sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hBd := he KI.Bd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- transfers
  obtain ⟨m1, hm1, e1⟩ := exec_transfer KI.kC (fun k => decide (k = KI.W0)) _ s rfl
  set s1 := Function.update (Function.update s KI.kC []) KI.W0 (toksE ι1 (c.map digU)) with hs1
  have e1' := exec_congr e1 (t' := s1)
    (by funext k; cases k <;> first | rfl | simp [hs1, transferStore, Function.update_apply, hkC, hW0, hTC])
  obtain ⟨m2, hm2, e2⟩ := exec_transfer KI.kD (fun k => decide (k = KI.DD)) _ s1 rfl
  set s2 := Function.update (Function.update s1 KI.kD []) KI.DD (toksE ι2 (d.map tokN)) with hs2
  have e2' := exec_congr e2 (t' := s2)
    (by funext k; cases k <;> first | rfl | simp [hs1, hs2, transferStore, Function.update_apply, hkD, hDD, hTD])
  -- halve
  have e3 := exec_halve KI.kd KI.N KI.Pp (by decide) (by decide) (by decide) mkA d.length 0 s2
    (by simp [hs1, hs2, hkd]) (by norm_num) (by first | exact hPp | simp [hs1, hs2, hPp])
  set s3 := Function.update (Function.update (Function.update s2 KI.kd []) KI.Pp
    (List.replicate (d.length % 2) mkA)) KI.N (List.replicate n mkA) with hs3
  have e3' := exec_congr e3 (t' := s3)
    (by funext k; cases k <;> first | rfl | simp [hs1, hs2, hs3, Function.update_apply, hN, hn])
  -- build `Xv n` and `n + 2`
  obtain ⟨m4, hm4, e4⟩ := exec_build s3 n (by simp [hs1, hs2, hs3]) (by first | exact hXs | simp [hs1, hs2, hs3, hXs])
    (by first | exact hCn | simp [hs1, hs2, hs3, hCn]) (by first | exact hNp | simp [hs1, hs2, hs3, hNp]) (by simp [hs1, hs2, hs3, hsc])
  set s4 := Function.update (Function.update s3 KI.Xs (List.replicate (Xv n) mkA)) KI.Np
    (List.replicate (n + 2) mkA) with hs4
  obtain ⟨m5, hm5, e5⟩ := exec_copy KI.Xs KI.Cn KI.sc (by decide) (by decide) (by decide) s4
    (by simp [hs1, hs2, hs3, hs4, hsc])
  set s5 := Function.update s4 KI.Cn (s4 KI.Xs ++ s4 KI.Cn) with hs5
  have hs5c : s5 KI.kc = List.replicate c.length mkA := by simp [hs1, hs2, hs3, hs4, hs5, hkc]
  have hs5C : s5 KI.Cn = List.replicate (Xv n) mkA := by simp [hs4, hs5, hs3, hs2, hs1, hCn]
  have e6 := exec_syncPop KI.kc KI.Cn (by decide) (min (s5 KI.kc).length (s5 KI.Cn).length) s5 rfl
  rw [hs5c, hs5C] at e6
  simp only [List.length_replicate, List.drop_replicate] at e6
  set s6 := Function.update (Function.update s5 KI.kc
    (List.replicate (c.length - min c.length (Xv n)) mkA)) KI.Cn
    (List.replicate (Xv n - min c.length (Xv n)) mkA) with hs6
  obtain ⟨m7, hm7, e7⟩ := exec_clearG KI.Cn s6
  set r := c.length - Xv n with hr
  set s7 := Function.update s6 KI.Cn [] with hs7
  have hrr : c.length - min c.length (Xv n) = r := by omega
  obtain ⟨m8, hm8, e8⟩ := exec_div KI.kc KI.Np KI.X1 KI.Mq KI.X2 KI.sc (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) mkA (n + 2) (by omega)
    r s7 (by simp [hs7, hs6, hrr]) (by simp [hs7, hs6, hs5, hs4])
    (by first | exact hX1 | simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hX1])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hsc])
  set M := (r + (n + 2) - 1) / (n + 2) with hM
  have hMof : Mof c d = M := by unfold Mof; rw [← hn]
  set s8 := divPost KI.kc KI.Mq KI.X2 mkA s7 r (n + 2) with hs8
  obtain ⟨m9, hm9, e9⟩ := exec_clearG KI.X2 s8
  obtain ⟨m10, hm10, e10⟩ := exec_copy KI.Mq KI.Kc KI.sc (by decide) (by decide) (by decide)
    (Function.update s8 KI.X2 []) (by simp [hs8, divPost, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hsc])
  -- normalize (s14: no store equality; `u` is the store e10 ends in)
  set u := Function.update (Function.update s8 KI.X2 []) KI.Kc
      ((Function.update s8 KI.X2 []) KI.Mq ++ (Function.update s8 KI.X2 []) KI.Kc) with hu
  have hML : M ≤ L := le_trans (ceil_le r (n + 2) (by omega)) (by omega)
  have hnL : n ≤ L := by omega
  obtain ⟨s11, m11, hm11, e11, b, hs11, hb⟩ := exec_kLoop u c d n M L
    rfl rfl rfl
    (he KI.K (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rfl (by simp [hu, hs8, divPost, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hMq, hM])
    (by simp [hu, hs8, divPost, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hMq, hKc, hM])
    (he KI.Ic (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.I (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Tx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Tp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Inf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Wr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Wd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Wp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Cx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Jc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.P (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Q (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.X1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rfl
    (he KI.Y1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Y2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.E (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.St (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.C1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.C2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Fl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.Ca (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (he KI.O (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hML hnL hlc hld
  have hko11 : s11 KI.ko = s KI.ko := by rw [hs11]; rfl
  have hBdu : u KI.Bd = [] := hBd
  rw [hBdu] at hb
  simp only [true_and] at hb
  have hG : MC c d ↔ ∀ k < M, okK c d k n M := by unfold MC; rw [hMof, ← hn]
  -- time
  have g1 : m1 ≤ 3 * L + 1 := by simp [hkC] at hm1; omega
  have g2 : m2 ≤ 3 * L + 1 := by simp [hs1, hkD] at hm2; omega
  have hXv := xv_le n L hnL
  have g5 : m5 ≤ 6 * (2 * L * L + L + 2) + 3 := by
    have : (s4 KI.Xs).length = Xv n := by simp [hs4]
    omega
  have g7 : m7 ≤ 3 * (2 * L * L + L + 2) + 1 := by
    have : (s6 KI.Cn).length ≤ Xv n := by simp [hs6]
    omega
  have g8 : m8 ≤ L * (12 * L + 36) + 1 := by
    have : r * (12 * (n + 2) + 12) ≤ L * (12 * L + 36) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have g9 : m9 ≤ 4 := by
    have : (s8 KI.X2).length ≤ 1 := by
      rw [hs8]; unfold divPost
      simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hX2]; split_ifs <;> simp
    omega
  have g10 : m10 ≤ 6 * L + 3 := by
    have : ((Function.update s8 KI.X2 []) KI.Mq).length = M := by
      simp [hs8, divPost, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hMq]
      rw [hM]; congr 1
    omega
  have g11 : m11 ≤ L * (L * (7000 * ((L + 1) * (L + 1) * (L + 1)) + 6) +
      3000 * ((L + 1) * (L + 1) * (L + 1)) + 20 * L + 40) + 1 := by
    have : M * (L * (7000 * ((L + 1) * (L + 1) * (L + 1)) + 6) +
        3000 * ((L + 1) * (L + 1) * (L + 1)) + 20 * L + 40) ≤ L * (L * (7000 * ((L + 1) * (L + 1)
        * (L + 1)) + 6) + 3000 * ((L + 1) * (L + 1) * (L + 1)) + 20 * L + 40) :=
      Nat.mul_le_mul_right _ hML
    omega
  have g4 : m4 ≤ 12 * L * L + 40 * L + 30 := by
    have : 12 * n * n ≤ 12 * L * L := Nat.mul_le_mul (Nat.mul_le_mul_left 12 hnL) hnL
    omega
  have hc5 := poly_c5 L
  have l1 : 6 * (2 * L * L + L + 2) = 12 * (L * L) + 6 * L + 12 := by ring
  have l2 : 3 * (2 * L * L + L + 2) = 6 * (L * L) + 3 * L + 6 := by ring
  have l3 : 12 * L * L = 12 * (L * L) := by ring
  have hsyn : min c.length (Xv n) ≤ L := by omega
  by_cases hbe : b = []
  · have e12 := exec_skipP (K := KI) s11
    refine ⟨s11, _, ?_, StackProg.Exec.seq e1' (StackProg.Exec.seq e2' (StackProg.Exec.seq e3'
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
      (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10 (StackProg.Exec.seq e11
        (StackProg.Exec.branchTrue (by rw [hs11]; first | exact hbe | simp [hbe]) e12))))))))))), fun _ => hko11, ?_⟩
    · generalize (L + 1) * (L + 1) * (L + 1) = C3 at g11 hc5 ⊢
      generalize L * (L * (7000 * C3 + 6) + 3000 * C3 + 20 * L + 40) = X at g11 hc5 ⊢
      clear * - g1 g2 hdl g4 g5 hsyn g7 g8 g9 g10 g11 hc5 l1 l2 l3
      linarith
    · intro hg; exact absurd (hG.2 (hb.1 hbe)) hg
  · obtain ⟨m12, hm12, e12⟩ := exec_clearG KI.ko s11
    obtain ⟨x, l, hxl⟩ := List.exists_cons_of_ne_nil hbe
    refine ⟨_, _, ?_, StackProg.Exec.seq e1' (StackProg.Exec.seq e2' (StackProg.Exec.seq e3'
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
      (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10 (StackProg.Exec.seq e11
        (StackProg.Exec.branchFalse (by rw [hs11]; first | exact hxl | simp [hxl]) e12))))))))))), ?_, fun _ => by simp⟩
    · rw [hko11] at hm12
      generalize (L + 1) * (L + 1) * (L + 1) = C3 at g11 hc5 ⊢
      generalize L * (L * (7000 * C3 + 6) + 3000 * C3 + 20 * L + 40) = X at g11 hc5 ⊢
      clear * - g1 g2 hdl g4 g5 hsyn g7 g8 g9 g10 g11 hc5 l1 l2 l3 hm12 hko
      linarith
    · intro hg; exact absurd (hb.2 (hG.1 hg)) hbe

/-! ### the whole program -/

lemma len_encNats' (d : List ℕ) : d.length ≤ (encNats d).length := by
  induction d with
  | nil => simp
  | cons k d ih =>
    rw [encNats_cons, List.length_append, List.length_cons]
    have : 1 ≤ (encNat k).length := by
      rw [encNat_dg]; simp only [List.length_append, List.length_singleton]; omega
    omega

def mainProg : SP := .seq (copyProg KI.ki KI.ko KI.sc)
  (.seq (scanProg KI.ki KI.st δA (outA KI.kc KI.kd KI.kC KI.kD))
    (.branch (fun h => decide (h KI.st = some (dsA DS.T0))) phaseB skipP))

set_option maxHeartbeats 8000000 in
theorem mainI (u : List A) : ∃ t n, n ≤ 30000 * ((u.length + 1) * (u.length + 1) * (u.length + 1) *
      (u.length + 1) * (u.length + 1)) ∧
    mainProg.Exec (fun j => if j = KI.ki then u else []) t n ∧
    ((∃ c d, u = Ew c d ∧ ¬MC c d) → t KI.ko = []) ∧
    (¬(∃ c d, u = Ew c d ∧ ¬MC c d) → t KI.ko = u) := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy KI.ki KI.ko KI.sc (by decide) (by decide) (by decide)
    (fun j => if j = KI.ki then u else []) (by simp)
  have hn1' : n1 ≤ 6 * u.length + 3 := by simpa using hn1
  have e1' := exec_congr e1 (t' := fun j => if j = KI.ki ∨ j = KI.ko then u else [])
    (by funext k; cases k <;> first | rfl | simp [Function.update_apply])
  set s1 : KI → List A := fun j => if j = KI.ki ∨ j = KI.ko then u else [] with hs1
  obtain ⟨e2, hiff, hcont, hoth⟩ := scanA_result KI.ki KI.st KI.kc KI.kd KI.kC KI.kD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) u s1 (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
    (by simp [hs1]) (by simp [hs1])
  set s2 := scanRun KI.ki KI.st δA (outA KI.kc KI.kd KI.kC KI.kD) u s1 with hs2
  have hko2 : s2 KI.ko = u := by
    rw [hoth KI.ko (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [hs1]
  have hemp : ∀ k, k ≠ KI.ki → k ≠ KI.ko → k ≠ KI.st → k ≠ KI.kc → k ≠ KI.kd → k ≠ KI.kC →
      k ≠ KI.kD → s2 k = [] := by
    intro k h0 h6 h1 h2 h3 h4 h5
    rw [hoth k h0 h1 h2 h3 h4 h5]; simp [hs1, h0, h6]
  have hp1 : u.length + 1 ≤ (u.length + 1) * (u.length + 1) * (u.length + 1) * (u.length + 1) *
      (u.length + 1) := by
    have h1 : 1 ≤ u.length + 1 := by omega
    calc u.length + 1 = 1 * 1 * 1 * 1 * (u.length + 1) := by ring
      _ ≤ (u.length + 1) * (u.length + 1) * (u.length + 1) * (u.length + 1) * (u.length + 1) := by
        gcongr
  by_cases hsh : ∃ c d, u = Ew c d
  · obtain ⟨c, d, hu⟩ := hsh
    obtain ⟨hkc, hkd, hkC, hkD⟩ := hcont c d hu
    have hlen : (encInts c).length + 1 + (encNats d).length = u.length := by
      rw [hu]; simp [Ew]; omega
    have hd1 := len_encNats' d
    have hc1 := len_encInts' c
    have hst : decide ((s2 KI.st).head? = some (dsA DS.T0)) = true :=
      decide_eq_true (hiff.2 ⟨c, d, hu⟩)
    obtain ⟨t, m, hm, he, hg1, hg2⟩ := exec_phaseB s2 c d u.length hkC hkD hkd hkc hemp
      (by omega) (by omega) (by omega) (by omega) (by rw [hko2])
    have key : (∃ c0 d0, u = Ew c0 d0 ∧ ¬MC c0 d0) ↔ ¬MC c d := by
      constructor
      · rintro ⟨c0, d0, hu0, hg0⟩
        obtain ⟨-, -, hkC0, hkD0⟩ := hcont c0 d0 hu0
        have hcc : c0 = c :=
          encInts_inj _ _ (map_ι1_inj (List.reverse_inj.1 (hkC0.symm.trans hkC)))
        have hdd : d0 = d := encNats_inj (map_ι2_inj (List.reverse_inj.1 (hkD0.symm.trans hkD)))
        rw [← hcc, ← hdd]; exact hg0
      · intro h; exact ⟨c, d, hu, h⟩
    refine ⟨t, n1 + 1 + (3 * u.length + 1 + 1 + (1 + m)), ?_,
      StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchTrue hst he)), ?_, ?_⟩
    · generalize (u.length + 1) * (u.length + 1) * (u.length + 1) * (u.length + 1) *
        (u.length + 1) = P5 at hm hp1 ⊢
      omega
    · intro h; exact hg2 (key.1 h)
    · intro h; rw [hg1 (by by_contra hg; exact h (key.2 hg)), hko2]
  · have hst : decide ((s2 KI.st).head? = some (dsA DS.T0)) = false :=
      decide_eq_false (fun h => hsh (hiff.1 h))
    have e3 := exec_skipP (K := KI) s2
    refine ⟨_, n1 + 1 + (3 * u.length + 1 + 1 + (1 + 1)), by omega,
      StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchFalse hst e3)), ?_, ?_⟩
    · rintro ⟨c, d, hu, -⟩; exact absurd ⟨c, d, hu⟩ hsh
    · intro _; exact hko2

theorem poly_gen (c d : ℕ) : ∃ K, ∀ n : ℕ, c * (n + 1) ^ d ≤ n ^ K + K := by
  refine ⟨c * (c * 2 ^ d + 1) ^ d + d + 1, fun n => ?_⟩
  by_cases hn : n ≤ c * 2 ^ d
  · have h1 : c * (n + 1) ^ d ≤ c * (c * 2 ^ d + 1) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  · push Not at hn
    have hn1 : 1 ≤ n := by omega
    have h2 : (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) _
    have h3 : c * (n + 1) ^ d ≤ c * 2 ^ d * n ^ d := by
      calc c * (n + 1) ^ d ≤ c * (2 * n) ^ d := Nat.mul_le_mul_left _ h2
        _ = c * 2 ^ d * n ^ d := by rw [mul_pow, mul_assoc]
    have h4 : c * 2 ^ d * n ^ d ≤ n * n ^ d := Nat.mul_le_mul_right _ hn.le
    have h5 : n * n ^ d = n ^ (d + 1) := by ring
    have h6 : n ^ (d + 1) ≤ n ^ (c * (c * 2 ^ d + 1) ^ d + d + 1) :=
      Nat.pow_le_pow_right hn1 (by omega)
    omega

/-! ### the specification in the form of the child statement -/

/-- the inventory conditions for resource `k`, in the indexing of the instance code. -/
def BodyI (c : List ℤ) (d : List ℕ) (N M k : ℕ) : Prop :=
  (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
      ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
    ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
      c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
  ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
    (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
        ∑ j ∈ Finset.range N,
          (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
              (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
            then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
      ∑ j ∈ Finset.range N,
          (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
              (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
            then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
        c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0)

def GI (c : List ℤ) (d : List ℕ) : Prop := ∀ N M : ℕ, N = d.length / 2 →
  M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M, BodyI c d N M k

lemma okK_iff (c : List ℤ) (d : List ℕ) (k N M : ℕ) : okK c d k N M ↔ BodyI c d N M k := by
  have i1 : k + Xv N + N * M = 2 + N + 2 * (N * N) + N * M + k := by unfold Xv; ring
  have i2 : 2 + N + 2 * (N * N) + N * M + k + M = 2 + N + 2 * (N * N) + N * M + M + k := by ring
  have hT : ∀ T, invS c d true k N M T =
      ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 := by
    intro T; unfold invS fz
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [if_pos (Or.inl rfl)]
    congr 1; unfold Xv; ring
  have hF : ∀ T, invS c d false k N M T = ∑ j ∈ Finset.range N,
      (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
          (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
            d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
        then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) := by
    intro T; unfold invS fz
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have e : k + Xv N + j * M = 2 + N + 2 * (N * N) + (j * M + k) := by unfold Xv; ring
    rw [e]; simp only [Bool.false_eq_true, false_or]
  have e2 : ∀ i : ℕ, i + 2 = 2 + i := fun i => Nat.add_comm i 2
  unfold okK okAt BodyI
  simp only [hT, hF, i1, i2, e2]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun i hi T hT' => ?_⟩
    rcases hT' with rfl | rfl
    · exact (h1 i hi).1
    · exact (h1 i hi).2
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun i hi => ⟨h1 i hi _ (Or.inl rfl), h1 i hi _ (Or.inr rfl)⟩⟩

lemma GI_iff (c : List ℤ) (d : List ℕ) : GI c d ↔ MC c d := by
  constructor
  · intro h k hk
    exact (okK_iff c d k _ _).2 (h _ _ rfl (by unfold Mof Xv; rfl) k hk)
  · intro h N M hN hM k hk
    subst hN; subst hM
    exact (okK_iff c d k _ _).1 (h k (by unfold Mof Xv; exact hk))

/-- E_inv: the inventory filter (resource sum bounds, and the inventory at every event time)
is computed by a polynomial-time stack program. -/
theorem E_inv : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ N M : ℕ, N = d.length / 2 →
            M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M,
            (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
              ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
                c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
            ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
              (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                  ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
                ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
                  c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0))) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ N M : ℕ, N = d.length / 2 →
            M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M,
            (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
              ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
                c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
            ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
              (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                  ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
                ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
                  c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0))) → s ko = u) := by
  obtain ⟨K, hK⟩ := poly_gen 30000 5
  refine ⟨KI, inferInstance, inferInstance, mainProg, KI.ki, KI.ko, K, fun u => ?_⟩
  obtain ⟨t, n, hn, he, h1, h2⟩ := mainI u
  have hGI : ∀ c d, GI c d ↔ MC c d := GI_iff
  refine ⟨t, n, ?_, he, fun h => h1 ?_, fun h => h2 ?_⟩
  · have e : (u.length + 1) * (u.length + 1) * (u.length + 1) * (u.length + 1) * (u.length + 1) =
        (u.length + 1) ^ 5 := by ring
    have := hK u.length
    rw [e] at hn
    omega
  · obtain ⟨c, d, hu, hg⟩ := h
    exact ⟨c, d, hu, fun hm => hg ((hGI c d).2 hm)⟩
  · rintro ⟨c, d, hu, hg⟩
    exact h ⟨c, d, hu, fun hm => hg ((hGI c d).1 hm)⟩

end D0bfC

theorem solution : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ N M : ℕ, N = d.length / 2 →
            M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M,
            (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
              ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
                c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
            ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
              (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                  ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
                ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
                  c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0))) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(∀ N M : ℕ, N = d.length / 2 →
            M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M,
            (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
              ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
                c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
            ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
              (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                  ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
                ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
                  c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0))) → s ko = u) := by
  exact D0bfC.E_inv
