-- Prove2me | solution 1 for ProjSchedTW.Complexity.cumCheck_len_filter_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:26:39.567064+00:00
-- url     : https://prove2.me/submissions/2c3ef00f-6b7b-4ac0-a4a9-edea00ddd6c0

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

/-! ## E_len stack program (namespace D0bfE) -/

namespace D0bfE
open D0bfL

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


lemma len_encInts (c : List ℤ) : c.length ≤ (encInts c).length := by
  induction c with
  | nil => simp
  | cons z c ih =>
    rw [encInts_cons, List.length_append, List.length_cons]
    have : 1 ≤ (encInt z).length := by
      rw [encInt_split]; simp only [List.length_append, List.length_singleton]; omega
    omega

lemma len_encNats (d : List ℕ) : d.length ≤ (encNats d).length := by
  induction d with
  | nil => simp
  | cons k d ih =>
    rw [encNats_cons, List.length_append, List.length_cons]
    have : 1 ≤ (encNat k).length := by
      rw [encNat_dg]; simp only [List.length_append, List.length_singleton]; omega
    omega

lemma bits_len_le (z : ℤ) (c : List ℤ) : (Nat.bits z.natAbs).length ≤ (encInts (z :: c)).length := by
  rw [encInts_cons, encInt_split]
  simp only [List.length_append, List.length_map, List.length_singleton]
  omega

lemma tail_len_le (z : ℤ) (c : List ℤ) : (encInts c).length ≤ (encInts (z :: c)).length := by
  rw [encInts_cons, List.length_append]; omega

lemma bits_getD_le (c : List ℤ) : (Nat.bits (c.getD 0 0).natAbs).length ≤ (encInts c).length := by
  rcases c with _ | ⟨z, c⟩
  · simp [Nat.zero_bits]
  · simpa using bits_len_le z c

inductive KS
  | ki | ko | sc | st | kc | kd | kC | kD | CC | N | Pp | Bd | N2 | W | H | P | Xs | Cn | Np | Y | Q
  deriving DecidableEq

instance : Fintype KS := Fintype.ofList
  [KS.ki, KS.ko, KS.sc, KS.st, KS.kc, KS.kd, KS.kC, KS.kD, KS.CC, KS.N, KS.Pp, KS.Bd, KS.N2, KS.W,
    KS.H, KS.P, KS.Xs, KS.Cn, KS.Np, KS.Y, KS.Q] (by intro x; cases x <;> simp)

abbrev SP := StackProg KS A

def Res (s t : KS → List A) (Q : Prop) : Prop := (Q → t KS.ko = s KS.ko) ∧ (¬Q → t KS.ko = [])

lemma res_iff {s t : KS → List A} {Q Q' : Prop} (h : Res s t Q) (e : Q ↔ Q') : Res s t Q' :=
  ⟨fun q => h.1 (e.2 q), fun q => h.2 (fun q' => q (e.1 q'))⟩

lemma exec_congr {p : SP} {s t t' : KS → List A} {n : ℕ} (h : p.Exec s t n) (e : t = t') :
    p.Exec s t' n := e ▸ h

def flagProg (t : (KS → Option A) → Bool) : SP :=
  .act (fun h k => if k = KS.Bd ∧ t h = true then .push mkA else .keep)

def skipProg : SP := .act (fun _ _ => .keep)

def guard (step rest : SP) : SP :=
  .seq step (.branch (fun h => (h KS.Bd).isNone) rest (clearProg KS.ko))

lemma exec_flag (t : (KS → Option A) → Bool) (s : KS → List A) :
    (flagProg t).Exec s (Function.update s KS.Bd
      (if t (fun k => (s k).head?) = true then mkA :: s KS.Bd else s KS.Bd)) 1 := by
  unfold flagProg
  refine exec_congr (StackProg.Exec.act _ s) ?_
  funext k
  by_cases hk : k = KS.Bd
  · subst hk
    by_cases ht : t (fun k => (s k).head?) = true <;> simp [StackProg.applyAct, StackAct.apply, ht]
  · simp [StackProg.applyAct, StackAct.apply, hk]

lemma exec_skip (s : KS → List A) : skipProg.Exec s s 1 := by
  unfold skipProg
  refine exec_congr (StackProg.Exec.act _ s) ?_
  funext k; simp [StackProg.applyAct, StackAct.apply]

lemma exec_push (c : KS) (a : A) (s : KS → List A) :
    (pushProg c a).Exec s (Function.update s c (a :: s c)) 1 := by
  unfold pushProg
  refine exec_congr (StackProg.Exec.act _ s) ?_
  funext k; by_cases k1 : k = c
  · subst k1; simp [StackProg.applyAct, StackAct.apply]
  · simp [StackProg.applyAct, StackAct.apply, k1]

lemma exec_clear (c : KS) (s : KS → List A) :
    ∃ n ≤ 3 * (s c).length + 1, (clearProg c).Exec s (Function.update s c []) n := by
  obtain ⟨n, hn, h⟩ := exec_transfer c (fun _ => false) (s c) s rfl
  refine ⟨n, hn, exec_congr h ?_⟩
  funext k; by_cases k1 : k = c
  · subst k1; simp [transferStore]
  · simp [transferStore, k1]

lemma exec_guard (step rest : SP) (s t : KS → List A) (n R : ℕ) (P1 P2 : Prop)
    (hst : step.Exec s t n) (hko : t KS.ko = s KS.ko) (hc : t KS.Bd = [] ↔ P1)
    (hrest : t KS.Bd = [] → ∃ t' m, m ≤ R ∧ rest.Exec t t' m ∧ Res t t' P2) :
    ∃ t' m, m ≤ n + R + 3 * (s KS.ko).length + 4 ∧ (guard step rest).Exec s t' m ∧
      Res s t' (P1 ∧ P2) := by
  by_cases hb : t KS.Bd = []
  · obtain ⟨t', m, hm, he, h1, h2⟩ := hrest hb
    refine ⟨t', n + 1 + (1 + m), by omega,
      StackProg.Exec.seq hst (StackProg.Exec.branchTrue (by simp [hb]) he), ?_, ?_⟩
    · rintro ⟨-, h⟩; rw [h1 h, hko]
    · intro h; exact h2 (fun h' => h ⟨hc.1 hb, h'⟩)
  · obtain ⟨m, hm, he⟩ := exec_clear KS.ko t
    obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hb
    refine ⟨_, n + 1 + (1 + m), by rw [hko] at hm; omega,
      StackProg.Exec.seq hst (StackProg.Exec.branchFalse (by simp [hal]) he), ?_, ?_⟩
    · rintro ⟨h, -⟩; exact absurd (hc.2 h) hb
    · intro _; simp

lemma flag_rep (q : ℕ) (l : List A) :
    (if (List.replicate q mkA).head?.isSome = true then mkA :: l else l) = [] ↔ (q = 0 ∧ l = []) := by
  cases q <;> simp

/-! ### stage 7: compare the last token with `Q` -/

def prog7 : SP := guard (.seq (hcLoop KS.W KS.Q KS.H KS.P KS.Bd mkA isDA isOneA)
  (flagProg (fun h => (h KS.Q).isSome))) skipProg

lemma st7 (s : KS → List A) (a v L : ℕ) (r : List A) (hr : isDA r.head? = false)
    (hW : s KS.W = (Nat.bits a).map dsymA ++ r) (hQ : s KS.Q = List.replicate v mkA)
    (hH : s KS.H = []) (hP : s KS.P = []) (hB : s KS.Bd = [])
    (ha : (Nat.bits a).length ≤ L) (hv : v ≤ L) (hko : (s KS.ko).length ≤ L) :
    ∃ t m, m ≤ 30 * (L + 1) ^ 2 ∧ prog7.Exec s t m ∧ Res s t (a = v) := by
  obtain ⟨n1, hn1, e1⟩ := exec_hc KS.W KS.Q KS.H KS.P KS.Bd (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    mkA dsymA isDA isOneA isDA_dsym isOneA_dsym r hr (Nat.bits a) v s hW hQ hH hP
  have e2 := exec_flag (fun h => (h KS.Q).isSome) (hcPost KS.W KS.Q KS.Bd mkA s (Nat.bits a) v r)
  have hQ1 : hcPost KS.W KS.Q KS.Bd mkA s (Nat.bits a) v r KS.Q =
      List.replicate (v / 2 ^ (Nat.bits a).length) mkA := by simp [hcPost, Function.update_apply]
  have hB1 : hcPost KS.W KS.Q KS.Bd mkA s (Nat.bits a) v r KS.Bd =
      List.replicate (mism (Nat.bits a) v) mkA := by simp [hcPost, Function.update_apply, hB]
  have hk1 : hcPost KS.W KS.Q KS.Bd mkA s (Nat.bits a) v r KS.ko = s KS.ko := by
    simp [hcPost, Function.update_apply]
  obtain ⟨t, m, hm, he, hres⟩ := exec_guard _ skipProg s _ _ 1 (a = v) True
    (StackProg.Exec.seq e1 e2) (by simp [Function.update_apply, hk1])
    (by
      rw [Function.update_self]
      simp only [hQ1, hB1]
      rw [flag_rep, List.replicate_eq_nil_iff, and_comm]
      exact mism_bits a v)
    (fun _ => ⟨_, 1, le_rfl, exec_skip _, fun _ => rfl, fun h => absurd trivial h⟩)
  refine ⟨t, m, ?_, he, res_iff hres ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩⟩
  have h1 : (Nat.bits a).length * (6 * v + 12) ≤ L * (6 * L + 12) := Nat.mul_le_mul ha (by omega)
  nlinarith

/-! ### stage 6: divide by `N + 2` -/

def prog6 : SP := guard (divLoop KS.kc KS.Np KS.Y KS.Q KS.Bd KS.sc mkA) prog7

lemma ceil_div_of_mod (r D : ℕ) (hD : 1 ≤ D) (h : r % D = 0) : (r + D - 1) / D = r / D := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rw [Nat.mul_div_cancel_left q (by omega)]
  have e : D * q + D - 1 = (D - 1) + D * q := by
    generalize D * q = X; omega
  rw [e, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]

lemma st6 (s : KS → List A) (a r D L : ℕ) (r' : List A) (hr' : isDA r'.head? = false) (hD : 1 ≤ D)
    (hW : s KS.W = (Nat.bits a).map dsymA ++ r') (hc : s KS.kc = List.replicate r mkA)
    (hNp : s KS.Np = List.replicate D mkA) (hY : s KS.Y = []) (hsc : s KS.sc = [])
    (hQ : s KS.Q = []) (hH : s KS.H = []) (hP : s KS.P = []) (hB : s KS.Bd = [])
    (ha : (Nat.bits a).length ≤ L) (hrL : r ≤ L) (hDL : D ≤ L + 2) (hko : (s KS.ko).length ≤ L) :
    ∃ t m, m ≤ 80 * (L + 1) ^ 2 ∧ prog6.Exec s t m ∧ Res s t (r % D = 0 ∧ a = r / D) := by
  obtain ⟨n1, hn1, e1⟩ := exec_div KS.kc KS.Np KS.Y KS.Q KS.Bd KS.sc (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) mkA D hD r s hc hNp hY hsc
  have hB1 : divPost KS.kc KS.Q KS.Bd mkA s r D KS.Bd =
      List.replicate (if r % D = 0 then 0 else 1) mkA := by
    simp [divPost, Function.update_apply, hB]
  obtain ⟨t, m, hm, he, hres⟩ := exec_guard _ prog7 s _ n1 (30 * (L + 1) ^ 2) (r % D = 0) (a = r / D) e1
    (by simp [divPost, Function.update_apply])
    (by rw [hB1]; split_ifs with h <;> simp [h])
    (fun hb => by
      have hr0 : r % D = 0 := by
        rw [hB1] at hb; split_ifs at hb with h
        · exact h
        · simp at hb
      have hQ1 : divPost KS.kc KS.Q KS.Bd mkA s r D KS.Q = List.replicate ((r + D - 1) / D) mkA := by
        simp [divPost, Function.update_apply, hQ]
      rw [ceil_div_of_mod r D hD hr0] at hQ1
      exact st7 _ a (r / D) L r' hr'
        (by simp [divPost, Function.update_apply, hW]) hQ1
        (by simp [divPost, Function.update_apply, hH]) (by simp [divPost, Function.update_apply, hP]) hb ha
        (le_trans (Nat.div_le_self r D) hrL) (by simpa [divPost, Function.update_apply] using hko))
  refine ⟨t, m, ?_, he, hres⟩
  have h1 : r * (12 * D + 12) ≤ L * (12 * (L + 2) + 12) := Nat.mul_le_mul hrL (by omega)
  nlinarith


/-! ### stage 5: build `Xv N` and `N + 2`, compare `|c|` with `Xv N` -/

def buildProg : SP :=
  .seq (pushProg KS.Xs mkA) (.seq (pushProg KS.Xs mkA) (.seq (copyProg KS.N KS.Xs KS.sc)
  (.seq (copyProg KS.N KS.Cn KS.sc) (.seq (copyProg KS.N KS.Cn KS.sc)
  (.seq (rcLoop KS.N KS.Xs KS.Cn KS.sc) (.seq (copyProg KS.N KS.Np KS.sc)
  (.seq (pushProg KS.Np mkA) (pushProg KS.Np mkA))))))))

lemma xv_rep (N : ℕ) : List.replicate (Xv N) mkA =
    List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]) := by
  have e : Xv N = (N + N) * N + N + 2 := by unfold Xv; ring
  rw [e, List.replicate_add, List.replicate_add, List.append_assoc]; rfl

lemma rep2 (N : ℕ) : List.replicate (N + 2) mkA = mkA :: mkA :: List.replicate N mkA := rfl

lemma exec_build (s : KS → List A) (N : ℕ) (hN : s KS.N = List.replicate N mkA) (hX : s KS.Xs = [])
    (hCn : s KS.Cn = []) (hNp : s KS.Np = []) (hsc : s KS.sc = []) :
    ∃ n ≤ 12 * N * N + 40 * N + 30, buildProg.Exec s
      (Function.update (Function.update s KS.Xs (List.replicate (Xv N) mkA)) KS.Np
        (List.replicate (N + 2) mkA)) n := by
  have e1 : (pushProg KS.Xs mkA).Exec s (Function.update s KS.Xs [mkA]) 1 :=
    exec_congr (exec_push KS.Xs mkA s) (by funext k; cases k <;> simp [Function.update_apply, hX])
  have e2 : (pushProg KS.Xs mkA).Exec (Function.update s KS.Xs [mkA])
      (Function.update s KS.Xs [mkA, mkA]) 1 :=
    exec_congr (exec_push KS.Xs mkA _) (by funext k; cases k <;> simp [Function.update_apply])
  obtain ⟨n3, hn3, e3⟩ := exec_copy KS.N KS.Xs KS.sc (by decide) (by decide) (by decide)
    (Function.update s KS.Xs [mkA, mkA]) (by simp [Function.update_apply, hsc])
  have e3' := exec_congr e3 (t' := Function.update s KS.Xs (List.replicate N mkA ++ [mkA, mkA]))
    (by funext k; cases k <;> simp [Function.update_apply, hN])
  have hn3' : n3 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn3
  obtain ⟨n4, hn4, e4⟩ := exec_copy KS.N KS.Cn KS.sc (by decide) (by decide) (by decide)
    (Function.update s KS.Xs (List.replicate N mkA ++ [mkA, mkA]))
    (by simp [Function.update_apply, hsc])
  have e4' := exec_congr e4 (t' := Function.update (Function.update s KS.Xs
      (List.replicate N mkA ++ [mkA, mkA])) KS.Cn (List.replicate N mkA))
    (by funext k; cases k <;> simp [Function.update_apply, hN, hCn])
  have hn4' : n4 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn4
  obtain ⟨n5, hn5, e5⟩ := exec_copy KS.N KS.Cn KS.sc (by decide) (by decide) (by decide)
    (Function.update (Function.update s KS.Xs (List.replicate N mkA ++ [mkA, mkA])) KS.Cn
      (List.replicate N mkA)) (by simp [Function.update_apply, hsc])
  have e5' := exec_congr e5 (t' := Function.update (Function.update s KS.Xs
      (List.replicate N mkA ++ [mkA, mkA])) KS.Cn (List.replicate N mkA ++ List.replicate N mkA))
    (by funext k; cases k <;> simp [Function.update_apply, hN])
  have hn5' : n5 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn5
  obtain ⟨n6, hn6, e6⟩ := exec_rc KS.N KS.Xs KS.Cn KS.sc (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) mkA N (N + N)
    (Function.update (Function.update s KS.Xs (List.replicate N mkA ++ [mkA, mkA])) KS.Cn
      (List.replicate N mkA ++ List.replicate N mkA))
    (by simp [Function.update_apply]) (by simp [Function.update_apply, hN])
    (by simp [Function.update_apply, hsc])
  have e6' := exec_congr e6 (t' := Function.update s KS.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA])))
    (by funext k; cases k <;> simp [Function.update_apply, hCn])
  obtain ⟨n7, hn7, e7⟩ := exec_copy KS.N KS.Np KS.sc (by decide) (by decide) (by decide)
    (Function.update s KS.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA])))
    (by simp [Function.update_apply, hsc])
  have e7' := exec_congr e7 (t' := Function.update (Function.update s KS.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KS.Np
      (List.replicate N mkA))
    (by funext k; cases k <;> simp [Function.update_apply, hN, hNp])
  have hn7' : n7 ≤ 6 * N + 3 := by simpa [Function.update_apply, hN] using hn7
  have e8 := exec_congr (exec_push KS.Np mkA (Function.update (Function.update s KS.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KS.Np
      (List.replicate N mkA))) (t' := Function.update (Function.update s KS.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KS.Np
      (mkA :: List.replicate N mkA))
    (by funext k; cases k <;> simp [Function.update_apply])
  have e9 := exec_congr (exec_push KS.Np mkA (Function.update (Function.update s KS.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KS.Np
      (mkA :: List.replicate N mkA))) (t' := Function.update (Function.update s KS.Xs
      (List.replicate ((N + N) * N) mkA ++ (List.replicate N mkA ++ [mkA, mkA]))) KS.Np
      (mkA :: mkA :: List.replicate N mkA))
    (by funext k; cases k <;> simp [Function.update_apply])
  rw [xv_rep N, rep2 N]
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3'
    (StackProg.Exec.seq e4' (StackProg.Exec.seq e5' (StackProg.Exec.seq e6'
    (StackProg.Exec.seq e7' (StackProg.Exec.seq e8 e9)))))))⟩
  have h6 : (N + N) * (6 * N + 8) = 12 * N * N + 16 * N := by ring
  rw [h6] at hn6
  omega

def step5 : SP :=
  .seq buildProg (.seq (syncPopProg KS.kc KS.Xs) (flagProg (fun h => (h KS.Xs).isSome)))
def prog5 : SP := guard step5 prog6

lemma st5 (s : KS → List A) (a N cl L : ℕ) (r' : List A) (hr' : isDA r'.head? = false)
    (hW : s KS.W = (Nat.bits a).map dsymA ++ r') (hN : s KS.N = List.replicate N mkA)
    (hc : s KS.kc = List.replicate cl mkA) (hX : s KS.Xs = []) (hCn : s KS.Cn = [])
    (hNp : s KS.Np = []) (hY : s KS.Y = []) (hsc : s KS.sc = []) (hQ : s KS.Q = [])
    (hH : s KS.H = []) (hP : s KS.P = []) (hB : s KS.Bd = [])
    (ha : (Nat.bits a).length ≤ L) (hNL : N ≤ L) (hcl : cl ≤ L) (hko : (s KS.ko).length ≤ L) :
    ∃ t m, m ≤ 150 * (L + 1) ^ 2 ∧ prog5.Exec s t m ∧
      Res s t (Xv N ≤ cl ∧ (cl - Xv N) % (N + 2) = 0 ∧ a = (cl - Xv N) / (N + 2)) := by
  obtain ⟨n1, hn1, e1⟩ := exec_build s N hN hX hCn hNp hsc
  have e2 := exec_syncPop KS.kc KS.Xs (by decide) (min cl (Xv N))
    (Function.update (Function.update s KS.Xs (List.replicate (Xv N) mkA)) KS.Np
      (List.replicate (N + 2) mkA)) (by simp [Function.update_apply, hc])
  have h1 : cl - min cl (Xv N) = cl - Xv N := by omega
  have h2 : Xv N - min cl (Xv N) = Xv N - cl := by omega
  have e2' := exec_congr e2 (t' := Function.update (Function.update (Function.update s KS.Xs
      (List.replicate (Xv N - cl) mkA)) KS.Np (List.replicate (N + 2) mkA)) KS.kc
      (List.replicate (cl - Xv N) mkA))
    (by funext k; cases k <;> simp [Function.update_apply, hc, List.drop_replicate, h1, h2])
  have e3 := exec_flag (fun h => (h KS.Xs).isSome) (Function.update (Function.update
    (Function.update s KS.Xs (List.replicate (Xv N - cl) mkA)) KS.Np (List.replicate (N + 2) mkA))
    KS.kc (List.replicate (cl - Xv N) mkA))
  obtain ⟨t, m, hm, he, hres⟩ := exec_guard _ prog6 s _ _ (80 * (L + 1) ^ 2) (Xv N ≤ cl)
    ((cl - Xv N) % (N + 2) = 0 ∧ a = (cl - Xv N) / (N + 2))
    (StackProg.Exec.seq e1 (StackProg.Exec.seq e2' e3))
    (by simp [Function.update_apply])
    (by
      rw [Function.update_self]
      simp only [Function.update_apply, hB, reduceCtorEq, if_false, if_true]
      rw [flag_rep]; simp; omega)
    (fun hb => by
      have hle : Xv N ≤ cl := by
        by_contra hlt
        rw [Function.update_self] at hb
        simp only [Function.update_apply, hB, reduceCtorEq, if_false, if_true] at hb
        rw [flag_rep] at hb
        omega
      exact st6 _ a (cl - Xv N) (N + 2) L r' hr' (by omega)
        (by simp [Function.update_apply, hW]) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) (by simp [Function.update_apply, hY])
        (by simp [Function.update_apply, hsc]) (by simp [Function.update_apply, hQ])
        (by simp [Function.update_apply, hH]) (by simp [Function.update_apply, hP]) hb ha
        (by omega) (by omega) (by simpa [Function.update_apply] using hko))
  refine ⟨t, m, ?_, he, hres⟩
  have hNN : N * N ≤ L * L := Nat.mul_le_mul hNL hNL
  have hmin : min cl (Xv N) ≤ L := le_trans (Nat.min_le_left _ _) hcl
  nlinarith

/-! ### stage 4: drop the separator, sign check on `c'` -/

def prog4 : SP := guard (.seq (popProg KS.W)
  (flagProg (fun h => decide (h KS.W = some (ι1 BSym.minus))))) prog5

lemma head_minus_iff (c : List ℤ) :
    ((encInts c).map ι1).head? = some (ι1 BSym.minus) ↔ ¬ (∀ z c', c = z :: c' → 0 ≤ z) := by
  rcases c with _ | ⟨z, c'⟩
  · simp [encInts]
  · by_cases hz : 0 ≤ z
    · rw [encInts_head_nonneg z hz]
      constructor
      · intro h; exfalso
        rcases hb : Nat.bits z.natAbs with _ | ⟨b, l⟩
        · rw [hb] at h; simp [ι1] at h
        · rw [hb] at h; cases b <;> simp [dsymA, dg, ι1] at h
      · intro h
        exact absurd (fun z0 c0 (e : z :: c' = z0 :: c0) => by
          rw [List.cons.injEq] at e; rw [← e.1]; exact hz) h
    · rw [encInts_head_neg z (by omega)]
      simp only [true_iff]
      intro h; exact hz (h z c' rfl)

lemma W_decomp (c : List ℤ) (h : ∀ z c', c = z :: c' → 0 ≤ z) :
    ∃ r', isDA r'.head? = false ∧
      (encInts c).map ι1 = (Nat.bits (c.getD 0 0).natAbs).map dsymA ++ r' := by
  rcases c with _ | ⟨z, c'⟩
  · exact ⟨[], rfl, by simp [encInts, Nat.zero_bits]⟩
  · refine ⟨ι1 BSym.sep :: (encInts c').map ι1, isDA_sep, ?_⟩
    rw [encInts_head_nonneg z (h z c' rfl)]
    simp

lemma st4 (s : KS → List A) (c' : List ℤ) (N cl L : ℕ)
    (hW : s KS.W = ι1 BSym.sep :: (encInts c').map ι1) (hN : s KS.N = List.replicate N mkA)
    (hc : s KS.kc = List.replicate cl mkA) (hX : s KS.Xs = []) (hCn : s KS.Cn = [])
    (hNp : s KS.Np = []) (hY : s KS.Y = []) (hsc : s KS.sc = []) (hQ : s KS.Q = [])
    (hH : s KS.H = []) (hP : s KS.P = []) (hB : s KS.Bd = [])
    (hcL : (encInts c').length ≤ L) (hNL : N ≤ L) (hcl : cl ≤ L) (hko : (s KS.ko).length ≤ L) :
    ∃ t m, m ≤ 160 * (L + 1) ^ 2 ∧ prog4.Exec s t m ∧
      Res s t ((∀ z' c'', c' = z' :: c'' → 0 ≤ z') ∧ (Xv N ≤ cl ∧ (cl - Xv N) % (N + 2) = 0 ∧
        (c'.getD 0 0).natAbs = (cl - Xv N) / (N + 2))) := by
  have e1 := exec_pop KS.W s
  have e2 := exec_flag (fun h => decide (h KS.W = some (ι1 BSym.minus)))
    (Function.update s KS.W (s KS.W).tail)
  have hW1 : Function.update s KS.W (s KS.W).tail KS.W = (encInts c').map ι1 := by simp [hW]
  have hB1 : Function.update s KS.W (s KS.W).tail KS.Bd = [] := by
    simp [Function.update_apply, hB]
  obtain ⟨t, m, hm, he, hres⟩ := exec_guard _ prog5 s _ _ (150 * (L + 1) ^ 2)
    (∀ z' c'', c' = z' :: c'' → 0 ≤ z')
    (Xv N ≤ cl ∧ (cl - Xv N) % (N + 2) = 0 ∧ (c'.getD 0 0).natAbs = (cl - Xv N) / (N + 2))
    (StackProg.Exec.seq e1 e2)
    (by simp [Function.update_apply])
    (by
      rw [Function.update_self]
      simp only [hW1, hB1]
      by_cases hm : ((encInts c').map ι1).head? = some (ι1 BSym.minus)
      · rw [if_pos (by simpa using hm)]
        exact iff_of_false (List.cons_ne_nil _ _) ((head_minus_iff c').1 hm)
      · rw [if_neg (by simpa using hm)]
        exact iff_of_true rfl (not_not.1 (mt (head_minus_iff c').2 hm)))
    (fun hb => by
      have hpos : ∀ z' c'', c' = z' :: c'' → 0 ≤ z' := by
        by_contra hneg
        have hm := (head_minus_iff c').2 hneg
        rw [Function.update_self] at hb
        simp only [hW1, hB1] at hb
        rw [if_pos (by simpa using hm)] at hb
        exact List.cons_ne_nil _ _ hb
      obtain ⟨r', hr', hWd⟩ := W_decomp c' hpos
      exact st5 _ (c'.getD 0 0).natAbs N cl L r' hr'
        (by simp [Function.update_apply, hW, hWd]) (by simp [Function.update_apply, hN])
        (by simp [Function.update_apply, hc]) (by simp [Function.update_apply, hX])
        (by simp [Function.update_apply, hCn]) (by simp [Function.update_apply, hNp])
        (by simp [Function.update_apply, hY]) (by simp [Function.update_apply, hsc])
        (by simp [Function.update_apply, hQ]) (by simp [Function.update_apply, hH])
        (by simp [Function.update_apply, hP]) hb (le_trans (bits_getD_le c') hcL) hNL hcl
        (by simpa [Function.update_apply] using hko))
  exact ⟨t, m, by nlinarith, he, hres⟩

/-! ### stage 3: compare the first token `z` with `N - 2` -/

def prog3 : SP := guard (.seq (hcLoop KS.W KS.N2 KS.H KS.P KS.Bd mkA isDA isOneA)
  (flagProg (fun h => (h KS.N2).isSome))) prog4

lemma st3 (s : KS → List A) (z : ℤ) (c' : List ℤ) (v N cl L : ℕ)
    (hW : s KS.W = (Nat.bits z.natAbs).map dsymA ++ ι1 BSym.sep :: (encInts c').map ι1)
    (hN2 : s KS.N2 = List.replicate v mkA) (hN : s KS.N = List.replicate N mkA)
    (hc : s KS.kc = List.replicate cl mkA) (hX : s KS.Xs = []) (hCn : s KS.Cn = [])
    (hNp : s KS.Np = []) (hY : s KS.Y = []) (hsc : s KS.sc = []) (hQ : s KS.Q = [])
    (hH : s KS.H = []) (hP : s KS.P = []) (hB : s KS.Bd = [])
    (hz : (Nat.bits z.natAbs).length ≤ L) (hv : v ≤ L) (hcL : (encInts c').length ≤ L)
    (hNL : N ≤ L) (hcl : cl ≤ L) (hko : (s KS.ko).length ≤ L) :
    ∃ t m, m ≤ 170 * (L + 1) ^ 2 ∧ prog3.Exec s t m ∧
      Res s t (z.natAbs = v ∧ ((∀ z' c'', c' = z' :: c'' → 0 ≤ z') ∧ (Xv N ≤ cl ∧
        (cl - Xv N) % (N + 2) = 0 ∧ (c'.getD 0 0).natAbs = (cl - Xv N) / (N + 2)))) := by
  obtain ⟨n1, hn1, e1⟩ := exec_hc KS.W KS.N2 KS.H KS.P KS.Bd (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    mkA dsymA isDA isOneA isDA_dsym isOneA_dsym (ι1 BSym.sep :: (encInts c').map ι1) isDA_sep
    (Nat.bits z.natAbs) v s hW hN2 hH hP
  have e2 := exec_flag (fun h => (h KS.N2).isSome)
    (hcPost KS.W KS.N2 KS.Bd mkA s (Nat.bits z.natAbs) v (ι1 BSym.sep :: (encInts c').map ι1))
  have hQ1 : hcPost KS.W KS.N2 KS.Bd mkA s (Nat.bits z.natAbs) v
      (ι1 BSym.sep :: (encInts c').map ι1) KS.N2 =
      List.replicate (v / 2 ^ (Nat.bits z.natAbs).length) mkA := by simp [hcPost]
  have hB1 : hcPost KS.W KS.N2 KS.Bd mkA s (Nat.bits z.natAbs) v
      (ι1 BSym.sep :: (encInts c').map ι1) KS.Bd =
      List.replicate (mism (Nat.bits z.natAbs) v) mkA := by simp [hcPost, hB]
  obtain ⟨t, m, hm, he, hres⟩ := exec_guard _ prog4 s _ _ (160 * (L + 1) ^ 2) (z.natAbs = v)
    ((∀ z' c'', c' = z' :: c'' → 0 ≤ z') ∧ (Xv N ≤ cl ∧
        (cl - Xv N) % (N + 2) = 0 ∧ (c'.getD 0 0).natAbs = (cl - Xv N) / (N + 2)))
    (StackProg.Exec.seq e1 e2) (by simp [Function.update_apply, hcPost])
    (by
      rw [Function.update_self]
      simp only [hQ1, hB1]
      rw [flag_rep, List.replicate_eq_nil_iff, and_comm]
      exact mism_bits z.natAbs v)
    (fun hb => st4 _ c' N cl L (by simp [Function.update_apply, hcPost])
        (by simp [Function.update_apply, hcPost, hN]) (by simp [Function.update_apply, hcPost, hc])
        (by simp [Function.update_apply, hcPost, hX]) (by simp [Function.update_apply, hcPost, hCn])
        (by simp [Function.update_apply, hcPost, hNp]) (by simp [Function.update_apply, hcPost, hY])
        (by simp [Function.update_apply, hcPost, hsc]) (by simp [Function.update_apply, hcPost, hQ])
        (by simp [Function.update_apply, hcPost, hH]) (by simp [Function.update_apply, hcPost, hP])
        hb hcL hNL hcl (by simpa [Function.update_apply, hcPost] using hko))
  refine ⟨t, m, ?_, he, hres⟩
  have h1 : (Nat.bits z.natAbs).length * (6 * v + 12) ≤ L * (6 * L + 12) :=
    Nat.mul_le_mul hz (by omega)
  nlinarith

/-! ### stage 2: `N - 2`, copy of the integer part, first-token sign check -/

def step2 : SP := .seq (copyProg KS.N KS.N2 KS.sc) (.seq (popProg KS.N2) (.seq (popProg KS.N2)
  (.seq (copyProg KS.CC KS.W KS.sc) (flagProg (fun h => !isDA (h KS.W))))))
def prog2 : SP := guard step2 prog3

lemma isDA_head_iff (c : List ℤ) :
    isDA ((encInts c).map ι1).head? = true ↔ ∃ z c', c = z :: c' ∧ 1 ≤ z := by
  rcases c with _ | ⟨z, c'⟩
  · simp [encInts, isDA]
  · by_cases hz : 0 ≤ z
    · rw [head_encInts_nonneg z hz]
      simp only [decide_eq_true_eq, List.cons.injEq]
      constructor
      · intro h; exact ⟨z, c', ⟨rfl, rfl⟩, by omega⟩
      · rintro ⟨z0, c0, ⟨rfl, rfl⟩, h⟩; omega
    · rw [encInts_head_neg z (by omega)]
      constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨z0, c0, e, h⟩; rw [List.cons.injEq] at e; omega

lemma st2 (s : KS → List A) (c : List ℤ) (N L : ℕ)
    (hCC : s KS.CC = (encInts c).map ι1) (hN : s KS.N = List.replicate N mkA) (hN2 : s KS.N2 = [])
    (hW : s KS.W = []) (hc : s KS.kc = List.replicate c.length mkA) (hX : s KS.Xs = [])
    (hCn : s KS.Cn = []) (hNp : s KS.Np = []) (hY : s KS.Y = []) (hsc : s KS.sc = [])
    (hQ : s KS.Q = []) (hH : s KS.H = []) (hP : s KS.P = []) (hB : s KS.Bd = [])
    (hcL : (encInts c).length ≤ L) (hNL : N ≤ L) (hcl : c.length ≤ L)
    (hko : (s KS.ko).length ≤ L) :
    ∃ t m, m ≤ 200 * (L + 1) ^ 2 ∧ prog2.Exec s t m ∧
      Res s t (∃ z c', c = z :: c' ∧ 1 ≤ z ∧ z.natAbs = N - 2 ∧
        ((∀ z' c'', c' = z' :: c'' → 0 ≤ z') ∧ (Xv N ≤ c.length ∧
          (c.length - Xv N) % (N + 2) = 0 ∧ (c'.getD 0 0).natAbs = (c.length - Xv N) / (N + 2)))) := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy KS.N KS.N2 KS.sc (by decide) (by decide) (by decide) s hsc
  have e1' := exec_congr e1 (t' := Function.update s KS.N2 (List.replicate N mkA))
    (by funext k; cases k <;> simp [Function.update_apply, hN, hN2])
  have hn1' : n1 ≤ 6 * N + 3 := by simpa [hN] using hn1
  have e2 := exec_congr (exec_pop KS.N2 (Function.update s KS.N2 (List.replicate N mkA)))
    (t' := Function.update s KS.N2 (List.replicate (N - 1) mkA))
    (by funext k; cases k <;> simp [Function.update_apply])
  have e3 := exec_congr (exec_pop KS.N2 (Function.update s KS.N2 (List.replicate (N - 1) mkA)))
    (t' := Function.update s KS.N2 (List.replicate (N - 2) mkA))
    (by funext k; cases k <;> simp [Function.update_apply, Nat.sub_sub])
  obtain ⟨n4, hn4, e4⟩ := exec_copy KS.CC KS.W KS.sc (by decide) (by decide) (by decide)
    (Function.update s KS.N2 (List.replicate (N - 2) mkA)) (by simp [Function.update_apply, hsc])
  have e4' := exec_congr e4 (t' := Function.update (Function.update s KS.N2
      (List.replicate (N - 2) mkA)) KS.W ((encInts c).map ι1))
    (by funext k; cases k <;> simp [Function.update_apply, hCC, hW])
  have hn4' : n4 ≤ 6 * L + 3 := by
    have h := hn4; simp [Function.update_apply, hCC] at h; omega
  set S4 := Function.update (Function.update s KS.N2 (List.replicate (N - 2) mkA)) KS.W
    ((encInts c).map ι1) with hS4
  have e5 := exec_flag (fun h => !isDA (h KS.W)) S4
  have hW4 : S4 KS.W = (encInts c).map ι1 := by simp [hS4]
  have hB4 : S4 KS.Bd = [] := by simp [hS4, Function.update_apply, hB]
  obtain ⟨t, m, hm, he, hres⟩ := exec_guard _ prog3 s _ _ (170 * (L + 1) ^ 2)
    (∃ z c', c = z :: c' ∧ 1 ≤ z)
    (∀ z c', c = z :: c' → (z.natAbs = N - 2 ∧ ((∀ z' c'', c' = z' :: c'' → 0 ≤ z') ∧
      (Xv N ≤ c.length ∧ (c.length - Xv N) % (N + 2) = 0 ∧
        (c'.getD 0 0).natAbs = (c.length - Xv N) / (N + 2)))))
    (StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4' e5))))
    (by simp [hS4, Function.update_apply])
    (by
      rw [Function.update_self]
      simp only [hW4, hB4]
      cases hd : isDA ((encInts c).map ι1).head?
      · have hn : ¬ ∃ z c', c = z :: c' ∧ 1 ≤ z := fun h => by
          have := (isDA_head_iff c).2 h; rw [hd] at this; exact Bool.false_ne_true this
        exact iff_of_false (by simp) hn
      · have := (isDA_head_iff c).1 hd; exact iff_of_true (by simp) this)
    (fun hb => by
      have hP1 : ∃ z c', c = z :: c' ∧ 1 ≤ z := by
        by_contra hn
        rw [Function.update_self] at hb
        simp only [hW4, hB4] at hb
        have hd : isDA ((encInts c).map ι1).head? = false := by
          cases h : isDA ((encInts c).map ι1).head?
          · rfl
          · exact absurd ((isDA_head_iff c).1 h) hn
        rw [hd] at hb; simp at hb
      obtain ⟨z, c', rfl, hz1⟩ := hP1
      have hWz := encInts_head_nonneg z (by omega) c'
      obtain ⟨t', m', hm', he', hres'⟩ := st3 _ z c' (N - 2) N (z :: c').length L
        (by simp [hS4, Function.update_apply, hWz]) (by simp [hS4, Function.update_apply])
        (by simp [hS4, Function.update_apply, hN]) (by simp [hS4, Function.update_apply, hc])
        (by simp [hS4, Function.update_apply, hX]) (by simp [hS4, Function.update_apply, hCn])
        (by simp [hS4, Function.update_apply, hNp]) (by simp [hS4, Function.update_apply, hY])
        (by simp [hS4, Function.update_apply, hsc]) (by simp [hS4, Function.update_apply, hQ])
        (by simp [hS4, Function.update_apply, hH]) (by simp [hS4, Function.update_apply, hP])
        hb (le_trans (bits_len_le z c') hcL) (by omega) (le_trans (tail_len_le z c') hcL) hNL hcl
        (by simpa [hS4, Function.update_apply] using hko)
      refine ⟨t', m', hm', he', res_iff hres' ⟨fun h z0 c0 e => ?_, fun h => h z c' rfl⟩⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj e
      exact h)
  refine ⟨t, m, by nlinarith, he, res_iff hres ⟨?_, ?_⟩⟩
  · rintro ⟨⟨z, c', rfl, h1⟩, h2⟩; exact ⟨z, c', rfl, h1, h2 z c' rfl⟩
  · rintro ⟨z, c', rfl, h1, h2⟩
    exact ⟨⟨z, c', rfl, h1⟩, fun z0 c0 e => by obtain ⟨rfl, rfl⟩ := List.cons.inj e; exact h2⟩

/-! ### stage 1: parity of `|d|`, `N = |d| / 2`, the integer part back in order -/

def step1 : SP := .seq (transferProg KS.kC (fun k => decide (k = KS.CC)))
  (.seq (halveProg KS.kd KS.N KS.Pp mkA) (flagProg (fun h => (h KS.Pp).isSome)))
def prog1 : SP := guard step1 prog2

lemma st1 (s : KS → List A) (c : List ℤ) (d : List ℕ) (L : ℕ)
    (hkC : s KS.kC = ((encInts c).map ι1).reverse) (hkd : s KS.kd = List.replicate d.length mkA)
    (hc : s KS.kc = List.replicate c.length mkA) (hCC : s KS.CC = []) (hN : s KS.N = [])
    (hPp : s KS.Pp = []) (hN2 : s KS.N2 = []) (hW : s KS.W = []) (hX : s KS.Xs = [])
    (hCn : s KS.Cn = []) (hNp : s KS.Np = []) (hY : s KS.Y = []) (hsc : s KS.sc = [])
    (hQ : s KS.Q = []) (hH : s KS.H = []) (hP : s KS.P = []) (hB : s KS.Bd = [])
    (hcL : (encInts c).length ≤ L) (hcl : c.length ≤ L) (hdl : d.length ≤ L)
    (hko : (s KS.ko).length ≤ L) :
    ∃ t m, m ≤ 220 * (L + 1) ^ 2 ∧ prog1.Exec s t m ∧ Res s t (GlenSteps c d) := by
  obtain ⟨n1, hn1, e1⟩ := exec_transfer KS.kC (fun k => decide (k = KS.CC)) _ s rfl
  have e1' := exec_congr e1 (t' := Function.update (Function.update s KS.kC []) KS.CC
      ((encInts c).map ι1))
    (by funext k; cases k <;> simp [transferStore, Function.update_apply, hkC, hCC])
  have hn1' : n1 ≤ 3 * L + 1 := by
    have h := hn1; simp [hkC] at h; omega
  have e2 := exec_halve KS.kd KS.N KS.Pp (by decide) (by decide) (by decide) mkA d.length 0
    (Function.update (Function.update s KS.kC []) KS.CC ((encInts c).map ι1))
    (by simp [Function.update_apply, hkd]) (by norm_num) (by simp [Function.update_apply, hPp])
  set S2 := Function.update (Function.update (Function.update (Function.update
    (Function.update s KS.kC []) KS.CC ((encInts c).map ι1)) KS.kd []) KS.Pp
    (List.replicate (d.length % 2) mkA)) KS.N (List.replicate (d.length / 2) mkA) with hS2
  have e2' := exec_congr e2 (t' := S2)
    (by funext k; cases k <;> simp [hS2, Function.update_apply, hN])
  have e3 := exec_flag (fun h => (h KS.Pp).isSome) S2
  have hP2 : S2 KS.Pp = List.replicate (d.length % 2) mkA := by simp [hS2, Function.update_apply]
  have hB2 : S2 KS.Bd = [] := by simp [hS2, Function.update_apply, hB]
  obtain ⟨t, m, hm, he, hres⟩ := exec_guard _ prog2 s _ _ (200 * (L + 1) ^ 2) (d.length % 2 = 0)
    (∃ z c', c = z :: c' ∧ 1 ≤ z ∧ z.natAbs = d.length / 2 - 2 ∧
      ((∀ z' c'', c' = z' :: c'' → 0 ≤ z') ∧ (Xv (d.length / 2) ≤ c.length ∧
        (c.length - Xv (d.length / 2)) % (d.length / 2 + 2) = 0 ∧
        (c'.getD 0 0).natAbs = (c.length - Xv (d.length / 2)) / (d.length / 2 + 2))))
    (StackProg.Exec.seq e1' (StackProg.Exec.seq e2' e3))
    (by simp [hS2, Function.update_apply])
    (by rw [Function.update_self]; simp only [hP2, hB2]; rw [flag_rep]; simp)
    (fun hb => st2 _ c (d.length / 2) L (by simp [hS2, Function.update_apply])
      (by simp [hS2, Function.update_apply]) (by simp [hS2, Function.update_apply, hN2])
      (by simp [hS2, Function.update_apply, hW]) (by simp [hS2, Function.update_apply, hc])
      (by simp [hS2, Function.update_apply, hX]) (by simp [hS2, Function.update_apply, hCn])
      (by simp [hS2, Function.update_apply, hNp]) (by simp [hS2, Function.update_apply, hY])
      (by simp [hS2, Function.update_apply, hsc]) (by simp [hS2, Function.update_apply, hQ])
      (by simp [hS2, Function.update_apply, hH]) (by simp [hS2, Function.update_apply, hP])
      hb hcL (by omega) hcl (by simpa [hS2, Function.update_apply] using hko))
  exact ⟨t, m, by nlinarith, he, hres⟩

/-! ### the whole program -/

def mainProg : SP := .seq (copyProg KS.ki KS.ko KS.sc)
  (.seq (scanProg KS.ki KS.st δA (outA KS.kc KS.kd KS.kC KS.kD))
    (.branch (fun h => decide (h KS.st = some (dsA DS.T0))) prog1 (clearProg KS.ko)))

lemma map_ι1_inj {l l' : List BSym} (h : l.map ι1 = l'.map ι1) : l = l' := by
  refine List.map_injective_iff.mpr ?_ h
  intro a b hab; simpa [ι1] using hab

theorem main (u : List A) : ∃ t n, n ≤ 230 * (u.length + 1) ^ 2 ∧
    mainProg.Exec (fun j => if j = KS.ki then u else []) t n ∧
    ((∃ c d, u = Ew c d ∧ Glen c d) → t KS.ko = u) ∧
    (¬(∃ c d, u = Ew c d ∧ Glen c d) → t KS.ko = []) := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy KS.ki KS.ko KS.sc (by decide) (by decide) (by decide)
    (fun j => if j = KS.ki then u else []) (by simp)
  have hn1' : n1 ≤ 6 * u.length + 3 := by simpa using hn1
  have e1' := exec_congr e1 (t' := fun j => if j = KS.ki ∨ j = KS.ko then u else [])
    (by funext k; cases k <;> simp [Function.update_apply])
  set s1 : KS → List A := fun j => if j = KS.ki ∨ j = KS.ko then u else [] with hs1
  obtain ⟨e2, hiff, hcont, hoth⟩ := scanA_result KS.ki KS.st KS.kc KS.kd KS.kC KS.kD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) u s1 (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
    (by simp [hs1]) (by simp [hs1])
  set s2 := scanRun KS.ki KS.st δA (outA KS.kc KS.kd KS.kC KS.kD) u s1 with hs2
  have hko2 : s2 KS.ko = u := by
    rw [hoth KS.ko (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [hs1]
  have hemp : ∀ k, k ≠ KS.ki → k ≠ KS.st → k ≠ KS.kc → k ≠ KS.kd → k ≠ KS.kC → k ≠ KS.kD →
      k ≠ KS.ko → s2 k = [] := by
    intro k h0 h1 h2 h3 h4 h5 h6
    rw [hoth k h0 h1 h2 h3 h4 h5]; simp [hs1, h0, h6]
  by_cases hsh : ∃ c d, u = Ew c d
  · obtain ⟨c, d, hu⟩ := hsh
    obtain ⟨hkc, hkd, hkC, -⟩ := hcont c d hu
    have hlen : (encInts c).length + 1 + (encNats d).length = u.length := by
      rw [hu]; simp [Ew]; omega
    have hc1 := len_encInts c
    have hd1 := len_encNats d
    have hst : decide ((s2 KS.st).head? = some (dsA DS.T0)) = true :=
      decide_eq_true (hiff.2 ⟨c, d, hu⟩)
    obtain ⟨t, m, hm, he, hres⟩ := st1 s2 c d u.length hkC hkd hkc
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by omega) (by omega) (by omega) (by rw [hko2])
    have key : (∃ c0 d0, u = Ew c0 d0 ∧ Glen c0 d0) ↔ GlenSteps c d := by
      constructor
      · rintro ⟨c0, d0, hu0, hg0⟩
        obtain ⟨-, hkd0, hkC0, -⟩ := hcont c0 d0 hu0
        have hcc : c0 = c :=
          encInts_inj _ _ (map_ι1_inj (List.reverse_inj.1 (hkC0.symm.trans hkC)))
        have hdd : d0.length = d.length := by
          have := congrArg List.length (hkd0.symm.trans hkd); simpa using this
        subst hcc
        rw [← glen_iff]; unfold Glen at hg0 ⊢; rw [← hdd]; exact hg0
      · intro h; exact ⟨c, d, hu, (glen_iff c d).2 h⟩
    refine ⟨t, n1 + 1 + (3 * u.length + 1 + 1 + (1 + m)), by nlinarith,
      StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchTrue hst he)), ?_, ?_⟩
    · intro h; rw [hres.1 (key.1 h), hko2]
    · intro h; exact hres.2 (fun hg => h (key.2 hg))
  · have hst : decide ((s2 KS.st).head? = some (dsA DS.T0)) = false :=
      decide_eq_false (fun h => hsh (hiff.1 h))
    obtain ⟨m, hm, he⟩ := exec_clear KS.ko s2
    refine ⟨_, n1 + 1 + (3 * u.length + 1 + 1 + (1 + m)), by rw [hko2] at hm; nlinarith,
      StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchFalse hst he)), ?_, ?_⟩
    · rintro ⟨c, d, hu, -⟩; exact absurd ⟨c, d, hu⟩ hsh
    · intro _; simp

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

/-- E_len: the layout filter is computed by a polynomial-time stack program. -/
theorem E_len : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
          c.length = 2 + ((c.getD 0 0).toNat + 2) +
            2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
            ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat +
            (c.getD 1 0).toNat ∧
          d.length = 2 * ((c.getD 0 0).toNat + 2)) → s ko = u) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
          c.length = 2 + ((c.getD 0 0).toNat + 2) +
            2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
            ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat +
            (c.getD 1 0).toNat ∧
          d.length = 2 * ((c.getD 0 0).toNat + 2)) → s ko = []) := by
  obtain ⟨K, hK⟩ := poly_gen 230 2
  refine ⟨KS, inferInstance, inferInstance, mainProg, KS.ki, KS.ko, K, fun u => ?_⟩
  obtain ⟨t, n, hn, he, h1, h2⟩ := main u
  exact ⟨t, n, le_trans hn (hK _), he, h1, h2⟩

end D0bfE

theorem solution : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
          c.length = 2 + ((c.getD 0 0).toNat + 2) +
            2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
            ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat +
            (c.getD 1 0).toNat ∧
          d.length = 2 * ((c.getD 0 0).toNat + 2)) → s ko = u) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
          c.length = 2 + ((c.getD 0 0).toNat + 2) +
            2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
            ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat +
            (c.getD 1 0).toNat ∧
          d.length = 2 * ((c.getD 0 0).toNat + 2)) → s ko = []) := by
  exact D0bfE.E_len
