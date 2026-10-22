-- Prove2me | solution 1 for ProjSchedTW.Complexity.cumCheck_time_filter_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:42:30.527267+00:00
-- url     : https://prove2.me/submissions/0254a80c-f88d-442a-bfc6-84f0b77a2729

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
        · intro h; have := he h; cases x <;> cases y <;> simp_all [dg]
        · intro h; rw [h]
      have h1S : s1 St = (if a = b then [] else [stSym b]) ++ s St := by
        simp only [hs1, StackProg.applyAct, cmpAct, hX, hY, List.map_cons, List.cons_append,
          List.head?_cons, Option.some.injEq, Function.comp_apply, hXS.symm, hYS.symm, or_self,
          if_false, if_true]
        by_cases hab : a = b
        · subst hab; simp [StackAct.apply]
        · have hne : ¬ e (dg a) = e (dg b) := fun h => hab ((hdg a b).1 h)
          rw [if_neg hne]
          cases a <;> cases b <;> simp_all [StackAct.apply, dg, stSym]
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

/-! ## E_time stack program (namespace D0bfB) -/

namespace D0bfB
open D0bfL D0bfT D0bfS


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

lemma dd_head (d : List ℕ) : digA (toksE ι2 (d.map tokN)).head? = !decide (d.getD 0 0 = 0) := by
  cases d with
  | nil => rw [List.map_nil, toksE_nil]; rfl
  | cons a d =>
    rw [List.map_cons, toksE_cons]
    have hg : (a :: d).getD 0 0 = a := rfl
    rw [hg]
    by_cases ha : a = 0
    · subst ha; rfl
    · obtain ⟨b, l, hbl⟩ : ∃ b l, Nat.bits a = b :: l := by
        cases h : Nat.bits a with
        | nil => exact absurd (show a = 0 by rw [← bval_bits a, h]; rfl) ha
        | cons b l => exact ⟨b, l, rfl⟩
      simp only [tokN, hbl, List.map_cons, List.cons_append, List.head?_cons, ha, decide_false,
        Bool.not_false]
      cases b <;> rfl

/-! ### keys -/

inductive KA
  | ki | ko | sc | st | kc | kd | kC | kD | DD | N | Pp | W | Cx | Cy | Ic | I | Jc | J | F | X | Y
  | St | Bd | E | C1 | C2
  deriving DecidableEq

instance : Fintype KA := Fintype.ofList
  [KA.ki, KA.ko, KA.sc, KA.st, KA.kc, KA.kd, KA.kC, KA.kD, KA.DD, KA.N, KA.Pp, KA.W, KA.Cx, KA.Cy,
    KA.Ic, KA.I, KA.Jc, KA.J, KA.F, KA.X, KA.Y, KA.St, KA.Bd, KA.E, KA.C1, KA.C2]
  (by intro x; cases x <;> simp)

abbrev SP := StackProg KA A

lemma exec_congr {p : SP} {s t t' : KA → List A} {n : ℕ} (h : p.Exec s t n) (e : t = t') :
    p.Exec s t' n := e ▸ h

/-! ### the sum-compare branch: `d_i + δ` against `d_j` (or `d_i` against `d_j + |δ|`) -/

def sumBr : SP := .branch (fun h => decide (h KA.W = some (ι1 .minus)))
  (.seq (popProg KA.W) (sumLoop KA.X KA.E KA.Y KA.W KA.C1 KA.C2 KA.St mkA))
  (sumLoop KA.X KA.W KA.Y KA.E KA.C1 KA.C2 KA.St mkA)

set_option maxHeartbeats 4000000 in
lemma exec_sumBr (s : KA → List A) (cl : List ℤ) (q a b L : ℕ) (RX RY : List A)
    (hX : s KA.X = (Nat.bits a).map (ι2 ∘ dg) ++ ι2 .sep :: RX)
    (hY : s KA.Y = (Nat.bits b).map (ι2 ∘ dg) ++ ι2 .sep :: RY)
    (hW : s KA.W = toksE ι1 ((cl.map digU).drop q)) (hE : s KA.E = [])
    (hC1 : s KA.C1 = []) (hC2 : s KA.C2 = []) (hSt : s KA.St = [])
    (ha : (Nat.bits a).length ≤ L) (hb : (Nat.bits b).length ≤ L)
    (hLw : (toksE ι1 ((cl.map digU).drop q)).length ≤ L) :
    ∃ P t, t ≤ 3 * L + 10 ∧ P.length ≤ L + 1 ∧
      sumBr.Exec s (Function.update (Function.update (Function.update (Function.update s
        KA.W (Rw cl q)) KA.X (ι2 .sep :: RX)) KA.Y (ι2 .sep :: RY)) KA.St P) t ∧
      (P.head? = some (stSym false) ↔ ¬(cl.getD q 0 ≤ (b : ℤ) - a)) := by
  obtain ⟨z, hz⟩ : ∃ z, cl.getD q 0 = z := ⟨_, rfl⟩
  have hWs := W_split cl q
  rw [hz, digU_map] at hWs
  have hlz : (Nat.bits z.natAbs).length ≤ L := by
    have h := hLw
    rw [hWs] at h
    simp only [List.length_append, List.length_map] at h
    omega
  have hW' : s KA.W = (if z < 0 then [ι1 .minus] else []) ++
      ((Nat.bits z.natAbs).map (ι1 ∘ dg) ++ Rw cl q) := by
    rw [hW, hWs, List.append_assoc]
  have hdig := Rw_dig cl q
  rw [hz]
  by_cases hneg : z < 0
  · rw [if_pos hneg, List.singleton_append] at hW'
    have e1 := exec_pop KA.W s
    set s1 := Function.update s KA.W (s KA.W).tail with hs1
    obtain ⟨P, t, ht, hP, e2, hhd⟩ := exec_sum KA.X KA.E KA.Y KA.W KA.C1 KA.C2 KA.St
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      mkA (ι2 .sep :: RX) [] (ι2 .sep :: RY) (Rw cl q) digA_sep2 digA_none digA_sep2 hdig
      (L + 1) ((Nat.bits a).map (ι2 ∘ dg)) [] ((Nat.bits b).map (ι2 ∘ dg))
      ((Nat.bits z.natAbs).map (ι1 ∘ dg)) false false s1 (digs2 a) (by simp) (digs2 b) (digs1 _)
      (by simp [hs1, hX]) (by simp [hs1, hE]) (by simp [hs1, hY]) (by simp [hs1, hW'])
      (by simp [hs1, hC1, cst]) (by simp [hs1, hC2, cst])
      (Or.inl (Nat.add_le_add_right (max_le (max_le (by simpa using ha) (Nat.zero_le _))
        (max_le (by simpa using hb) (by simpa using hlz))) 1))
    have hs1St : s1 KA.St = [] := by simp [hs1, hSt]
    rw [hs1St, List.append_nil, dval_bits2, dval_bits2, dval_bits1, dval_nil] at hhd
    simp only [Bool.toNat_false, add_zero, zero_add, List.head?_nil] at hhd
    refine ⟨P, _, ?_, hP, exec_congr (StackProg.Exec.branchTrue ?_ (StackProg.Exec.seq e1 e2)) ?_, ?_⟩
    · omega
    · show decide ((s KA.W).head? = some (ι1 .minus)) = true
      rw [hW']; simp
    · funext k
      cases k <;> simp [hs1, Function.update_apply, hE, hC1, hC2, hSt]
    · rw [hhd, scRes_false]
      rcases Int.natAbs_eq z with h | h <;> omega
  · rw [if_neg hneg, List.nil_append] at hW'
    obtain ⟨P, t, ht, hP, e2, hhd⟩ := exec_sum KA.X KA.W KA.Y KA.E KA.C1 KA.C2 KA.St
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      mkA (ι2 .sep :: RX) (Rw cl q) (ι2 .sep :: RY) [] digA_sep2 hdig digA_sep2 digA_none
      (L + 1) ((Nat.bits a).map (ι2 ∘ dg)) ((Nat.bits z.natAbs).map (ι1 ∘ dg))
      ((Nat.bits b).map (ι2 ∘ dg)) [] false false s (digs2 a) (digs1 _) (digs2 b) (by simp)
      (by simp [hX]) (by simp [hW']) (by simp [hY]) (by simp [hE])
      (by simp [hC1, cst]) (by simp [hC2, cst])
      (Or.inl (Nat.add_le_add_right (max_le (max_le (by simpa using ha) (by simpa using hlz))
        (max_le (by simpa using hb) (Nat.zero_le _))) 1))
    rw [hSt, List.append_nil, dval_bits2, dval_bits2, dval_bits1, dval_nil] at hhd
    simp only [Bool.toNat_false, add_zero, zero_add, List.head?_nil] at hhd
    refine ⟨P, _, ?_, hP, exec_congr (StackProg.Exec.branchFalse ?_ e2) ?_, ?_⟩
    · omega
    · show decide ((s KA.W).head? = some (ι1 .minus)) = false
      rw [hW']; exact decide_eq_false (head_nonminus _ cl q)
    · funext k
      cases k <;> simp [Function.update_apply, hE, hC1, hC2, hSt]
    · rw [hhd, scRes_false]
      rcases Int.natAbs_eq z with h | h <;> omega

/-! ### the time block: flag `Bd` unless `δ ≤ d_j - d_i` (δ the token at `q`) -/

def timeBlock : SP :=
  .seq (copyProg KA.DD KA.X KA.sc) (.seq (copyProg KA.DD KA.Y KA.sc)
  (.seq (copyProg KA.I KA.Cx KA.sc) (.seq (skipToks KA.Cx KA.X ι2)
  (.seq (copyProg KA.J KA.Cy KA.sc) (.seq (skipToks KA.Cy KA.Y ι2)
  (.seq sumBr
  (.seq (flagP KA.Bd (fun h => decide (h KA.St = some (stSym false))))
  (.seq (popProg KA.W)
  (.seq (clearProg KA.X) (.seq (clearProg KA.Y) (clearProg KA.St)))))))))))

set_option maxHeartbeats 4000000 in
lemma exec_timeBlock (s : KA → List A) (cl : List ℤ) (d : List ℕ) (q i j L : ℕ)
    (hW : s KA.W = toksE ι1 ((cl.map digU).drop q))
    (hDD : s KA.DD = toksE ι2 (d.map tokN))
    (hI : s KA.I = List.replicate i mkA) (hJ : s KA.J = List.replicate j mkA)
    (hX : s KA.X = []) (hY : s KA.Y = []) (hCx : s KA.Cx = []) (hCy : s KA.Cy = [])
    (hSt : s KA.St = []) (hsc : s KA.sc = []) (hE : s KA.E = []) (hC1 : s KA.C1 = [])
    (hC2 : s KA.C2 = [])
    (hi : i < d.length) (hj : j < d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hijL : i + j ≤ L) :
    ∃ m ≤ 100 * (L + 1), timeBlock.Exec s (Function.update (Function.update s KA.W
      (toksE ι1 ((cl.map digU).drop (q + 1))))
      KA.Bd (if cl.getD q 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0 then s KA.Bd else mkA :: s KA.Bd)) m := by
  have hts : ∀ t ∈ d.map tokN, BSym.sep ∉ t := by
    simp only [List.mem_map]; rintro t ⟨a, -, rfl⟩; exact tokN_no_sep a
  obtain ⟨m1, hm1, e1⟩ := exec_copy KA.DD KA.X KA.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s KA.X (s KA.DD ++ s KA.X) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_copy KA.DD KA.Y KA.sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 KA.Y (s1 KA.DD ++ s1 KA.Y) with hs2
  obtain ⟨m3, hm3, e3⟩ := exec_copy KA.I KA.Cx KA.sc (by decide) (by decide) (by decide) s2
    (by simp [hs1, hs2, hsc])
  set s3 := Function.update s2 KA.Cx (s2 KA.I ++ s2 KA.Cx) with hs3
  obtain ⟨m4, hm4, e4⟩ := exec_skipToks KA.Cx KA.X (by decide) ι2 ι2_inj mkA [] i
    (d.map tokN) s3 hts (by simp; omega) (by simp [hs1, hs2, hs3, hI, hCx])
    (by simp [hs1, hs2, hs3, hDD, hX])
  set s4 := Function.update (Function.update s3 KA.Cx []) KA.X
    (toksE ι2 ((d.map tokN).drop i) ++ []) with hs4
  obtain ⟨m5, hm5, e5⟩ := exec_copy KA.J KA.Cy KA.sc (by decide) (by decide) (by decide) s4
    (by simp [hs1, hs2, hs3, hs4, hsc])
  set s5 := Function.update s4 KA.Cy (s4 KA.J ++ s4 KA.Cy) with hs5
  obtain ⟨m6, hm6, e6⟩ := exec_skipToks KA.Cy KA.Y (by decide) ι2 ι2_inj mkA [] j
    (d.map tokN) s5 hts (by simp; omega) (by simp [hs1, hs2, hs3, hs4, hs5, hJ, hCy])
    (by simp [hs1, hs2, hs3, hs4, hs5, hDD, hY])
  set s6 := Function.update (Function.update s5 KA.Cy []) KA.Y
    (toksE ι2 ((d.map tokN).drop j) ++ []) with hs6
  have hdx := dropTok d i hi
  have hdy := dropTok d j hj
  have h1x := toksE_len_drop ι2 (d.map tokN) (i + 1)
  have h1y := toksE_len_drop ι2 (d.map tokN) (j + 1)
  have hbx := bits_len_le_toks d i hi
  have hby := bits_len_le_toks d j hj
  have h6X : s6 KA.X = (Nat.bits (d.getD i 0)).map (ι2 ∘ dg) ++
      ι2 .sep :: toksE ι2 ((d.map tokN).drop (i + 1)) := by
    rw [← hdx]; simp [hs6, hs5, hs4]
  have h6Y : s6 KA.Y = (Nat.bits (d.getD j 0)).map (ι2 ∘ dg) ++
      ι2 .sep :: toksE ι2 ((d.map tokN).drop (j + 1)) := by
    rw [← hdy]; simp [hs6]
  have hLw : (toksE ι1 ((cl.map digU).drop q)).length ≤ L := le_trans (toksE_len_drop ι1 _ q) hLc
  obtain ⟨P, t7, ht7, hP, e7, hPh⟩ := exec_sumBr s6 cl q (d.getD i 0) (d.getD j 0) L _ _ h6X h6Y
    (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hW]) (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hE])
    (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hC1]) (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hC2])
    (by simp [hs1, hs2, hs3, hs4, hs5, hs6, hSt]) (le_trans hbx hL) (le_trans hby hL) hLw
  set s7 := Function.update (Function.update (Function.update (Function.update s6 KA.W (Rw cl q))
    KA.X (ι2 .sep :: toksE ι2 ((d.map tokN).drop (i + 1))))
    KA.Y (ι2 .sep :: toksE ι2 ((d.map tokN).drop (j + 1)))) KA.St P with hs7
  have hs7St : s7 KA.St = P := by simp [hs7]
  have hs7Bd : s7 KA.Bd = s KA.Bd := by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  have e8 := exec_congr (exec_flagP KA.Bd (fun h => decide (h KA.St = some (stSym false))) s7)
    (t' := Function.update s7 KA.Bd
      (if cl.getD q 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0 then s KA.Bd else mkA :: s KA.Bd)) (by
      congr 1
      show (if decide ((s7 KA.St).head? = some (stSym false)) = true then mkA :: s7 KA.Bd
        else s7 KA.Bd) = _
      rw [hs7St, hs7Bd]
      by_cases hc : cl.getD q 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0
      · rw [if_pos hc, if_neg (fun h => (hPh.1 (of_decide_eq_true h)) hc)]
      · rw [if_neg hc, if_pos (decide_eq_true (hPh.2 hc))])
  set s8 := Function.update s7 KA.Bd
      (if cl.getD q 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0 then s KA.Bd else mkA :: s KA.Bd) with hs8
  have e9 := exec_pop KA.W s8
  set s9 := Function.update s8 KA.W (s8 KA.W).tail with hs9
  obtain ⟨m10, hm10, e10⟩ := exec_clearG KA.X s9
  obtain ⟨m11, hm11, e11⟩ := exec_clearG KA.Y (Function.update s9 KA.X [])
  obtain ⟨m12, hm12, e12⟩ := exec_clearG KA.St
    (Function.update (Function.update s9 KA.X []) KA.Y [])
  have hX9 : (s9 KA.X).length = (toksE ι2 ((d.map tokN).drop (i + 1))).length + 1 := by
    simp [hs9, hs8, hs7]
  have hY9 : ((Function.update s9 KA.X []) KA.Y).length =
      (toksE ι2 ((d.map tokN).drop (j + 1))).length + 1 := by
    simp [hs9, hs8, hs7]
  have hSt9 : ((Function.update (Function.update s9 KA.X []) KA.Y []) KA.St).length = P.length := by
    simp [hs9, hs8, hs7]
  rw [hX9] at hm10
  rw [hY9] at hm11
  rw [hSt9] at hm12
  have hm1' : m1 ≤ 6 * L + 3 := by rw [hDD] at hm1; omega
  have hm2' : m2 ≤ 6 * L + 3 := by
    have : (s1 KA.DD).length = (toksE ι2 (d.map tokN)).length := by simp [hs1, hDD]
    omega
  have hm3' : m3 ≤ 6 * i + 3 := by
    have : (s2 KA.I).length = i := by simp [hs1, hs2, hI]
    omega
  have hm4' : m4 ≤ 7 * L + 1 := by
    have : (s3 KA.X).length = (toksE ι2 (d.map tokN)).length := by simp [hs1, hs2, hs3, hDD, hX]
    omega
  have hm5' : m5 ≤ 6 * j + 3 := by
    have : (s4 KA.J).length = j := by simp [hs1, hs2, hs3, hs4, hJ]
    omega
  have hm6' : m6 ≤ 7 * L + 1 := by
    have : (s5 KA.Y).length = (toksE ι2 (d.map tokN)).length := by
      simp [hs1, hs2, hs3, hs4, hs5, hDD, hY]
    omega
  refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
    (StackProg.Exec.seq e8 (StackProg.Exec.seq e9 (StackProg.Exec.seq e10
    (StackProg.Exec.seq e11 (exec_congr e12 ?_)))))))))))⟩
  · omega
  · funext k
    cases k <;> simp [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, Function.update_apply, hX, hY,
      hCx, hCy, hSt, Rw_tail]

/-! ### the inner round: read the arc flag of `(i, j)`, check `δ_ij ≤ d_j - d_i` if set -/

def innerBody : SP :=
  .seq (popProg KA.Jc) (.seq (readFlag KA.W KA.F)
    (.seq (.branch (fun h => (h KA.F).isSome) (.seq (popProg KA.F) timeBlock) (skipOne KA.W ι1))
      (pushProg KA.J mkA)))

set_option maxHeartbeats 2000000 in
lemma exec_innerBody (s : KA → List A) (cl : List ℤ) (d : List ℕ) (n i j p L : ℕ)
    (hW : s KA.W = toksE ι1 ((cl.map digU).drop p)) (hF : s KA.F = [])
    (hDD : s KA.DD = toksE ι2 (d.map tokN))
    (hI : s KA.I = List.replicate i mkA) (hJ : s KA.J = List.replicate j mkA)
    (hX : s KA.X = []) (hY : s KA.Y = []) (hCx : s KA.Cx = []) (hCy : s KA.Cy = [])
    (hSt : s KA.St = []) (hsc : s KA.sc = []) (hE : s KA.E = []) (hC1 : s KA.C1 = [])
    (hC2 : s KA.C2 = [])
    (hi : i < n) (hj : j < n) (hd : n + n ≤ d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hnL : 3 * n ≤ L) :
    ∃ m ≤ 120 * (L + 2), innerBody.Exec s
      (Function.update (Function.update (Function.update (Function.update s KA.Jc (s KA.Jc).tail)
        KA.W (toksE ι1 ((cl.map digU).drop (p + 2))))
        KA.Bd (if (cl.getD p 0 = 1 → cl.getD (p + 1) 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0) then s KA.Bd
          else mkA :: s KA.Bd))
        KA.J (mkA :: s KA.J)) m := by
  have e1 := exec_pop KA.Jc s
  set s1 := Function.update s KA.Jc (s KA.Jc).tail with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_readFlag KA.W KA.F (by decide) ((cl.map digU).drop p) s1
    (digU_toks_nosep cl p) (by simp [hs1, hW]) (by simp [hs1, hF])
  simp only [headFlag, List.tail_drop] at e2
  set s2 := Function.update (Function.update s1 KA.W (toksE ι1 ((cl.map digU).drop (p + 1))))
    KA.F (if cl.getD p 0 = 1 then [mkA] else []) with hs2
  have hl1 := toksE_len_drop ι1 (cl.map digU) p
  simp [hs1, hW] at hm2
  have hF2 : s2 KA.F = (if cl.getD p 0 = 1 then [mkA] else []) := by simp [hs2]
  by_cases hf : cl.getD p 0 = 1
  · rw [if_pos hf] at hF2
    have hf' := hf
    rw [List.getD_eq_getElem?_getD] at hf'
    have e4 := exec_pop KA.F s2
    set s4 := Function.update s2 KA.F (s2 KA.F).tail with hs4
    obtain ⟨m5, hm5, e5⟩ := exec_timeBlock s4 cl d (p + 1) i j L
      (by simp [hs1, hs2, hs4]) (by simp [hs1, hs2, hs4, hDD])
      (by simp [hs1, hs2, hs4, hI]) (by simp [hs1, hs2, hs4, hJ])
      (by simp [hs1, hs2, hs4, hX]) (by simp [hs1, hs2, hs4, hY])
      (by simp [hs1, hs2, hs4, hCx]) (by simp [hs1, hs2, hs4, hCy])
      (by simp [hs1, hs2, hs4, hSt]) (by simp [hs1, hs2, hs4, hsc])
      (by simp [hs1, hs2, hs4, hE]) (by simp [hs1, hs2, hs4, hC1])
      (by simp [hs1, hs2, hs4, hC2])
      (by omega) (by omega) hLc hL (by omega)
    have e6 := exec_pushG KA.J mkA (Function.update (Function.update s4 KA.W
      (toksE ι1 ((cl.map digU).drop (p + 1 + 1))))
      KA.Bd (if cl.getD (p + 1) 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0 then s4 KA.Bd
        else mkA :: s4 KA.Bd))
    refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.seq (StackProg.Exec.branchTrue (by simp [hF2])
        (StackProg.Exec.seq e4 e5)) (exec_congr e6 ?_)))⟩
    · omega
    · funext k
      cases k <;> simp [hs1, hs2, hs4, Function.update_apply, hf', hF]
  · rw [if_neg hf] at hF2
    have hf' := hf
    rw [List.getD_eq_getElem?_getD] at hf'
    obtain ⟨m3, hm3, e3⟩ := exec_skipOne' KA.W ι1 ι1_inj ((cl.map digU).drop (p + 1)) s2
      (digU_toks_nosep cl (p + 1)) (by simp [hs2])
    simp only [List.tail_drop] at e3
    have hl2 := toksE_len_drop ι1 (cl.map digU) (p + 1)
    simp [hs2] at hm3
    have e6 := exec_pushG KA.J mkA (Function.update s2 KA.W
      (toksE ι1 ((cl.map digU).drop (p + 1 + 1))))
    refine ⟨_, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2
      (StackProg.Exec.seq (StackProg.Exec.branchFalse (by simp [hF2]) e3)
        (exec_congr e6 ?_)))⟩
    · omega
    · funext k
      cases k <;> simp [hs1, hs2, Function.update_apply, hf', hF]

/-! ### the inner loop over `j` -/

def innerLoop : SP := .loop (fun h => (h KA.Jc).isSome) innerBody

set_option maxHeartbeats 2000000 in
lemma exec_innerLoop (s0 : KA → List A) (cl : List ℤ) (d : List ℕ) (n i p0 L : ℕ)
    (hW : s0 KA.W = toksE ι1 ((cl.map digU).drop p0)) (hF : s0 KA.F = [])
    (hJc : s0 KA.Jc = List.replicate n mkA) (hJ : s0 KA.J = [])
    (hDD : s0 KA.DD = toksE ι2 (d.map tokN))
    (hI : s0 KA.I = List.replicate i mkA)
    (hX : s0 KA.X = []) (hY : s0 KA.Y = []) (hCx : s0 KA.Cx = []) (hCy : s0 KA.Cy = [])
    (hSt : s0 KA.St = []) (hsc : s0 KA.sc = []) (hE : s0 KA.E = []) (hC1 : s0 KA.C1 = [])
    (hC2 : s0 KA.C2 = [])
    (hi : i < n) (hd : n + n ≤ d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hnL : 3 * n ≤ L) :
    ∃ s' m, m ≤ n * (120 * (L + 2) + 2) + 1 ∧ innerLoop.Exec s0 s' m ∧
      ∃ b, s' = Function.update (Function.update (Function.update (Function.update s0
        KA.Jc []) KA.W (toksE ι1 ((cl.map digU).drop (p0 + 2 * n)))) KA.J (List.replicate n mkA))
        KA.Bd b ∧
      (b = [] ↔ (s0 KA.Bd = [] ∧ ∀ j < n,
        (cl.getD (p0 + 2 * j) 0 = 1 →
          cl.getD (p0 + 2 * j + 1) 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0))) := by
  have key := exec_for KA.Jc innerBody mkA
    (fun t s => ∃ b, s = Function.update (Function.update (Function.update (Function.update s0
        KA.Jc (List.replicate (n - t) mkA)) KA.W (toksE ι1 ((cl.map digU).drop (p0 + 2 * t))))
        KA.J (List.replicate t mkA)) KA.Bd b ∧
      (b = [] ↔ (s0 KA.Bd = [] ∧ ∀ j < t,
        (cl.getD (p0 + 2 * j) 0 = 1 →
          cl.getD (p0 + 2 * j + 1) 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0))))
    n (120 * (L + 2)) ?_ s0 ⟨s0 KA.Bd, ?_, by simp⟩ hJc
  · obtain ⟨s', m, hm, he, b, hs', hb⟩ := key
    refine ⟨s', m, hm, he, b, ?_, hb⟩
    rw [hs']; simp
  · intro t ht s ⟨b, hs, hb⟩ _
    obtain ⟨m, hm, e⟩ := exec_innerBody s cl d n i t (p0 + 2 * t) L
      (by rw [hs]; simp) (by rw [hs]; simp [hF]) (by rw [hs]; simp [hDD])
      (by rw [hs]; simp [hI]) (by rw [hs]; simp)
      (by rw [hs]; simp [hX]) (by rw [hs]; simp [hY]) (by rw [hs]; simp [hCx])
      (by rw [hs]; simp [hCy]) (by rw [hs]; simp [hSt])
      (by rw [hs]; simp [hsc]) (by rw [hs]; simp [hE]) (by rw [hs]; simp [hC1])
      (by rw [hs]; simp [hC2]) hi ht hd hLc hL hnL
    refine ⟨_, m, hm, e, ⟨if (cl.getD (p0 + 2 * t) 0 = 1 →
        cl.getD (p0 + 2 * t + 1) 0 ≤ (d.getD t 0 : ℤ) - d.getD i 0)
      then b else mkA :: b, ?_, ?_⟩, ?_⟩
    · have hp : p0 + 2 * (t + 1) = p0 + 2 * t + 2 := by ring
      rw [hp]
      subst hs
      funext k
      cases k <;> simp [Function.update_apply, List.tail_replicate, Nat.sub_sub, List.replicate_succ]
    · constructor
      · intro h
        by_cases hok : (cl.getD (p0 + 2 * t) 0 = 1 →
            cl.getD (p0 + 2 * t + 1) 0 ≤ (d.getD t 0 : ℤ) - d.getD i 0)
        · rw [if_pos hok] at h
          obtain ⟨h1, h2⟩ := hb.1 h
          refine ⟨h1, fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact h2 j hj
          · exact hok
        · rw [if_neg hok] at h; simp at h
      · rintro ⟨h1, h2⟩
        rw [if_pos (h2 t (by omega))]
        exact hb.2 ⟨h1, fun j hj => h2 j (by omega)⟩
    · subst hs; simp [Function.update_apply, List.tail_replicate, Nat.sub_sub]
  · funext k; cases k <;> simp [Function.update_apply, hJc, hJ, hW]

/-! ### the outer loop over `i` -/

def outerBody : SP := .seq (popProg KA.Ic) (.seq (copyProg KA.N KA.Jc KA.sc)
  (.seq innerLoop (.seq (clearProg KA.J) (pushProg KA.I mkA))))

def outerLoop : SP := .loop (fun h => (h KA.Ic).isSome) outerBody

set_option maxHeartbeats 4000000 in
lemma exec_outerLoop (r0 : KA → List A) (cl : List ℤ) (d : List ℕ) (n q0 L : ℕ)
    (hW : r0 KA.W = toksE ι1 ((cl.map digU).drop q0)) (hF : r0 KA.F = [])
    (hIc : r0 KA.Ic = List.replicate n mkA) (hI : r0 KA.I = [])
    (hJc : r0 KA.Jc = []) (hJ : r0 KA.J = [])
    (hDD : r0 KA.DD = toksE ι2 (d.map tokN)) (hN : r0 KA.N = List.replicate n mkA)
    (hX : r0 KA.X = []) (hY : r0 KA.Y = []) (hCx : r0 KA.Cx = []) (hCy : r0 KA.Cy = [])
    (hSt : r0 KA.St = []) (hsc : r0 KA.sc = []) (hE : r0 KA.E = []) (hC1 : r0 KA.C1 = [])
    (hC2 : r0 KA.C2 = [])
    (hd : n + n ≤ d.length)
    (hLc : (toksE ι1 (cl.map digU)).length ≤ L) (hL : (toksE ι2 (d.map tokN)).length ≤ L)
    (hnL : 3 * n ≤ L) :
    ∃ s' m, m ≤ n * (n * (120 * (L + 2) + 2) + 9 * L + 22) + 1 ∧ outerLoop.Exec r0 s' m ∧
      ∃ b, s' = Function.update (Function.update (Function.update (Function.update r0
        KA.Ic []) KA.W (toksE ι1 ((cl.map digU).drop (q0 + 2 * n * n)))) KA.I
        (List.replicate n mkA)) KA.Bd b ∧
      (b = [] ↔ (r0 KA.Bd = [] ∧ ∀ i < n, ∀ j < n,
        (cl.getD (q0 + 2 * (i * n + j)) 0 = 1 →
          cl.getD (q0 + 2 * (i * n + j) + 1) 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0))) := by
  have key := exec_for KA.Ic outerBody mkA
    (fun t s => ∃ b, s = Function.update (Function.update (Function.update (Function.update r0
        KA.Ic (List.replicate (n - t) mkA)) KA.W (toksE ι1 ((cl.map digU).drop (q0 + 2 * n * t))))
        KA.I (List.replicate t mkA)) KA.Bd b ∧
      (b = [] ↔ (r0 KA.Bd = [] ∧ ∀ i < t, ∀ j < n,
        (cl.getD (q0 + 2 * (i * n + j)) 0 = 1 →
          cl.getD (q0 + 2 * (i * n + j) + 1) 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0))))
    n (n * (120 * (L + 2) + 2) + 9 * L + 20) ?_ r0 ⟨r0 KA.Bd, ?_, by simp⟩ hIc
  · obtain ⟨s', m, hm, he, b, hs', hb⟩ := key
    refine ⟨s', m, hm, he, b, ?_, hb⟩
    rw [hs']; simp
  · intro t ht s ⟨b, hs, hb⟩ _
    have e1 := exec_pop KA.Ic s
    set s1 := Function.update s KA.Ic (s KA.Ic).tail with hs1
    obtain ⟨m2, hm2, e2⟩ := exec_copy KA.N KA.Jc KA.sc (by decide) (by decide) (by decide) s1
      (by rw [hs1, hs]; simp [hsc])
    set s2 := Function.update s1 KA.Jc (s1 KA.N ++ s1 KA.Jc) with hs2
    obtain ⟨s3, m3, hm3, e3, b', hs3, hb'⟩ := exec_innerLoop s2 cl d n t (q0 + 2 * n * t) L
      (by rw [hs2, hs1, hs]; simp) (by rw [hs2, hs1, hs]; simp [hF])
      (by rw [hs2, hs1, hs]; simp [hN, hJc]) (by rw [hs2, hs1, hs]; simp [hJ])
      (by rw [hs2, hs1, hs]; simp [hDD])
      (by rw [hs2, hs1, hs]; simp) (by rw [hs2, hs1, hs]; simp [hX]) (by rw [hs2, hs1, hs]; simp [hY])
      (by rw [hs2, hs1, hs]; simp [hCx]) (by rw [hs2, hs1, hs]; simp [hCy])
      (by rw [hs2, hs1, hs]; simp [hSt]) (by rw [hs2, hs1, hs]; simp [hsc])
      (by rw [hs2, hs1, hs]; simp [hE]) (by rw [hs2, hs1, hs]; simp [hC1])
      (by rw [hs2, hs1, hs]; simp [hC2]) ht hd hLc hL hnL
    obtain ⟨m4, hm4, e4⟩ := exec_clearG KA.J s3
    have e5 := exec_pushG KA.I mkA (Function.update s3 KA.J [])
    have hm2' : m2 ≤ 6 * n + 3 := by
      have : s1 KA.N = List.replicate n mkA := by rw [hs1, hs]; simp [hN]
      rw [this] at hm2; simpa using hm2
    have hm4' : m4 ≤ 3 * n + 1 := by
      have : s3 KA.J = List.replicate n mkA := by rw [hs3]; simp
      rw [this] at hm4; simpa using hm4
    refine ⟨_, _, ?_, StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 e5))), ⟨b', ?_, ?_⟩, ?_⟩
    · have : n ≤ L := by omega
      omega
    · have hp : q0 + 2 * n * (t + 1) = q0 + 2 * n * t + 2 * n := by ring
      rw [hp, hs3, hs2, hs1, hs]
      funext k
      cases k <;> simp [Function.update_apply, List.tail_replicate, Nat.sub_sub, hJc, hJ,
        List.replicate_succ]
    · have hBd : s2 KA.Bd = b := by rw [hs2, hs1, hs]; simp
      rw [hBd] at hb'
      have hidx : ∀ j, q0 + 2 * n * t + 2 * j = q0 + 2 * (t * n + j) := by intro j; ring
      simp only [hidx] at hb'
      rw [hb']
      constructor
      · rintro ⟨h0, h1⟩
        obtain ⟨h2, h3⟩ := hb.1 h0
        refine ⟨h2, fun i hi j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h3 i hi j hj
        · exact h1 j hj
      · rintro ⟨h2, h3⟩
        exact ⟨hb.2 ⟨h2, fun i hi j hj => h3 i (by omega) j hj⟩, fun j hj => h3 t (by omega) j hj⟩
    · rw [hs3, hs2, hs1, hs]; simp [Function.update_apply, List.tail_replicate, Nat.sub_sub]
  · funext k; cases k <;> simp [Function.update_apply, hIc, hI, hW]

/-! ### skipping `k` tokens when fewer may be present -/

lemma exec_skipToks' (cnt W : KA) (hcW : cnt ≠ W) (e : BSym → A) (he : Function.Injective e)
    (k : ℕ) (ts : List (List BSym)) (s : KA → List A) (hts : ∀ t ∈ ts, BSym.sep ∉ t)
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

/-! ### phase B: set up `W`, `DD`, `N`, flag `d_0 ≠ 0`, run the double loop, clear `ko` on a
violation -/

def phaseB : SP :=
  .seq (transferProg KA.kC (fun k => decide (k = KA.W)))
  (.seq (transferProg KA.kD (fun k => decide (k = KA.DD)))
  (.seq (halveProg KA.kd KA.N KA.Pp mkA)
  (.seq (flagP KA.Bd (fun h => digA (h KA.DD)))
  (.seq (copyProg KA.N KA.Cx KA.sc) (.seq (pushProg KA.Cx mkA) (.seq (pushProg KA.Cx mkA)
  (.seq (skipToks KA.Cx KA.W ι1)
  (.seq (copyProg KA.N KA.Ic KA.sc)
  (.seq outerLoop (.branch (fun h => (h KA.Bd).isNone) skipP (clearProg KA.ko)))))))))))

/-- the temporal condition, indexed with `N := |d| / 2`: `S_0 = 0` and `δ_ij ≤ S_j - S_i` on
every arc. -/
def Gtm (cl : List ℤ) (d : List ℕ) : Prop := d.getD 0 0 = 0 ∧
  ∀ i < d.length / 2, ∀ j < d.length / 2,
    cl.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j)) 0 = 1 →
      cl.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j) + 1) 0 ≤
        (d.getD j 0 : ℤ) - d.getD i 0

lemma outer_bound (n M : ℕ) (hn : n ≤ M) :
    n * (n * (120 * (M + 2) + 2) + 9 * M + 22) + 1 ≤ 400 * ((M + 1) * (M + 1) * (M + 1)) := by
  have h2 : n * (n * (120 * (M + 2) + 2) + 9 * M + 22) ≤ M * (M * (120 * (M + 2) + 2) + 9 * M + 22) :=
    Nat.mul_le_mul hn (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _) _)
  have h3 : M * (M * (120 * (M + 2) + 2) + 9 * M + 22) + 1 ≤ 400 * ((M + 1) * (M + 1) * (M + 1)) := by
    nlinarith [Nat.zero_le (M * M * M), Nat.zero_le (M * M)]
  exact le_trans (Nat.add_le_add_right h2 1) h3

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

set_option maxHeartbeats 4000000 in
lemma exec_phaseB (s : KA → List A) (c : List ℤ) (d : List ℕ) (L : ℕ)
    (hkC : s KA.kC = ((encInts c).map ι1).reverse) (hkD : s KA.kD = ((encNats d).map ι2).reverse)
    (hkd : s KA.kd = List.replicate d.length mkA)
    (hW : s KA.W = []) (hDD : s KA.DD = []) (hN : s KA.N = []) (hPp : s KA.Pp = [])
    (hCx : s KA.Cx = []) (hCy : s KA.Cy = []) (hIc : s KA.Ic = []) (hI : s KA.I = [])
    (hJc : s KA.Jc = []) (hJ : s KA.J = []) (hF : s KA.F = []) (hX : s KA.X = [])
    (hY : s KA.Y = []) (hSt : s KA.St = []) (hsc : s KA.sc = []) (hBd : s KA.Bd = [])
    (hE : s KA.E = []) (hC1 : s KA.C1 = []) (hC2 : s KA.C2 = [])
    (hLc : (encInts c).length ≤ L) (hLd : (encNats d).length ≤ L) (hdl : d.length ≤ L)
    (hko : (s KA.ko).length ≤ L) :
    ∃ t m, m ≤ 1000 * ((3 * L + 4) * (3 * L + 4) * (3 * L + 4)) ∧ phaseB.Exec s t m ∧
      (Gtm c d → t KA.ko = s KA.ko) ∧ (¬Gtm c d → t KA.ko = []) := by
  set n := d.length / 2 with hn
  have hTC : (encInts c).map ι1 = toksE ι1 (c.map digU) := encInts_toks c
  have hTD : (encNats d).map ι2 = toksE ι2 (d.map tokN) := encNats_toks ι2 d
  have hlc : (toksE ι1 (c.map digU)).length ≤ L := by rw [← hTC]; simpa using hLc
  have hld : (toksE ι2 (d.map tokN)).length ≤ L := by rw [← hTD]; simpa using hLd
  -- transfers
  obtain ⟨m1, hm1, e1⟩ := exec_transfer KA.kC (fun k => decide (k = KA.W)) _ s rfl
  set s1 := Function.update (Function.update s KA.kC []) KA.W (toksE ι1 (c.map digU)) with hs1
  have e1' := exec_congr e1 (t' := s1)
    (by funext k; cases k <;> simp [hs1, transferStore, Function.update_apply, hkC, hW, hTC])
  obtain ⟨m2, hm2, e2⟩ := exec_transfer KA.kD (fun k => decide (k = KA.DD)) _ s1 rfl
  set s2 := Function.update (Function.update s1 KA.kD []) KA.DD (toksE ι2 (d.map tokN)) with hs2
  have e2' := exec_congr e2 (t' := s2)
    (by funext k; cases k <;> simp [hs1, hs2, transferStore, Function.update_apply, hkD, hDD, hTD])
  -- halve
  have e3 := exec_halve KA.kd KA.N KA.Pp (by decide) (by decide) (by decide) mkA d.length 0 s2
    (by simp [hs1, hs2, hkd]) (by norm_num) (by simp [hs1, hs2, hPp])
  set s3 := Function.update (Function.update (Function.update s2 KA.kd []) KA.Pp
    (List.replicate (d.length % 2) mkA)) KA.N (List.replicate n mkA) with hs3
  have e3' := exec_congr e3 (t' := s3)
    (by funext k; cases k <;> simp [hs1, hs2, hs3, Function.update_apply, hN, hn])
  -- flag `d_0 ≠ 0`
  have hs3DD : s3 KA.DD = toksE ι2 (d.map tokN) := by simp [hs1, hs2, hs3]
  set B0 : List A := if d.getD 0 0 = 0 then [] else [mkA] with hB0
  have e3b := exec_congr (exec_flagP KA.Bd (fun h => digA (h KA.DD)) s3)
    (t' := Function.update s3 KA.Bd B0) (by
      congr 1
      show (if digA (s3 KA.DD).head? = true then mkA :: s3 KA.Bd else s3 KA.Bd) = B0
      rw [hs3DD, dd_head, hB0]
      have : s3 KA.Bd = [] := by simp [hs1, hs2, hs3, hBd]
      rw [this]
      by_cases h0 : d.getD 0 0 = 0 <;> simp [h0])
  set s3b := Function.update s3 KA.Bd B0 with hs3b
  -- Cx := N + 2, skip the first n + 2 tokens of W
  obtain ⟨m4, hm4, e4⟩ := exec_copy KA.N KA.Cx KA.sc (by decide) (by decide) (by decide) s3b
    (by simp [hs1, hs2, hs3, hs3b, hsc])
  set s4 := Function.update s3b KA.Cx (s3b KA.N ++ s3b KA.Cx) with hs4
  have e5 := exec_pushG KA.Cx mkA s4
  have e6 := exec_pushG KA.Cx mkA (Function.update s4 KA.Cx (mkA :: s4 KA.Cx))
  set s6 := Function.update (Function.update s4 KA.Cx (mkA :: s4 KA.Cx)) KA.Cx
    (mkA :: (Function.update s4 KA.Cx (mkA :: s4 KA.Cx)) KA.Cx) with hs6
  obtain ⟨m7, hm7, e7⟩ := exec_skipToks' KA.Cx KA.W (by decide) ι1 ι1_inj (n + 2) (c.map digU) s6
    (by simpa using digU_toks_nosep c 0)
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hCx, List.replicate_succ])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6])
  set s7 := Function.update (Function.update s6 KA.Cx []) KA.W
    (toksE ι1 ((c.map digU).drop (n + 2))) with hs7
  obtain ⟨m8, hm8, e8⟩ := exec_copy KA.N KA.Ic KA.sc (by decide) (by decide) (by decide) s7
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hsc])
  set s8 := Function.update s7 KA.Ic (s7 KA.N ++ s7 KA.Ic) with hs8
  -- the double loop
  obtain ⟨s9, m9, hm9, e9, b, hs9, hb⟩ := exec_outerLoop s8 c d n (n + 2) (3 * L + 3)
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hF])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hIc])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hI])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hJc])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hJ])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hX])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hY])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hCy])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hSt])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hsc])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hE])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hC1])
    (by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8, hC2])
    (by omega) (by omega) (by omega) (by omega)
  have hko9 : s9 KA.ko = s KA.ko := by rw [hs9]; simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8]
  have hBd8 : s8 KA.Bd = B0 := by simp [hs1, hs2, hs3, hs3b, hs4, hs6, hs7, hs8]
  have hB0e : B0 = [] ↔ d.getD 0 0 = 0 := by
    rw [hB0]; by_cases h0 : d.getD 0 0 = 0 <;> simp [h0]
  have hG : Gtm c d ↔ d.getD 0 0 = 0 ∧ ∀ i < n, ∀ j < n,
      (c.getD (n + 2 + 2 * (i * n + j)) 0 = 1 →
        c.getD (n + 2 + 2 * (i * n + j) + 1) 0 ≤ (d.getD j 0 : ℤ) - d.getD i 0) := by
    unfold Gtm
    rw [← hn]
    have e : ∀ i j, 2 + n + 2 * (i * n + j) = n + 2 + 2 * (i * n + j) := by intro i j; ring
    simp only [e]
  rw [hBd8, hB0e] at hb
  have hm4' : m4 ≤ 6 * n + 3 := by simpa [hs1, hs2, hs3, hs3b] using hm4
  have hm8' : m8 ≤ 6 * n + 3 := by simpa [hs1, hs2, hs3, hs3b, hs4, hs6, hs7] using hm8
  have hm1' : m1 ≤ 3 * L + 1 := by simp [hkC] at hm1; omega
  have hm2' : m2 ≤ 3 * L + 1 := by simp [hs1, hkD] at hm2; omega
  have hm7' : m7 ≤ (n + 2) * (3 * L + 7) + 1 := by
    have : (n + 2) * (3 * (toksE ι1 (c.map digU)).length + 7) ≤ (n + 2) * (3 * L + 7) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hob := outer_bound n (3 * L + 3) (by omega)
  have hsk : (n + 2) * (3 * L + 7) ≤ 3 * ((3 * L + 4) * (3 * L + 4)) := by
    calc (n + 2) * (3 * L + 7) ≤ (3 * L + 4) * (3 * (3 * L + 4)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * ((3 * L + 4) * (3 * L + 4)) := by ring
  have hsq : (3 * L + 4) * (3 * L + 4) ≤ (3 * L + 4) * (3 * L + 4) * (3 * L + 4) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hsq1 : 3 * L + 4 ≤ (3 * L + 4) * (3 * L + 4) := Nat.le_mul_of_pos_right _ (by omega)
  have hob' : m9 ≤ 400 * ((3 * L + 4) * (3 * L + 4) * (3 * L + 4)) := by
    have e : 3 * L + 3 + 1 = 3 * L + 4 := by ring
    rw [e] at hob; omega
  by_cases hbe : b = []
  · have e10 := exec_skipP (K := KA) s9
    refine ⟨s9, _, ?_, StackProg.Exec.seq e1' (StackProg.Exec.seq e2' (StackProg.Exec.seq e3'
      (StackProg.Exec.seq e3b
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
      (StackProg.Exec.seq e8 (StackProg.Exec.seq e9
        (StackProg.Exec.branchTrue (by rw [hs9]; simp [hbe]) e10)))))))))), fun _ => hko9, ?_⟩
    · omega
    · intro hg; exact absurd (hG.2 (hb.1 hbe)) hg
  · obtain ⟨m10, hm10, e10⟩ := exec_clearG KA.ko s9
    obtain ⟨x, l, hxl⟩ := List.exists_cons_of_ne_nil hbe
    refine ⟨_, _, ?_, StackProg.Exec.seq e1' (StackProg.Exec.seq e2' (StackProg.Exec.seq e3'
      (StackProg.Exec.seq e3b
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6 (StackProg.Exec.seq e7
      (StackProg.Exec.seq e8 (StackProg.Exec.seq e9
        (StackProg.Exec.branchFalse (by rw [hs9]; simp [hxl]) e10)))))))))), ?_, fun _ => by simp⟩
    · rw [hko9] at hm10
      omega
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

def mainProg : SP := .seq (copyProg KA.ki KA.ko KA.sc)
  (.seq (scanProg KA.ki KA.st δA (outA KA.kc KA.kd KA.kC KA.kD))
    (.branch (fun h => decide (h KA.st = some (dsA DS.T0))) phaseB skipP))

set_option maxHeartbeats 4000000 in
theorem mainT (u : List A) : ∃ t n, n ≤ 2000 * ((3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4)) ∧
    mainProg.Exec (fun j => if j = KA.ki then u else []) t n ∧
    ((∃ c d, u = Ew c d ∧ ¬Gtm c d) → t KA.ko = []) ∧
    (¬(∃ c d, u = Ew c d ∧ ¬Gtm c d) → t KA.ko = u) := by
  obtain ⟨n1, hn1, e1⟩ := exec_copy KA.ki KA.ko KA.sc (by decide) (by decide) (by decide)
    (fun j => if j = KA.ki then u else []) (by simp)
  have hn1' : n1 ≤ 6 * u.length + 3 := by simpa using hn1
  have e1' := exec_congr e1 (t' := fun j => if j = KA.ki ∨ j = KA.ko then u else [])
    (by funext k; cases k <;> simp [Function.update_apply])
  set s1 : KA → List A := fun j => if j = KA.ki ∨ j = KA.ko then u else [] with hs1
  obtain ⟨e2, hiff, hcont, hoth⟩ := scanA_result KA.ki KA.st KA.kc KA.kd KA.kC KA.kD
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) u s1 (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
    (by simp [hs1]) (by simp [hs1])
  set s2 := scanRun KA.ki KA.st δA (outA KA.kc KA.kd KA.kC KA.kD) u s1 with hs2
  have hko2 : s2 KA.ko = u := by
    rw [hoth KA.ko (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [hs1]
  have hemp : ∀ k, k ≠ KA.ki → k ≠ KA.st → k ≠ KA.kc → k ≠ KA.kd → k ≠ KA.kC → k ≠ KA.kD →
      k ≠ KA.ko → s2 k = [] := by
    intro k h0 h1 h2 h3 h4 h5 h6
    rw [hoth k h0 h1 h2 h3 h4 h5]; simp [hs1, h0, h6]
  have hpow : 3 * u.length + 4 ≤ (3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4) := by
    have h1 : 1 ≤ 3 * u.length + 4 := by omega
    have h2 : 1 ≤ (3 * u.length + 4) * (3 * u.length + 4) := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 3 * u.length + 4 = 1 * (3 * u.length + 4) := (one_mul _).symm
      _ ≤ (3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4) := Nat.mul_le_mul_right _ h2
  by_cases hsh : ∃ c d, u = Ew c d
  · obtain ⟨c, d, hu⟩ := hsh
    obtain ⟨hkc, hkd, hkC, hkD⟩ := hcont c d hu
    have hlen : (encInts c).length + 1 + (encNats d).length = u.length := by
      rw [hu]; simp [Ew]; omega
    have hd1 := len_encNats' d
    have hst : decide ((s2 KA.st).head? = some (dsA DS.T0)) = true :=
      decide_eq_true (hiff.2 ⟨c, d, hu⟩)
    have he : ∀ k, k ≠ KA.ki ∧ k ≠ KA.st ∧ k ≠ KA.kc ∧ k ≠ KA.kd ∧ k ≠ KA.kC ∧ k ≠ KA.kD ∧
        k ≠ KA.ko → s2 k = [] := fun k ⟨h0, h1, h2, h3, h4, h5, h6⟩ => hemp k h0 h1 h2 h3 h4 h5 h6
    obtain ⟨t, m, hm, he, hg1, hg2⟩ := exec_phaseB s2 c d u.length hkC hkD hkd
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (he _ (by decide)) (he _ (by decide)) (he _ (by decide))
      (by omega) (by omega) (by omega) (by rw [hko2])
    have key : (∃ c0 d0, u = Ew c0 d0 ∧ ¬Gtm c0 d0) ↔ ¬Gtm c d := by
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
    · omega
    · intro h; exact hg2 (key.1 h)
    · intro h; rw [hg1 (by by_contra hg; exact h (key.2 hg)), hko2]
  · have hst : decide ((s2 KA.st).head? = some (dsA DS.T0)) = false :=
      decide_eq_false (fun h => hsh (hiff.1 h))
    have e3 := exec_skipP (K := KA) s2
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

/-- E_time: the temporal-feasibility filter is computed by a polynomial-time stack program. -/
theorem E_time : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(d.getD 0 0 = 0 ∧ ∀ i < d.length / 2, ∀ j < d.length / 2,
            c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j)) 0 = 1 →
              c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j) + 1) 0 ≤
                (d.getD j 0 : ℤ) - d.getD i 0)) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(d.getD 0 0 = 0 ∧ ∀ i < d.length / 2, ∀ j < d.length / 2,
            c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j)) 0 = 1 →
              c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j) + 1) 0 ≤
                (d.getD j 0 : ℤ) - d.getD i 0)) → s ko = u) := by
  obtain ⟨K, hK⟩ := poly_gen 128000 3
  refine ⟨KA, inferInstance, inferInstance, mainProg, KA.ki, KA.ko, K, fun u => ?_⟩
  obtain ⟨t, n, hn, he, h1, h2⟩ := mainT u
  refine ⟨t, n, ?_, he, h1, h2⟩
  have h : 3 * u.length + 4 ≤ 4 * (u.length + 1) := by omega
  have hb : (3 * u.length + 4) * (3 * u.length + 4) * (3 * u.length + 4) ≤
      (4 * (u.length + 1)) * (4 * (u.length + 1)) * (4 * (u.length + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul h h) h
  have he' : (4 * (u.length + 1)) * (4 * (u.length + 1)) * (4 * (u.length + 1)) =
      64 * (u.length + 1) ^ 3 := by ring
  have := hK u.length
  omega

end D0bfB

theorem solution : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
    (p : StackProg K (Option (BSym ⊕ BSym))) (ki ko : K) (k : ℕ), ∀ u,
    ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
      ((∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(d.getD 0 0 = 0 ∧ ∀ i < d.length / 2, ∀ j < d.length / 2,
            c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j)) 0 = 1 →
              c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j) + 1) 0 ≤
                (d.getD j 0 : ℤ) - d.getD i 0)) → s ko = []) ∧
      (¬(∃ (c : List ℤ) (d : List ℕ),
          u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
          ¬(d.getD 0 0 = 0 ∧ ∀ i < d.length / 2, ∀ j < d.length / 2,
            c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j)) 0 = 1 →
              c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j) + 1) 0 ≤
                (d.getD j 0 : ℤ) - d.getD i 0)) → s ko = u) := by
  exact D0bfB.E_time
