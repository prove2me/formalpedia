-- Prove2me | solution 1 for TernaryCode.A_3_16_11_ge_19
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-20T02:33:43.721524+00:00
-- url     : https://prove2.me/submissions/8808b7fb-aa0f-44ee-9969-15e4462cf8eb

import Mathlib

set_option autoImplicit false

namespace QaryCodeCert

/-! ## Bit-sliced checker for `q`-ary codes

A code of `M` words of length `n` over the alphabet `{0, ..., q-1}` is given twice: as the list `words`
(word `j` is the natural number whose base-`q` digit `c`, least significant first, is its symbol at
coordinate `c`) and as the table `cols` of its `n * q` symbol columns (`cols[c][a]` is the `M`-bit natural
number whose bit `j` says that word `j` has symbol `a` at coordinate `c`); `cols` is checked to be computed
from `words`.

For a word `x`, `run q x 0 cols Ts` walks the coordinates and, at coordinate `c`, adds the column of the
symbol of `x` at `c` to unary saturating counters, one bit-slice per word: bit `j` of the `k`-th counter
(0-based) says that word `j` agrees with `x` in at least `k + 1` coordinates. Everything below is proved;
the final checks are `decide +kernel`. -/

/-- the symbol of the word `x` at coordinate `c`: digit `c` of `x` in base `q`. -/
def sym (q x c : ℕ) : ℕ := x / q ^ c % q

theorem sym_lt {q : ℕ} (hq : 0 < q) (x c : ℕ) : sym q x c < q := Nat.mod_lt _ hq

/-- advance all counters by one column `B`; `p` is the previous (lower) counter. -/
def upd (B : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | p, t :: ts => (t ||| (p &&& B)) :: upd B t ts

/-- process the coordinates `c, c + 1, ...`; `R :: rs` are their symbol columns. -/
def run (q x : ℕ) : ℕ → List (List ℕ) → List ℕ → List ℕ
  | _, [], Ts => Ts
  | c, R :: rs, Ts => run q x (c + 1) rs (upd (R.getD (sym q x c) 0) (R.getD (sym q x c) 0) Ts)

/-- symbol column `(c, a)` of a list of words: bit `j` says that word `j` has symbol `a` at coordinate `c`. -/
def colOf (q c a : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.bit (decide (sym q x c = a)) (colOf q c a xs)

/-- row check: for every word `x = words[i]`, the counter "agreement ≥ s + 1" is exactly `{i}`. -/
def rowsOk (q : ℕ) (cols : List (List ℕ)) (s : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, x :: xs => ((run q x 0 cols (List.replicate (s + 1) 0)).getD s 0 == 2 ^ i) && rowsOk q cols s (i + 1) xs

/-- `Rep j m k Ts`: bit `j` of the `idx`-th entry of `Ts` is `decide (k + idx + 1 ≤ m)`. -/
def Rep (j m : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | k, t :: ts => t.testBit j = decide (k + 1 ≤ m) ∧ Rep j m (k + 1) ts

theorem upd_length (B : ℕ) : ∀ (Ts : List ℕ) (p : ℕ), (upd B p Ts).length = Ts.length := by
  intro Ts
  induction Ts with
  | nil => intro p; simp [upd]
  | cons t ts ih => intro p; simp [upd, ih]

theorem run_length (q x : ℕ) : ∀ (cs : List (List ℕ)) (c : ℕ) (Ts : List ℕ),
    (run q x c cs Ts).length = Ts.length := by
  intro cs
  induction cs with
  | nil => intro c Ts; simp [run]
  | cons R cs ih =>
    intro c Ts
    simp only [run, ih, upd_length]

theorem rep_replicate (j : ℕ) (K : ℕ) : ∀ k, Rep j 0 k (List.replicate K 0) := by
  induction K with
  | zero => intro k; simp [Rep]
  | succ K ih => intro k; simp only [List.replicate_succ, Rep]; exact ⟨by simp, ih (k + 1)⟩

theorem upd_rep (B j : ℕ) : ∀ (Ts : List ℕ) (k m p : ℕ), Rep j m k Ts →
    (p.testBit j && B.testBit j) = (decide (k ≤ m) && B.testBit j) →
    Rep j (m + if B.testBit j then 1 else 0) k (upd B p Ts) := by
  intro Ts
  induction Ts with
  | nil => intro k m p _ _; simp [upd, Rep]
  | cons t ts ih =>
    intro k m p h hp
    simp only [Rep] at h
    obtain ⟨ht, hts⟩ := h
    simp only [upd, Rep]
    refine ⟨?_, ih (k + 1) m t hts (by rw [ht])⟩
    rw [Nat.testBit_or, Nat.testBit_and, hp, ht]
    cases hB : B.testBit j
    · simp
    · by_cases h2 : k ≤ m
      · have h3 : k + 1 ≤ m + 1 := by omega
        simp [h2, h3]
      · have h1 : ¬ k + 1 ≤ m := by omega
        have h3 : ¬ k + 1 ≤ m + 1 := by omega
        simp [h1, h2, h3]

theorem run_rep (q x j : ℕ) : ∀ (cs : List (List ℕ)) (c m : ℕ) (Ts : List ℕ), Rep j m 0 Ts →
    Rep j (m + ∑ i ∈ Finset.range cs.length,
      if ((cs.getD i []).getD (sym q x (c + i)) 0).testBit j then 1 else 0) 0 (run q x c cs Ts) := by
  intro cs
  induction cs with
  | nil => intro c m Ts h; simpa [run] using h
  | cons R cs ih =>
    intro c m Ts h
    have h1 : Rep j (m + if (R.getD (sym q x c) 0).testBit j then 1 else 0) 0
        (upd (R.getD (sym q x c) 0) (R.getD (sym q x c) 0) Ts) :=
      upd_rep _ j Ts 0 m _ h (by rw [Bool.and_self, decide_eq_true (Nat.zero_le m), Bool.true_and])
    have h2 := ih (c + 1) _ _ h1
    simp only [run]
    have e : (m + ∑ i ∈ Finset.range (R :: cs).length,
          if (((R :: cs).getD i []).getD (sym q x (c + i)) 0).testBit j then 1 else 0) =
        (m + if (R.getD (sym q x c) 0).testBit j then 1 else 0) + ∑ i ∈ Finset.range cs.length,
          if ((cs.getD i []).getD (sym q x (c + 1 + i)) 0).testBit j then 1 else 0 := by
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      have hs : (∑ i ∈ Finset.range cs.length,
            if ((cs.getD i []).getD (sym q x (c + (i + 1))) 0).testBit j then 1 else 0) =
          ∑ i ∈ Finset.range cs.length,
            if ((cs.getD i []).getD (sym q x (c + 1 + i)) 0).testBit j then 1 else 0 :=
        Finset.sum_congr rfl (fun i _ => by rw [show c + (i + 1) = c + 1 + i by omega])
      rw [hs]
      ring
    rw [e]
    exact h2

theorem rep_getD (j m : ℕ) : ∀ (Ts : List ℕ) (k idx : ℕ), Rep j m k Ts → idx < Ts.length →
    (Ts.getD idx 0).testBit j = decide (k + idx + 1 ≤ m) := by
  intro Ts
  induction Ts with
  | nil => intro k idx _ h; simp at h
  | cons t ts ih =>
    intro k idx h hidx
    simp only [Rep] at h
    cases idx with
    | zero => simpa using h.1
    | succ idx =>
      simp only [List.getD_cons_succ]
      rw [ih (k + 1) idx h.2 (by simpa using hidx)]
      have e : k + 1 + idx + 1 = k + (idx + 1) + 1 := by omega
      rw [e]

theorem colOf_testBit (q c a : ℕ) : ∀ (ws : List ℕ) (j : ℕ), j < ws.length →
    (colOf q c a ws).testBit j = decide (sym q (ws.getD j 0) c = a) := by
  intro ws
  induction ws with
  | nil => intro j h; simp at h
  | cons x xs ih =>
    intro j hj
    cases j with
    | zero => simp [colOf]
    | succ j =>
      simp only [colOf, Nat.testBit_bit_succ, List.getD_cons_succ]
      exact ih j (by simpa using hj)

theorem rowsOk_sound (q : ℕ) (cols : List (List ℕ)) (s : ℕ) : ∀ (xs : List ℕ) (i0 : ℕ),
    rowsOk q cols s i0 xs = true →
    ∀ idx < xs.length, (run q (xs.getD idx 0) 0 cols (List.replicate (s + 1) 0)).getD s 0 = 2 ^ (i0 + idx) := by
  intro xs
  induction xs with
  | nil => intro i0 _ idx h; simp at h
  | cons x xs ih =>
    intro i0 h idx hidx
    simp only [rowsOk, Bool.and_eq_true, beq_iff_eq] at h
    cases idx with
    | zero => simpa using h.1
    | succ idx =>
      simp only [List.getD_cons_succ]
      rw [ih (i0 + 1) h.2 idx (by simpa using hidx)]
      congr 1
      omega

/-- `d(x,y) + #{c | x c = y c} = n` for words of length `n`. -/
theorem ham_agree {n q : ℕ} (x y : Fin n → Fin q) :
    hammingDist x y + (Finset.univ.filter (fun c => x c = y c)).card = n := by
  simp only [hammingDist, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  have h : ∀ c ∈ (Finset.univ : Finset (Fin n)),
      ((if x c ≠ y c then 1 else 0) + (if x c = y c then 1 else 0) : ℕ) = 1 := by
    intro c _
    by_cases hc : x c = y c <;> simp [hc]
  rw [Finset.sum_congr rfl h]
  simp

/-- word `j` of the list, as a function from coordinates to symbols. -/
def word (q : ℕ) (hq : 0 < q) (words : List ℕ) (n j : ℕ) : Fin n → Fin q :=
  fun c => ⟨sym q (words.getD j 0) c, sym_lt hq _ _⟩

theorem sound (q n M s : ℕ) (hq : 0 < q) (hs : s < n) (words : List ℕ) (cols : List (List ℕ))
    (hlen : words.length = M)
    (hcols : cols = (List.range n).map (fun c => (List.range q).map (fun a => colOf q c a words)))
    (hR : rowsOk q cols s 0 words = true) :
    ∃ C : Finset (Fin n → Fin q), C.card = M ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → n - s ≤ hammingDist x y) := by
  have hcl : cols.length = n := by rw [hcols]; simp
  have hcol : ∀ c < n, ∀ a < q, ∀ j < M,
      ((cols.getD c []).getD a 0).testBit j = decide (sym q (words.getD j 0) c = a) := by
    intro c hc a ha j hj
    have e1 : cols.getD c [] = (List.range q).map (fun a => colOf q c a words) := by
      rw [hcols, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
      rfl
    have e2 : ((List.range q).map (fun a => colOf q c a words)).getD a 0 = colOf q c a words := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha]
      rfl
    rw [e1, e2]
    exact colOf_testBit q c a words j (by omega)
  -- the counter value for word `x` against word `j`
  have hcount : ∀ x j : ℕ, j < M → (∑ i ∈ Finset.range cols.length,
      if ((cols.getD i []).getD (sym q x (0 + i)) 0).testBit j then 1 else 0) =
      (Finset.univ.filter (fun c : Fin n => sym q (words.getD j 0) c = sym q x c)).card := by
    intro x j hj
    rw [hcl, Finset.card_filter, Finset.sum_range]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Nat.zero_add, hcol c c.isLt _ (sym_lt hq _ _) j hj]
    simp
  -- agreements
  have hov : ∀ i < M, ∀ j < M, i ≠ j →
      (Finset.univ.filter (fun c => word q hq words n i c = word q hq words n j c)).card ≤ s := by
    intro i hi j hj hij
    have hr := rowsOk_sound q cols s words 0 hR i (by omega)
    have hrep := run_rep q (words.getD i 0) j cols 0 0 _ (rep_replicate j (s + 1) 0)
    rw [hcount _ j hj] at hrep
    have hlenT := run_length q (words.getD i 0) cols 0 (List.replicate (s + 1) 0)
    rw [List.length_replicate] at hlenT
    have e := rep_getD j _ _ 0 s hrep (by omega)
    rw [hr, Nat.testBit_two_pow] at e
    have hne : decide (0 + i = j) = false := by simp; omega
    rw [hne] at e
    have e' : ¬ (0 + s + 1 ≤ 0 + (Finset.univ.filter
        (fun c : Fin n => sym q (words.getD j 0) c = sym q (words.getD i 0) c)).card) := by
      intro hh; rw [decide_eq_true hh] at e; exact Bool.false_ne_true e
    have hfil : (Finset.univ.filter (fun c => word q hq words n i c = word q hq words n j c)) =
        Finset.univ.filter (fun c : Fin n => sym q (words.getD j 0) c = sym q (words.getD i 0) c) := by
      apply Finset.filter_congr
      intro c _
      simp only [word, Fin.mk.injEq]
      exact eq_comm
    rw [hfil]
    omega
  have hdist : ∀ i < M, ∀ j < M, i ≠ j →
      n - s ≤ hammingDist (word q hq words n i) (word q hq words n j) := by
    intro i hi j hj hij
    have h1 := ham_agree (word q hq words n i) (word q hq words n j)
    have h2 := hov i hi j hj hij
    omega
  let f : Fin M → (Fin n → Fin q) := fun j => word q hq words n j
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hne' : (a : ℕ) ≠ b := fun e => hne (Fin.ext e)
    have := hdist a a.isLt b b.isLt hne'
    have h0 : hammingDist (word q hq words n a) (word q hq words n b) = 0 := by
      have : f a = f b := hab
      simp only [f] at this
      rw [this, hammingDist_self]
    omega
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    have hab : (a : ℕ) ≠ b := fun e => hxy (by simp only [f]; rw [e])
    exact hdist a a.isLt b b.isLt hab

end QaryCodeCert

namespace QaryCodeCert

/-- the 19 codewords: base-3 digit `c` (least significant first) of a word is its symbol at coordinate `c`
(`c < 16`). -/
def words : List ℕ := [12065782, 18195874, 20412038, 35147586, 6327567, 10214263, 17926461, 30629829,
  21789080, 8692320, 17248480, 25539040, 34095200, 4407683, 13209929, 30164881,
  38573467, 42582530, 42717030]

/-- the 16 x 3 symbol columns of the code (`cols[c][a]` has bit `j` iff word `j` has symbol `a` at coordinate `c`). -/
def cols : List (List ℕ) := [[262872,
   101411,
   160004],
  [133236,
   45705,
   345346],
  [266466,
   27676,
   230145],
  [132273,
   86598,
   305416],
  [294958,
   78929,
   150400],
  [139399,
   50792,
   334096],
  [278555,
   76452,
   169280],
  [196685,
   55442,
   272160],
  [283781,
   166418,
   74088],
  [198170,
   276545,
   49572],
  [297541,
   152616,
   74130],
  [145450,
   329348,
   49489],
  [84168,
   4899,
   435220],
  [102452,
   3465,
   418370],
  [42178,
   4892,
   477217],
  [25137,
   3398,
   495752]]

theorem words_length : words.length = 19 := by decide +kernel

theorem cols_eq : cols = (List.range 16).map (fun c => (List.range 3).map (fun a => colOf 3 c a words)) := by
  decide +kernel

theorem rows_ok : rowsOk 3 cols 5 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 16 → Fin 3), C.card = 19 ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 11 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2⟩ := sound 3 16 19 5 (by norm_num) (by norm_num) words cols words_length cols_eq rows_ok
  exact ⟨C, h1, fun x hx y hy hxy => by simpa using h2 x hx y hy hxy⟩

end QaryCodeCert

theorem solution : ∃ C : Finset (Fin 16 → Fin 3), C.card = 19 ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 11 ≤ hammingDist x y) := by
  exact QaryCodeCert.main
