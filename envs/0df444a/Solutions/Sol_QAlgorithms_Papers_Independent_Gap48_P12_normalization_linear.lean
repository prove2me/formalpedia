-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.normalization_linear
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:48:53.857843+00:00
-- url     : https://prove2.me/submissions/01af8c2a-3167-443c-8674-16c7324c1496

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_uniqueness
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_tcount_nonincrease
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_clifford_three_cosets
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_appendix_rewrite_tables

noncomputable section

namespace X4P12

open QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Gap48.P12 (CircuitLetter CircuitWord wordTCount atMostT minimalT
  chronologicalInstructions)

local notation "Mat" => Matrix Bool Bool ℂ
local notation "ω" => QAlgorithms.gateT true true

/-- printed-order matrix of a source letter (H/P basis) -/
def gm : CircuitLetter → Mat
  | .h => QAlgorithms.hadamard
  | .p => QAlgorithms.phaseS
  | .t => QAlgorithms.gateT

def wm (w : CircuitWord) : Mat :=
  Next46.P21.wordMatrix (chronologicalInstructions .hp w)

def toL : CircuitLetter → Next46.P21.Letter
  | .h => .h
  | .p => .s
  | .t => .t

lemma chron_eq (w : CircuitWord) : chronologicalInstructions .hp w = (w.map toL).reverse := by
  unfold chronologicalInstructions
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.reverse_cons, List.flatMap_append, List.map_cons, ih]
    cases a <;> simp [toL]

lemma wm_eq (w : CircuitWord) : wm w = (w.map gm).prod := by
  rw [wm, chron_eq, Next46.P21.wordMatrix, List.map_reverse, List.reverse_reverse, List.map_map]
  congr 2
  funext a; cases a <;> rfl

lemma wm_nil : wm [] = 1 := by simp [wm_eq]
lemma wm_append (u v : CircuitWord) : wm (u ++ v) = wm u * wm v := by simp [wm_eq, List.prod_append]
lemma wm_cons (a : CircuitLetter) (v : CircuitWord) : wm (a :: v) = gm a * wm v := by simp [wm_eq]

lemma tc_append (u v : CircuitWord) : wordTCount (u ++ v) = wordTCount u + wordTCount v := by
  simp [wordTCount, List.count_append]

/-! ### omega as an H/P word -/

lemma om_eq : ω = ((Real.sqrt 2 : ℂ))⁻¹ * (1 + Complex.I) := by
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0)
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  field_simp
  push_cast
  linear_combination (1 + Complex.I) * hs / 2

def omW : CircuitWord := [.h, .p, .h, .p, .h, .p]

lemma omW_val : wm omW = Gap48.P10.scalarOmega := by
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0)
  rw [wm_eq]
  simp only [omW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, gm]
  ext i j
  rw [Gap48.P10.scalarOmega, om_eq]
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, QAlgorithms.hadamard, QAlgorithms.phaseS, Matrix.diagonal,
      Matrix.one_apply] <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;>
    linear_combination (-(1 + Complex.I)) * hs

/-! ### translation to the Giles–Selinger (P10) setting -/

open Gap48.P10 (Clifford NormalForm maValue normalTCount Input inputWordMatrix inputTCount
  cliffordWordMatrix CliffordLetter cliffordLetterMatrix cliffordOfWord cliffordH cliffordSH)

def cS : Clifford := cliffordOfWord [.s]

def toI : CircuitLetter → Input
  | .h => .clifford cliffordH
  | .p => .clifford cS
  | .t => .t

lemma toI_mat (a : CircuitLetter) : Gap48.P10.inputMatrix (toI a) = gm a := by
  cases a <;> simp [toI, gm, Gap48.P10.inputMatrix, cliffordH, cS, cliffordOfWord, cliffordWordMatrix,
    cliffordLetterMatrix]

lemma iwm (w : CircuitWord) : inputWordMatrix (w.map toI) = wm w := by
  rw [wm_eq, inputWordMatrix, List.map_map]
  congr 1
  exact List.map_congr_left (fun a _ => toI_mat a)

lemma itc (w : CircuitWord) : inputTCount (w.map toI) = wordTCount w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp_all [inputTCount, wordTCount, toI, List.filter_cons, List.count_cons]

def cl : CliffordLetter → CircuitWord
  | .h => [.h]
  | .s => [.p]
  | .omega => omW

def clw (l : List CliffordLetter) : CircuitWord := l.flatMap cl

lemma clw_val (l : List CliffordLetter) : wm (clw l) = cliffordWordMatrix l := by
  induction l with
  | nil => simp [clw, wm_nil, cliffordWordMatrix]
  | cons a l ih =>
    rw [clw, List.flatMap_cons, wm_append, ← clw, ih]
    simp only [cliffordWordMatrix, List.map_cons, List.prod_cons]
    cases a
    · simp [cl, wm_cons, wm_nil, gm, cliffordLetterMatrix]
    · simp [cl, wm_cons, wm_nil, gm, cliffordLetterMatrix]
    · simp [cl, omW_val, cliffordLetterMatrix]

lemma clw_tc (l : List CliffordLetter) : wordTCount (clw l) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [clw, List.flatMap_cons, tc_append, ← clw, ih]
    cases a <;> rfl

def cw (C : Clifford) : CircuitWord := clw (Classical.choose C.property)

lemma cw_val (C : Clifford) : wm (cw C) = C.val :=
  (clw_val _).trans (Classical.choose_spec C.property)

lemma cw_tc (C : Clifford) : wordTCount (cw C) = 0 := clw_tc _

def syl (q : Bool) : CircuitWord := (if q then [.p, .h] else [.h]) ++ [.t]

def nfw (M : NormalForm) : CircuitWord :=
  (if M.leadingT then [.t] else []) ++ M.body.flatMap syl ++ cw M.terminal

lemma body_val (b : List Bool) : wm (b.flatMap syl) =
    ((b.flatMap fun q => [Gap48.P10.Token.clifford (if q then cliffordSH else cliffordH),
      Gap48.P10.Token.t]).map Gap48.P10.tokenMatrix).prod := by
  induction b with
  | nil => simp [wm_nil]
  | cons q b ih =>
    rw [List.flatMap_cons, wm_append, ih, List.flatMap_cons, List.map_append, List.prod_append]
    congr 1
    cases q <;> simp [syl, wm_cons, wm_nil, gm, Gap48.P10.tokenMatrix, cliffordSH, cliffordH, cliffordOfWord,
      cliffordWordMatrix, cliffordLetterMatrix, Matrix.mul_assoc]

lemma nfw_val (M : NormalForm) : wm (nfw M) = maValue M := by
  rw [nfw, wm_append, wm_append, body_val, cw_val]
  simp only [maValue, Gap48.P10.normalValue, Gap48.P10.normalTokens, List.map_append, List.prod_append]
  congr 2
  · cases M.leadingT <;> simp [wm_nil, wm_cons, gm, Gap48.P10.tokenMatrix]
  · simp [Gap48.P10.tokenMatrix]

lemma body_tc (b : List Bool) : wordTCount (b.flatMap syl) = b.length := by
  induction b with
  | nil => rfl
  | cons q b ih =>
    rw [List.flatMap_cons, tc_append, ih, List.length_cons]
    cases q <;> simp [syl, wordTCount] <;> omega

lemma nfw_tc (M : NormalForm) : wordTCount (nfw M) = normalTCount M := by
  rw [nfw, tc_append, tc_append, body_tc, cw_tc, normalTCount]
  cases M.leadingT <;> rfl

/-! ### layers -/

lemma atMost_eq (n : ℕ) : atMostT n = {U | ∃ M : NormalForm, normalTCount M ≤ n ∧ maValue M = U} := by
  ext U
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨M, hM, hc, -⟩ := Gap48.P10.ma_tcount_nonincrease (wm w) (wordTCount w)
      ⟨w.map toI, iwm w, itc w⟩
    exact ⟨M, hc.trans hw, hM⟩
  · rintro ⟨M, hc, rfl⟩
    exact ⟨nfw M, by rw [nfw_tc]; exact hc, nfw_val M⟩

lemma opt (M : NormalForm) (k : ℕ) (h : maValue M ∈ atMostT k) : normalTCount M ≤ k := by
  rw [atMost_eq] at h
  obtain ⟨M', hc, hM'⟩ := h
  rw [← Gap48.P10.ma_uniqueness hM']
  exact hc

lemma minimal_eq (n : ℕ) : minimalT (n + 1) = maValue '' {M | normalTCount M = n + 1} := by
  ext U
  simp only [minimalT, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [atMost_eq] at h1
    obtain ⟨M, hc, rfl⟩ := h1
    refine ⟨M, ?_, rfl⟩
    by_contra hne
    exact h2 (by rw [atMost_eq]; exact ⟨M, by omega, rfl⟩)
  · rintro ⟨M, hc, rfl⟩
    refine ⟨by rw [atMost_eq]; exact ⟨M, hc.le, rfl⟩, fun h => ?_⟩
    have := opt M n h
    omega

def eqv (n : ℕ) : {M : NormalForm // normalTCount M = n + 1} ≃
    (List.Vector Bool n ⊕ List.Vector Bool (n + 1)) × Clifford where
  toFun M := (if h : M.1.leadingT then .inl ⟨M.1.body, by
      have := M.2; simp only [normalTCount, h, if_true] at this; omega⟩
    else .inr ⟨M.1.body, by
      have := M.2; simp only [normalTCount, h] at this; simpa using this⟩, M.1.terminal)
  invFun p := ⟨⟨p.1.elim (fun _ => true) (fun _ => false), p.1.elim (·.1) (·.1), p.2⟩, by
    rcases p with ⟨v | v, C⟩
    · simp [normalTCount, v.2]; omega
    · simp [normalTCount, v.2]⟩
  left_inv := by
    rintro ⟨⟨b, l, C⟩, h⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨v | v, C⟩ <;> rfl

lemma card_layer (n : ℕ) : Nat.card {M : NormalForm // normalTCount M = n + 1} =
    (2 ^ n + 2 ^ (n + 1)) * Nat.card Clifford := by
  rw [Nat.card_congr (eqv n), Nat.card_prod, Nat.card_sum]
  simp [Nat.card_eq_fintype_card, card_vector]

/-! ### Clifford set -/

def back : CircuitLetter → CliffordLetter
  | .h => .h
  | .p => .s
  | .t => .omega

lemma back_val (w : CircuitWord) (hw : CircuitLetter.t ∉ w) : cliffordWordMatrix (w.map back) = wm w := by
  induction w with
  | nil => simp [cliffordWordMatrix, wm_nil]
  | cons a w ih =>
    simp only [List.mem_cons, not_or] at hw
    rw [wm_cons, ← ih hw.2]
    simp only [cliffordWordMatrix, List.map_cons, List.prod_cons]
    cases a
    · rfl
    · rfl
    · exact absurd rfl hw.1

lemma cliff_eq : Gap48.P10.cliffordSet = Gap48.P12.cliffordSet .hp := by
  ext U
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨clw l, ?_, clw_val l⟩
    have := clw_tc l
    simpa [Gap48.P12.IsCliffordWord, wordTCount, List.count_eq_zero] using this
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.map back, back_val w hw⟩

lemma cliff_card : (Gap48.P12.cliffordSet .hp).Finite ∧ (Gap48.P12.cliffordSet .hp).ncard = 192 := by
  obtain ⟨he, d1, d2, d3, f1, c1, f2, c2, f3, c3⟩ := Gap48.P12.clifford_three_cosets
  rw [he]
  refine ⟨(f1.union f2).union f3, ?_⟩
  rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d2, d3⟩) (f1.union f2) f3,
    Set.ncard_union_eq d1 f1 f2, c1, c2, c3]

lemma card_cliff : Nat.card Clifford = 192 := by
  rw [Nat.card_coe_set_eq, cliff_eq, cliff_card.2]

lemma minimal_card (n : ℕ) : (minimalT (n + 1)).ncard = 576 * 2 ^ n := by
  rw [minimal_eq, Set.ncard_image_of_injective _ Gap48.P10.ma_uniqueness, ← Nat.card_coe_set_eq]
  change Nat.card {M : NormalForm // normalTCount M = n + 1} = _
  rw [card_layer, card_cliff, pow_succ]
  ring

lemma minimal_fin (n : ℕ) : (minimalT (n + 1)).Finite :=
  Set.finite_of_ncard_pos (by rw [minimal_card]; positivity)

lemma atMost0 : atMostT 0 = Gap48.P12.cliffordSet .hp := by
  ext U
  simp only [atMostT, Gap48.P12.cliffordSet, Set.mem_setOf_eq, Gap48.P12.IsCliffordWord, wordTCount,
    Nat.le_zero, List.count_eq_zero]

lemma atMost_mono (n : ℕ) : atMostT n ⊆ atMostT (n + 1) := by
  rintro U ⟨w, hw, h⟩
  exact ⟨w, by omega, h⟩

lemma atMost_succ (n : ℕ) : atMostT (n + 1) = atMostT n ∪ minimalT (n + 1) := by
  rw [minimalT, Set.union_diff_cancel (atMost_mono n)]

lemma atMost_card (n : ℕ) : (atMostT n).Finite ∧ (atMostT n).ncard = 192 * (3 * 2 ^ n - 2) := by
  induction n with
  | zero => rw [atMost0]; exact ⟨cliff_card.1, by rw [cliff_card.2]; norm_num⟩
  | succ n ih =>
    rw [atMost_succ]
    refine ⟨ih.1.union (minimal_fin n), ?_⟩
    rw [Set.ncard_union_eq (show Disjoint (atMostT n) (minimalT (n + 1)) from Set.disjoint_sdiff_right) ih.1 (minimal_fin n), ih.2, minimal_card]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

end X4P12


noncomputable section

namespace X4P12N

open QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Gap48.P12
open X4P12 (wm wm_eq wm_nil wm_cons wm_append tc_append gm cliff_card)

local notation "Mat" => Matrix Bool Bool ℂ
local notation "TT" => QAlgorithms.gateT

lemma wm_fold (w : CircuitWord) : Next46.P21.wordMatrix (chronologicalInstructions .hp w) = wm w := rfl

lemma TT_sq : TT * TT = QAlgorithms.phaseS := by
  have h : Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) = Complex.I := by
    rw [← Complex.exp_add]
    have : Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 = (Real.pi / 2 : ℝ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.gateT, QAlgorithms.phaseS, Matrix.diagonal, Matrix.mul_apply, h]

/-! ### table facts -/

lemma table_tfree : ∀ row ∈ rewriteTable, CircuitLetter.t ∉ row.2.2 := by decide +kernel

def P0 : Set CircuitWord := {[], [.h], [.p, .h]}
def P1 : Set CircuitWord := {[.h], [.p, .h]}

lemma prefix_P0 (j : Fin 3) : appendixPrefix j ∈ P0 := by
  fin_cases j <;> simp [appendixPrefix, P0]

lemma row_of_mem (j : Fin 3) (p : CircuitWord × CircuitWord) (hp : p ∈ appendixTable j) :
    wm p.1 * TT = wm (appendixPrefix j) * TT * wm p.2 := by
  obtain ⟨hlen, hid⟩ := appendix_rewrite_tables.1 j
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  have := hid ⟨i, by omega⟩
  simp only [appendixRow, List.getD_eq_getElem _ _ hi] at this
  exact this

lemma table_row (row : CircuitWord × CircuitWord × CircuitWord) (h : row ∈ rewriteTable) :
    wm row.1 * TT = wm row.2.1 * TT * wm row.2.2 ∧ row.2.1 ∈ P0 := by
  simp only [rewriteTable, List.mem_append, List.mem_map] at h
  rcases h with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
  · exact ⟨row_of_mem 0 p hp, prefix_P0 0⟩
  · exact ⟨row_of_mem 1 p hp, prefix_P0 1⟩
  · exact ⟨row_of_mem 2 p hp, prefix_P0 2⟩

lemma lookup_spec (U : Mat) (hU : U ∈ cliffordSet .hp) :
    U * TT = wm (rewriteLookup U).1 * TT * wm (rewriteLookup U).2 ∧ (rewriteLookup U).1 ∈ P0 ∧
      CircuitLetter.t ∉ (rewriteLookup U).2 := by
  have hcov := (appendix_rewrite_tables.2.2.1 U).1 hU
  obtain ⟨row0, hrow0, e0⟩ := List.mem_map.1 hcov
  unfold rewriteLookup
  split
  · rename_i row hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    obtain ⟨h1, h2⟩ := table_row row hmem
    refine ⟨?_, h2, table_tfree row hmem⟩
    rw [← hp]
    exact h1
  · rename_i hfind
    exfalso
    have := List.find?_eq_none.1 hfind row0 hrow0
    simp only [decide_eq_true_eq] at this
    exact this e0

/-! ### Clifford closure -/

lemma cliff_of_tfree (w : CircuitWord) (hw : CircuitLetter.t ∉ w) : wm w ∈ cliffordSet .hp :=
  ⟨w, hw, rfl⟩

lemma tfree_P0 {a : CircuitWord} (ha : a ∈ P0) : CircuitLetter.t ∉ a := by
  simp only [P0, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl <;> decide

lemma cliff_tfree {U : Mat} (hU : U ∈ cliffordSet .hp) : ∃ w, CircuitLetter.t ∉ w ∧ wm w = U := hU

lemma cliff_mul {U V : Mat} (hU : U ∈ cliffordSet .hp) (hV : V ∈ cliffordSet .hp) : U * V ∈ cliffordSet .hp := by
  obtain ⟨u, hu, rfl⟩ := cliff_tfree hU
  obtain ⟨v, hv, rfl⟩ := cliff_tfree hV
  refine ⟨u ++ v, by simp [IsCliffordWord, hu, hv], (wm_append u v)⟩

lemma H_cliff : QAlgorithms.hadamard ∈ cliffordSet .hp := ⟨[.h], by simp [IsCliffordWord], by show wm [.h] = _; simp [wm_eq, gm]⟩
lemma S_cliff : QAlgorithms.phaseS ∈ cliffordSet .hp := ⟨[.p], by simp [IsCliffordWord], by show wm [.p] = _; simp [wm_eq, gm]⟩
lemma one_cliff : (1 : Mat) ∈ cliffordSet .hp := ⟨[], by simp [IsCliffordWord], rfl⟩

/-! ### stacks -/

def Good : List CircuitWord → Prop
  | [] => True
  | [a] => a ∈ P0
  | a :: b :: r => a ∈ P1 ∧ Good (b :: r)

lemma P1_P0 {a : CircuitWord} (h : a ∈ P1) : a ∈ P0 := by
  simp only [P1, P0, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  tauto

lemma good_mem : ∀ (l : List CircuitWord), Good l → ∀ a ∈ l, a ∈ P0
  | [], _, a, ha => by simp at ha
  | [b], h, a, ha => by simp at ha; subst ha; exact h
  | b :: c :: r, h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact P1_P0 h.1
    · exact good_mem (c :: r) h.2 a ha

lemma good_tail : ∀ (a : CircuitWord) (l : List CircuitWord), Good (a :: l) → Good l
  | _, [], _ => trivial
  | _, _ :: _, h => h.2

lemma good_push (s : CircuitWord) (l : List CircuitWord) (hl : Good l) (hs : s ∈ P0)
    (hne : l ≠ [] → s ∈ P1) : Good (s :: l) := by
  cases l with
  | nil => exact hs
  | cons b r => exact ⟨hne (by simp), hl⟩

lemma mat_eq (l : List CircuitWord) (x : CircuitWord) :
    materialize (l, x) = materialize (l, []) ++ x := by
  simp [materialize]

lemma mat_cons (a : CircuitWord) (l : List CircuitWord) (x : CircuitWord) :
    materialize (a :: l, x) = materialize (l, a ++ [.t] ++ x) := by
  simp [materialize, List.append_assoc]

lemma normal_mat (reps : Representatives .hp) : ∀ (l : List CircuitWord) (x : CircuitWord), Good l →
    IsNormalWord .hp reps x → x.head? ≠ some .t → IsNormalWord .hp reps (materialize (l, x))
  | [], x, _, hx, _ => by simpa [materialize] using hx
  | [a], x, ha, hx, hh => by
    rw [mat_cons]
    show IsNormalWord .hp reps (a ++ [.t] ++ x)
    change a ∈ P0 at ha
    simp only [P0, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact IsNormalWord.withT _ hx hh
    · exact IsNormalWord.withHT _ hx hh
    · exact IsNormalWord.withPHT _ hx hh
  | a :: b :: r, x, ha, hx, hh => by
    rw [mat_cons]
    obtain ⟨ha1, hr⟩ := ha
    simp only [P1, Set.mem_insert_iff, Set.mem_singleton_iff] at ha1
    rcases ha1 with rfl | rfl
    · exact normal_mat reps (b :: r) _ hr (IsNormalWord.withHT _ hx hh) (by simp)
    · exact normal_mat reps (b :: r) _ hr (IsNormalWord.withPHT _ hx hh) (by simp)

lemma tc_mat : ∀ (l : List CircuitWord), (∀ a ∈ l, a ∈ P0) →
    wordTCount (materialize (l, [])) = l.length
  | [], _ => rfl
  | a :: l, h => by
    rw [mat_cons, mat_eq, tc_append, tc_mat l (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    have ha := tfree_P0 (h a (List.mem_cons_self))
    simp [wordTCount, List.count_append, List.count_eq_zero.2 ha]

lemma len_mat : ∀ (l : List CircuitWord), (∀ a ∈ l, a ∈ P0) →
    (materialize (l, [])).length ≤ 3 * l.length
  | [], _ => by simp [materialize]
  | a :: l, h => by
    rw [mat_cons, mat_eq, List.length_append]
    have ih := len_mat l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self)
    have : a.length ≤ 2 := by
      simp only [P0, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl <;> simp
    simp at ih ⊢
    omega

/-! ### invariant -/

lemma rc (reps : Representatives .hp) {U : Mat} (hU : U ∈ cliffordSet .hp) : wm (reps.word U) = U :=
  reps.computes U hU


def Inv (reps : Representatives .hp) (u : CircuitWord) (acc : NormalizerState × ℕ) : Prop :=
  Good acc.1.1 ∧ (∃ V ∈ cliffordSet .hp, acc.1.2 = reps.word V) ∧ wm (materialize acc.1) = wm u ∧
    acc.1.1.length ≤ wordTCount u ∧ acc.2 ≤ 1 + 5 * u.length

lemma inv_init (reps : Representatives .hp) : Inv reps [] (([], reps.word 1), 1) := by
  refine ⟨trivial, ⟨1, one_cli, rfl⟩, ?_, le_refl _, by simp⟩
  simp only [materialize, List.reverse_nil, List.flatMap_nil, List.nil_append]
  exact reps.computes 1 one_cliff
where one_cli : (1 : Mat) ∈ cliffordSet .hp := one_cliff

lemma inv_step (reps : Representatives .hp) (u : CircuitWord) (acc : NormalizerState × ℕ)
    (g : CircuitLetter) (h : Inv reps u acc) :
    Inv reps (u ++ [g]) ((normalizeStep reps acc.1 g).1, acc.2 + (normalizeStep reps acc.1 g).2) := by
  obtain ⟨⟨l, x⟩, c⟩ := acc
  obtain ⟨hg, ⟨V, hV, rfl⟩, hval, hlen, hc⟩ := h
  have hwV : wm (reps.word V) = V := reps.computes V hV
  simp only at hg hval hlen hc
  rw [mat_eq, wm_append, hwV] at hval
  have htc : wordTCount (u ++ [g]) = wordTCount u + wordTCount [g] := tc_append _ _
  have hlu : (u ++ [g]).length = u.length + 1 := by simp
  cases g with
  | h =>
    simp only [normalizeStep, wm_fold]
    refine ⟨hg, ⟨V * QAlgorithms.hadamard, cliff_mul hV H_cliff, by rw [hwV]⟩, ?_, ?_, ?_⟩
    · rw [hwV, mat_eq, wm_append, rc reps (cliff_mul hV H_cliff), wm_append, ← hval]
      simp [wm_eq, gm, Matrix.mul_assoc]
    · dsimp only; omega
    · dsimp only; omega
  | p =>
    simp only [normalizeStep, wm_fold]
    refine ⟨hg, ⟨V * QAlgorithms.phaseS, cliff_mul hV S_cliff, by rw [hwV]⟩, ?_, ?_, ?_⟩
    · rw [hwV, mat_eq, wm_append, rc reps (cliff_mul hV S_cliff), wm_append, ← hval]
      simp [wm_eq, gm, Matrix.mul_assoc]
    · dsimp only; omega
    · dsimp only; omega
  | t =>
    obtain ⟨hid, hP0, htf⟩ := lookup_spec V hV
    have hRc : wm (rewriteLookup V).2 ∈ cliffordSet .hp := cliff_of_tfree _ htf
    have htc1 : wordTCount [CircuitLetter.t] = 1 := rfl
    have hT : wm [CircuitLetter.t] = TT := by simp [wm_eq, gm]
    simp only [normalizeStep, wm_fold]
    rw [hwV]
    generalize hr : rewriteLookup V = rule at hid hP0 htf hRc
    obtain ⟨s, rt⟩ := rule
    simp only at hid hP0 htf hRc ⊢
    cases s with
    | nil =>
      rw [wm_nil, Matrix.one_mul] at hid
      cases l with
      | nil =>
        have hm : materialize (([] : List CircuitWord), ([] : CircuitWord)) = [] := rfl
        rw [hm, wm_nil, Matrix.one_mul] at hval
        refine ⟨hP0, ⟨_, hRc, rfl⟩, ?_, ?_, ?_⟩
        · show wm ([] ++ [.t] ++ reps.word (wm rt)) = _
          rw [wm_append, wm_append, rc reps hRc, wm_append, ← hval, hT, hid, wm_nil, Matrix.one_mul]
        · dsimp only; simp only [List.length_cons, List.length_nil]; omega
        · dsimp only; omega
      | cons a rest =>
        have ha := good_mem _ hg a List.mem_cons_self
        have hc' : wm a * QAlgorithms.phaseS * wm rt ∈ cliffordSet .hp :=
          cliff_mul (cliff_mul (cliff_of_tfree a (tfree_P0 ha)) S_cliff) hRc
        have key : wm a * QAlgorithms.phaseS * wm rt = wm a * TT * (V * TT) := by
          rw [hid, ← TT_sq]; simp only [Matrix.mul_assoc]
        refine ⟨good_tail a rest hg, ⟨_, hc', rfl⟩, ?_, ?_, ?_⟩
        · dsimp only
          rw [mat_eq, wm_append, rc reps hc', key, wm_append, ← hval, mat_cons, mat_eq rest (a ++ _ ++ _)]
          simp only [wm_append, List.append_nil, hT, Matrix.mul_assoc]
        · dsimp only; simp only [List.length_cons] at hlen; omega
        · dsimp only; omega
    | cons y ys =>
      have hP1 : (y :: ys) ∈ P1 := by
        simp only [P0, P1, Set.mem_insert_iff, Set.mem_singleton_iff] at hP0 ⊢
        rcases hP0 with h0 | h0 | h0
        · exact absurd h0 (by simp)
        · exact Or.inl h0
        · exact Or.inr h0
      refine ⟨good_push _ l hg hP0 (fun _ => hP1), ⟨_, hRc, rfl⟩, ?_, ?_, ?_⟩
      · dsimp only
        rw [mat_cons, mat_eq]
        simp only [wm_append]
        rw [rc reps hRc, ← hval, hT, Matrix.mul_assoc _ V, hid]
      · dsimp only; simp only [List.length_cons]; omega
      · dsimp only; omega

lemma run_aux (reps : Representatives .hp) : ∀ (w u : CircuitWord) (acc : NormalizerState × ℕ),
    Inv reps u acc → Inv reps (u ++ w) (w.foldl (fun acc g =>
      let step := normalizeStep reps acc.1 g
      (step.1, acc.2 + step.2)) acc)
  | [], u, acc, h => by simpa using h
  | g :: w, u, acc, h => by
    rw [List.foldl_cons]
    have := run_aux reps w (u ++ [g]) _ (inv_step reps u acc g h)
    simpa [List.append_assoc] using this

lemma run_inv (reps : Representatives .hp) (C : CircuitWord) : Inv reps C (normalizeRun reps C) := by
  have := run_aux reps C [] _ (inv_init reps)
  simpa [normalizeRun] using this

theorem main (reps : Representatives .hp) :
    ∃ K : ℕ, 0 < K ∧ ∀ C : CircuitWord,
      IsNormalWord .hp reps (normalizeWord reps C) ∧
      wm (normalizeWord reps C) = wm C ∧
      wordTCount (normalizeWord reps C) ≤ wordTCount C ∧
      normalizationCost reps C ≤ K * (C.length + 1) := by
  obtain ⟨B, hB⟩ := (cliff_card.1.image (fun V => (reps.word V).length)).bddAbove
  refine ⟨13 + B, by omega, fun C => ?_⟩
  obtain ⟨hg, ⟨V, hV, hx⟩, hval, hlen, hc⟩ := run_inv reps C
  have hmem := good_mem _ hg
  have htf : CircuitLetter.t ∉ reps.word V := reps.clifford V hV
  have hxB : (reps.word V).length ≤ B := hB ⟨V, hV, rfl⟩
  have htcC : wordTCount C ≤ C.length := List.count_le_length
  have hnw : normalizeWord reps C = materialize ((normalizeRun reps C).1.1, []) ++ reps.word V := by
    rw [normalizeWord, ← hx, ← mat_eq]
  refine ⟨?_, hval, ?_, ?_⟩
  · rw [normalizeWord, ← Prod.mk.eta (p := (normalizeRun reps C).1), hx]
    refine normal_mat reps _ _ hg (IsNormalWord.tail V hV) ?_
    intro e; exact htf (List.mem_of_head? e)
  · rw [hnw, tc_append, tc_mat _ hmem]
    have : wordTCount (reps.word V) = 0 := List.count_eq_zero.2 htf
    omega
  · have hl := len_mat _ hmem
    rw [normalizationCost, hnw, List.length_append]
    nlinarith
end X4P12N

open QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ
local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

theorem solution (reps : Representatives .hp) :
    ∃ K : ℕ, 0 < K ∧ ∀ C : CircuitWord,
      IsNormalWord .hp reps (normalizeWord reps C) ∧
      wordMatrix .hp (normalizeWord reps C) = wordMatrix .hp C ∧
      wordTCount (normalizeWord reps C) ≤ wordTCount C ∧
      normalizationCost reps C ≤ K * (C.length + 1) :=
  X4P12N.main reps

end
