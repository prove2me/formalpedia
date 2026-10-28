-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.collision_implies_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:33:44.992789+00:00
-- url     : https://prove2.me/submissions/47ee25ca-824a-47b7-b9aa-df7ae058d9dd

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_uniqueness
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_tcount_nonincrease
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_clifford_three_cosets

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

namespace X4P12

open QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Gap48.P12 (CircuitLetter CircuitWord wordTCount IsNormalWord Representatives)
open Gap48.P10 (Clifford NormalForm maValue)

def nfwR (reps : Representatives .hp) (M : NormalForm) : CircuitWord :=
  (if M.leadingT then [.t] else []) ++ M.body.flatMap syl ++ reps.word M.terminal.val

lemma nfwR_val (reps : Representatives .hp) (M : NormalForm) : wm (nfwR reps M) = maValue M := by
  have hc : wm (reps.word M.terminal.val) = M.terminal.val :=
    reps.computes _ (cliff_eq ▸ M.terminal.property)
  rw [nfwR, wm_append, wm_append, body_val, hc]
  simp only [maValue, Gap48.P10.normalValue, Gap48.P10.normalTokens, List.map_append, List.prod_append]
  congr 2
  · cases M.leadingT <;> simp [wm_nil, wm_cons, gm, Gap48.P10.tokenMatrix]
  · simp [Gap48.P10.tokenMatrix]

lemma normal_rep (reps : Representatives .hp) (C : CircuitWord) (hC : IsNormalWord .hp reps C) :
    ∃ M : NormalForm, C = nfwR reps M := by
  induction hC with
  | tail U hU =>
    exact ⟨⟨false, [], ⟨U, cliff_eq ▸ hU⟩⟩, by simp [nfwR]⟩
  | withT w hw hhead ih =>
    obtain ⟨M, rfl⟩ := ih
    cases hl : M.leadingT
    · exact ⟨⟨true, M.body, M.terminal⟩, by simp [nfwR, hl]⟩
    · exact absurd (by simp [nfwR, hl]) hhead
  | withHT w hw hhead ih =>
    obtain ⟨M, rfl⟩ := ih
    cases hl : M.leadingT
    · exact ⟨⟨false, false :: M.body, M.terminal⟩, by simp [nfwR, hl, syl]⟩
    · exact absurd (by simp [nfwR, hl]) hhead
  | withPHT w hw hhead ih =>
    obtain ⟨M, rfl⟩ := ih
    cases hl : M.leadingT
    · exact ⟨⟨false, true :: M.body, M.terminal⟩, by simp [nfwR, hl, syl]⟩
    · exact absurd (by simp [nfwR, hl]) hhead

lemma no_collision (reps : Representatives .hp) (C D : CircuitWord) (hC : IsNormalWord .hp reps C)
    (hD : IsNormalWord .hp reps D) (h : wm C = wm D) : C = D := by
  obtain ⟨M, rfl⟩ := normal_rep reps C hC
  obtain ⟨N, rfl⟩ := normal_rep reps D hD
  rw [nfwR_val, nfwR_val] at h
  rw [Gap48.P10.ma_uniqueness h]

end X4P12

open QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ
local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

theorem solution (reps : Representatives .hp) :
    (∃ C D : CircuitWord, IsNormalWord .hp reps C ∧ IsNormalWord .hp reps D ∧
      C ≠ D ∧ wordMatrix .hp C = wordMatrix .hp D) →
    ∃ E : CircuitWord, IsNormalWord .hp reps E ∧ 0 < wordTCount E ∧ wordMatrix .hp E = 1 := by
  rintro ⟨C, D, hC, hD, hne, h⟩
  exact absurd (X4P12.no_collision reps C D hC hD h) hne

end
