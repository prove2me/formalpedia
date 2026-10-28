-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.r_basis_unique_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:41:33.112239+00:00
-- url     : https://prove2.me/submissions/55098348-c8de-4183-8a83-419cd9071a6d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_uniqueness
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_tcount_nonincrease
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_clifford_three_cosets
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_five_coset_identities

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

noncomputable section

namespace X4P12

open QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Gap48.P12 (CircuitLetter CircuitWord wordTCount IsNormalWord Representatives
  chronologicalInstructions)
open Gap48.P10 (Clifford NormalForm maValue normalValue normalTokens tokenMatrix smallSet cliffordSet
  cliffordWordMatrix CliffordLetter cliffordLetterMatrix cliffordOfWord cliffordH cliffordSH scalarOmega
  nonidentityTransversal five_coset_identities)
open scoped Pointwise

local notation "Mat" => Matrix Bool Bool ℂ
local notation "ω" => QAlgorithms.gateT true true
local notation "TT" => QAlgorithms.gateT
local notation "HH" => QAlgorithms.hadamard
local notation "SS" => QAlgorithms.phaseS
local notation "XX" => QAlgorithms.pauliX

def RR : Mat := SS * SS * HH

lemma om_sq : ω * ω = Complex.I := by
  rw [om_eq]
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0)
  field_simp
  ring_nf
  rw [Complex.I_sq]
  linear_combination (-(Complex.I)) * hs

lemma om_T : TT true true = ω := rfl

lemma RX : RR = HH * XX := by
  ext i j
  cases i <;> cases j <;> simp [RR, Matrix.mul_apply, QAlgorithms.hadamard, QAlgorithms.phaseS,
    QAlgorithms.pauliX, Matrix.diagonal]

lemma XX2 : XX * XX = 1 := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_apply, QAlgorithms.pauliX, Matrix.one_apply]

lemma S4 : SS * SS * SS * SS = 1 := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_apply, QAlgorithms.phaseS, Matrix.diagonal, Matrix.one_apply]

def c0 : Mat := scalarOmega * SS * SS * SS * XX

lemma XT : XX * TT = TT * c0 := by
  have h := om_sq
  ext i j
  cases i <;> cases j <;> simp [c0, Matrix.mul_apply, QAlgorithms.gateT, QAlgorithms.phaseS,
    QAlgorithms.pauliX, Matrix.diagonal, scalarOmega] at h ⊢
  linear_combination (-Complex.I ^ 3) * h + (1 - Complex.I ^ 2) * Complex.I_sq

lemma HRX : HH = RR * XX := by rw [RX, Matrix.mul_assoc, XX2, Matrix.mul_one]

lemma small_mul {x y : Mat} (hx : x ∈ smallSet) (hy : y ∈ smallSet) : x * y ∈ smallSet := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact ⟨u ++ v, by simp [List.prod_append]⟩

lemma S_small : SS ∈ smallSet := ⟨[.s], by simp [Gap48.P10.smallLetterMatrix]⟩
lemma X_small : XX ∈ smallSet := ⟨[.x], by simp [Gap48.P10.smallLetterMatrix]⟩
lemma W_small : scalarOmega ∈ smallSet := ⟨[.omega], by simp [Gap48.P10.smallLetterMatrix]⟩

lemma c0_small : c0 ∈ smallSet :=
  small_mul (small_mul (small_mul (small_mul W_small S_small) S_small) S_small) X_small

lemma small_cliff {x : Mat} (hx : x ∈ smallSet) : x ∈ cliffordSet := by
  have := five_coset_identities.1
  rw [this]
  have := Set.mul_mem_mul (show (1 : Mat) ∈ Gap48.P10.transversal from Set.mem_insert _ _) hx
  rwa [one_mul] at this

def cR : Clifford := cliffordOfWord [.s, .s, .h]
def cSR : Clifford := cliffordOfWord [.s, .s, .s, .h]

lemma cR_val : cR.val = RR := by
  simp [cR, RR, cliffordOfWord, cliffordWordMatrix, cliffordLetterMatrix, Matrix.mul_assoc]
lemma cSR_val : cSR.val = SS * RR := by
  simp [cSR, RR, cliffordOfWord, cliffordWordMatrix, cliffordLetterMatrix, Matrix.mul_assoc]

def ofSmall (x : Mat) (hx : x ∈ smallSet) : Clifford := ⟨x, small_cliff hx⟩

def cmul (C D : Clifford) : Clifford := ⟨C.val * D.val, by
  obtain ⟨u, hu⟩ := C.property
  obtain ⟨v, hv⟩ := D.property
  exact ⟨u ++ v, by simp [cliffordWordMatrix, List.prod_append] at hu hv ⊢; rw [hu, hv]⟩⟩

lemma nv_split (a b : Clifford) (lead : Bool) (body : List Bool) (C : Clifford) :
    normalValue a b ⟨lead, body, C⟩ = (if lead then TT else 1) * normalValue a b ⟨false, body, C⟩ := by
  cases lead <;> simp [normalValue, normalTokens, tokenMatrix]

lemma nv_cons (a b : Clifford) (q : Bool) (body : List Bool) (C : Clifford) :
    normalValue a b ⟨false, q :: body, C⟩ = (if q then b else a).val * TT * normalValue a b ⟨false, body, C⟩ := by
  simp [normalValue, normalTokens, tokenMatrix, Matrix.mul_assoc]

lemma nv_nil (a b : Clifford) (C : Clifford) : normalValue a b ⟨false, [], C⟩ = C.val := by
  simp [normalValue, normalTokens, tokenMatrix]

def hq (q : Bool) : Mat := if q then SS * HH else HH
def rq (q : Bool) : Mat := if q then SS * RR else RR

lemma x_T (q : Bool) : (if q then cSR else cR).val * TT = hq q * TT * c0 := by
  cases q
  · simp only [Bool.false_eq_true, if_false, hq, cR_val, RX, Matrix.mul_assoc, XT]
  · simp only [if_true, hq, cSR_val, RX, Matrix.mul_assoc, XT]

lemma hq_val (q : Bool) : (if q then cliffordSH else cliffordH).val = hq q := by
  cases q <;> simp [hq, cliffordSH, cliffordH, cliffordOfWord, cliffordWordMatrix, cliffordLetterMatrix]

lemma rq_val (q : Bool) : (if q then cSR else cR).val = rq q := by
  cases q <;> simp [rq, cR_val, cSR_val]

/-- R-form → MA-form carry transport -/
lemma phi (body : List Bool) : ∀ (s : Mat), s ∈ smallSet → ∀ C : Clifford, ∃ body' C',
    s * normalValue cR cSR ⟨false, body, C⟩ = normalValue cliffordH cliffordSH ⟨false, body', C'⟩ ∧
    body'.length = body.length := by
  induction body with
  | nil =>
    intro s hs C
    exact ⟨[], cmul (ofSmall s hs) C, by rw [nv_nil, nv_nil]; rfl, rfl⟩
  | cons q rest ih =>
    intro s hs C
    have h1 : s * hq q ∈ smallSet * nonidentityTransversal :=
      Set.mul_mem_mul hs (by cases q <;> simp [hq, nonidentityTransversal])
    have h1' := five_coset_identities.2.2.1 h1
    obtain ⟨h', hh', s1, hs1, e1⟩ := h1'
    have h2 : s1 * TT ∈ smallSet * {TT} := Set.mul_mem_mul hs1 rfl
    rw [five_coset_identities.2.2.2.1] at h2
    obtain ⟨t, ht, s2, hs2, e2⟩ := h2
    rw [Set.mem_singleton_iff] at ht; subst ht
    obtain ⟨body', C', e3, hl⟩ := ih (s2 * c0) (small_mul hs2 c0_small) C
    have hh'' : ∃ q', h' = hq q' := by
      simp only [nonidentityTransversal, Set.mem_insert_iff, Set.mem_singleton_iff] at hh'
      rcases hh' with e | e
      · exact ⟨false, e⟩
      · exact ⟨true, e⟩
    obtain ⟨q', rfl⟩ := hh''
    refine ⟨q' :: body', C', ?_, by simp [hl]⟩
    have e2' : TT * s2 = s1 * TT := e2
    rw [nv_cons, nv_cons, hq_val, ← e3, x_T]
    set R := normalValue cR cSR ⟨false, rest, C⟩
    calc s * (hq q * TT * c0 * R) = (s * hq q) * TT * (c0 * R) := by simp only [Matrix.mul_assoc]
      _ = hq q' * (s1 * TT) * (c0 * R) := by rw [← e1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← e2']; simp only [Matrix.mul_assoc]

lemma toMA (M : NormalForm) : ∃ N : NormalForm, maValue N = normalValue cR cSR M ∧
    N.leadingT = M.leadingT ∧ N.body.length = M.body.length ∧ N.body.head? = M.body.head? := by
  obtain ⟨lead, body, C⟩ := M
  cases body with
  | nil =>
    exact ⟨⟨lead, [], C⟩, by rw [maValue, nv_split, nv_nil, nv_split, nv_nil], rfl, rfl, rfl⟩
  | cons q rest =>
    obtain ⟨body', C', e, hl⟩ := phi rest c0 c0_small C
    refine ⟨⟨lead, q :: body', C'⟩, ?_, rfl, by simp [hl], rfl⟩
    show normalValue cliffordH cliffordSH _ = _
    rw [nv_split cliffordH cliffordSH lead, nv_cons cliffordH cliffordSH, nv_split cR cSR lead,
      nv_cons cR cSR, hq_val, x_T, ← e]
    simp only [Matrix.mul_assoc]

/-- MA-form → R-form carry transport -/
lemma psi (body : List Bool) : ∀ (s : Mat), s ∈ smallSet → ∀ C : Clifford, ∃ body' C',
    s * normalValue cliffordH cliffordSH ⟨false, body, C⟩ = normalValue cR cSR ⟨false, body', C'⟩ := by
  induction body with
  | nil =>
    intro s hs C
    exact ⟨[], cmul (ofSmall s hs) C, by rw [nv_nil, nv_nil]; rfl⟩
  | cons q rest ih =>
    intro s hs C
    have h1 : s * hq q ∈ smallSet * nonidentityTransversal :=
      Set.mul_mem_mul hs (by cases q <;> simp [hq, nonidentityTransversal])
    obtain ⟨h', hh', s1, hs1, e1⟩ := five_coset_identities.2.2.1 h1
    have hh'' : ∃ q', h' = rq q' * XX := by
      simp only [nonidentityTransversal, Set.mem_insert_iff, Set.mem_singleton_iff] at hh'
      rcases hh' with e | e
      · exact ⟨false, by simp [e, rq, HRX]⟩
      · exact ⟨true, by simp [e, rq, HRX, Matrix.mul_assoc]⟩
    obtain ⟨q', rfl⟩ := hh''
    have h2 : (XX * s1) * TT ∈ smallSet * {TT} := Set.mul_mem_mul (small_mul X_small hs1) rfl
    rw [five_coset_identities.2.2.2.1] at h2
    obtain ⟨t, ht, s2, hs2, e2⟩ := h2
    rw [Set.mem_singleton_iff] at ht; subst ht
    obtain ⟨body', C', e3⟩ := ih s2 hs2 C
    refine ⟨q' :: body', C', ?_⟩
    have e2' : TT * s2 = XX * s1 * TT := e2
    rw [nv_cons, nv_cons, hq_val, rq_val, ← e3]
    set R := normalValue cliffordH cliffordSH ⟨false, rest, C⟩
    calc s * (hq q * TT * R) = (s * hq q) * TT * R := by simp only [Matrix.mul_assoc]
      _ = rq q' * (XX * s1 * TT) * R := by rw [← e1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← e2']; simp only [Matrix.mul_assoc]

lemma toR (M : NormalForm) : ∃ N : NormalForm, normalValue cR cSR N = maValue M := by
  obtain ⟨lead, body, C⟩ := M
  obtain ⟨body', C', e⟩ := psi body 1 ⟨[], rfl⟩ C
  refine ⟨⟨lead, body', C'⟩, ?_⟩
  rw [maValue, nv_split cR cSR lead, nv_split cliffordH cliffordSH lead, ← e, Matrix.one_mul]

lemma omega_eq : Complex.exp (Complex.I * Real.pi / 4) =
    ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ := by
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  apply Complex.ext <;> simp

lemma s2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma s2c : ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  have h : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp; rw [Real.sq_sqrt (by norm_num)]
  rw [← h]; push_cast; rfl

lemma unit_T : TT ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h : (Real.sqrt 2 / 2) ^ 2 * 2 = 1 := by
    rw [div_pow, s2sq]; norm_num
  ext a b
  cases a <;> cases b <;>
    simp [QAlgorithms.gateT, omega_eq, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal,
      Matrix.star_apply] <;> apply Complex.ext <;> simp <;> nlinarith [h]

lemma unit_of (x : ℝ) (hx : x ^ 2 * 2 = 1) :
    (Matrix.of fun a b : Bool => if a && b then -((x : ℂ)) else (x : ℂ)) ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Complex.conj_ofReal] <;>
    apply Complex.ext <;> simp <;> nlinarith [hx]

lemma unit_H : HH ∈ Matrix.unitaryGroup Bool ℂ := by
  have e : QAlgorithms.hadamard = Matrix.of fun a b : Bool =>
      if a && b then -(((Real.sqrt 2 / 2 : ℝ) : ℂ)) else ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    unfold QAlgorithms.hadamard; rw [s2c]
  rw [e]
  apply unit_of
  rw [div_pow, s2sq]; norm_num

lemma unit_S : SS ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  cases a <;> cases b <;>
    simp [QAlgorithms.phaseS, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal, Matrix.star_apply]

lemma unit_W : scalarOmega ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h : (Real.sqrt 2 / 2) ^ 2 * 2 = 1 := by
    rw [div_pow, s2sq]; norm_num
  ext a b
  cases a <;> cases b <;>
    simp [scalarOmega, QAlgorithms.gateT, omega_eq, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal,
      Matrix.star_apply, Matrix.one_apply] <;> apply Complex.ext <;> simp <;> nlinarith [h]

lemma unit_word (w : List CliffordLetter) : cliffordWordMatrix w ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold cliffordWordMatrix
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Submonoid.mul_mem _ ?_ ih
    cases a
    · exact unit_H
    · exact unit_S
    · exact unit_W

lemma unit_cliff (C : Clifford) : C.val ∈ Matrix.unitaryGroup Bool ℂ := by
  obtain ⟨w, hw⟩ := C.property
  rw [← hw]; exact unit_word w

lemma cancel {X A B : Mat} (hX : X ∈ Matrix.unitaryGroup Bool ℂ) (h : X * A = X * B) : A = B := by
  have hXX : star X * X = 1 := Matrix.mem_unitaryGroup_iff'.1 hX
  calc A = star X * X * A := by rw [hXX, Matrix.one_mul]
    _ = star X * X * B := by rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]
    _ = B := by rw [hXX, Matrix.one_mul]

lemma unit_xT (q : Bool) : (if q then cSR else cR).val * TT ∈ Matrix.unitaryGroup Bool ℂ :=
  (Matrix.unitaryGroup Bool ℂ).mul_mem (unit_cliff _) unit_T

lemma unit_lead (lead : Bool) : (if lead then TT else 1 : Mat) ∈ Matrix.unitaryGroup Bool ℂ := by
  cases lead
  · exact (Matrix.unitaryGroup Bool ℂ).one_mem
  · exact unit_T

theorem r_inj (body : List Bool) : ∀ (lead lead' : Bool) (body' : List Bool) (C C' : Clifford),
    normalValue cR cSR ⟨lead, body, C⟩ = normalValue cR cSR ⟨lead', body', C'⟩ →
    lead = lead' ∧ body = body' ∧ C = C' := by
  induction body with
  | nil =>
    intro lead lead' body' C C' h
    obtain ⟨N, hN, l1, b1, _⟩ := toMA ⟨lead, [], C⟩
    obtain ⟨N', hN', l1', b1', _⟩ := toMA ⟨lead', body', C'⟩
    have := Gap48.P10.ma_uniqueness (hN.trans (h.trans hN'.symm))
    subst this
    have hl : lead = lead' := l1.symm.trans l1'
    subst hl
    have hb : body' = [] := by
      rw [← List.length_eq_zero_iff, ← b1', b1]; rfl
    subst hb
    rw [nv_split cR cSR lead [] C, nv_split cR cSR lead [] C'] at h
    have h' := cancel (unit_lead lead) h
    rw [nv_nil, nv_nil] at h'
    exact ⟨rfl, rfl, Subtype.ext h'⟩
  | cons q rest ih =>
    intro lead lead' body' C C' h
    obtain ⟨N, hN, l1, b1, c1⟩ := toMA ⟨lead, q :: rest, C⟩
    obtain ⟨N', hN', l1', b1', c1'⟩ := toMA ⟨lead', body', C'⟩
    have := Gap48.P10.ma_uniqueness (hN.trans (h.trans hN'.symm))
    subst this
    have hl : lead = lead' := l1.symm.trans l1'
    subst hl
    cases body' with
    | nil => rw [b1'] at b1; simp at b1
    | cons q' rest' =>
      have hq : q = q' := by have := c1.symm.trans c1'; simpa using this
      subst hq
      rw [nv_split cR cSR lead (q :: rest) C, nv_split cR cSR lead (q :: rest') C'] at h
      have h' := cancel (unit_lead lead) h
      rw [nv_cons, nv_cons, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (_ : Mat) TT,
        ← Matrix.mul_assoc (_ : Mat) TT] at h'
      have h'' := cancel (unit_xT q) h'
      obtain ⟨-, e1, e2⟩ := ih false false rest' C C' h''
      exact ⟨rfl, by rw [e1], e2⟩

end X4P12

noncomputable section

namespace X4P12

open QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Gap48.P12 (CircuitLetter CircuitWord wordTCount IsNormalWord Representatives
  chronologicalInstructions)
open Gap48.P10 (Clifford NormalForm maValue normalValue normalTokens tokenMatrix smallSet cliffordSet
  cliffordWordMatrix CliffordLetter cliffordLetterMatrix cliffordOfWord cliffordH cliffordSH scalarOmega
  Input inputWordMatrix inputTCount)

local notation "Mat" => Matrix Bool Bool ℂ
local notation "TT" => QAlgorithms.gateT
local notation "HH" => QAlgorithms.hadamard
local notation "SS" => QAlgorithms.phaseS

def gmR : CircuitLetter → Mat
  | .h => RR
  | .p => SS
  | .t => TT

def wmR (w : CircuitWord) : Mat := Next46.P21.wordMatrix (chronologicalInstructions .rp w)

lemma wmR_nil : wmR [] = 1 := rfl

lemma wmR_cons (a : CircuitLetter) (w : CircuitWord) : wmR (a :: w) = gmR a * wmR w := by
  unfold wmR chronologicalInstructions
  simp only [List.reverse_cons, List.flatMap_append, Next46.P21.wordMatrix, List.map_append,
    List.reverse_append, List.prod_append]
  congr 1
  cases a <;> simp [gmR, RR, Next46.P21.letterMatrix, Matrix.mul_assoc]

lemma wmR_append (u v : CircuitWord) : wmR (u ++ v) = wmR u * wmR v := by
  induction u with
  | nil => simp [wmR_nil]
  | cons a u ih => rw [List.cons_append, wmR_cons, wmR_cons, ih, Matrix.mul_assoc]

def trL : CircuitLetter → CircuitWord
  | .h => [.p, .p, .h]
  | .p => [.p]
  | .t => [.t]

def tr (w : CircuitWord) : CircuitWord := w.flatMap trL

lemma tr_val (w : CircuitWord) : wmR (tr w) = wm w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [tr, List.flatMap_cons, wmR_append, ← tr, ih, wm_cons]
    congr 1
    cases a
    · simp only [trL, wmR_cons, wmR_nil, gmR, gm, RR, Matrix.mul_one]
      simp only [← Matrix.mul_assoc]
      rw [S4, Matrix.one_mul]
    · simp [trL, wmR_cons, wmR_nil, gmR, gm]
    · simp [trL, wmR_cons, wmR_nil, gmR, gm]

lemma tr_tc (w : CircuitWord) : wordTCount (tr w) = wordTCount w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [tr, List.flatMap_cons, tc_append, ← tr, ih]
    cases a <;> simp [trL, wordTCount] <;> omega

def backR : CircuitLetter → List CliffordLetter
  | .h => [.s, .s, .h]
  | .p => [.s]
  | .t => []

lemma backR_val (w : CircuitWord) (hw : CircuitLetter.t ∉ w) :
    cliffordWordMatrix (w.flatMap backR) = wmR w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.mem_cons, not_or] at hw
    rw [List.flatMap_cons, wmR_cons, ← ih hw.2]
    simp only [cliffordWordMatrix, List.map_append, List.prod_append]
    congr 1
    cases a
    · simp [backR, gmR, RR, cliffordLetterMatrix, Matrix.mul_assoc]
    · simp [backR, gmR, cliffordLetterMatrix]
    · exact absurd rfl hw.1

lemma cliffR_sub {U : Mat} (hU : U ∈ Gap48.P12.cliffordSet .rp) : U ∈ cliffordSet := by
  obtain ⟨w, hw, rfl⟩ := hU
  exact ⟨w.flatMap backR, backR_val w hw⟩

lemma cliffR_sup (C : Clifford) : C.val ∈ Gap48.P12.cliffordSet .rp := by
  refine ⟨tr (cw C), ?_, (tr_val _).trans (cw_val C)⟩
  have := tr_tc (cw C)
  rw [cw_tc] at this
  simpa [Gap48.P12.IsCliffordWord, wordTCount, List.count_eq_zero] using this

def toIR : CircuitLetter → Input
  | .h => .clifford cR
  | .p => .clifford cS
  | .t => .t

lemma iwmR (w : CircuitWord) : inputWordMatrix (w.map toIR) = wmR w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.map_cons, inputWordMatrix, List.map_cons, List.prod_cons, ← inputWordMatrix, ih, wmR_cons]
    congr 1
    cases a <;> simp [toIR, gmR, Gap48.P10.inputMatrix, cR_val, cS, cliffordOfWord, cliffordWordMatrix,
      cliffordLetterMatrix]

def nfwRR (reps : Representatives .rp) (M : NormalForm) : CircuitWord :=
  (if M.leadingT then [.t] else []) ++ M.body.flatMap syl ++ reps.word M.terminal.val

lemma bodyR_val (reps : Representatives .rp) (b : List Bool) (V : Clifford) :
    wmR (b.flatMap syl ++ reps.word V.val) = normalValue cR cSR ⟨false, b, V⟩ := by
  induction b with
  | nil =>
    rw [List.flatMap_nil, List.nil_append, nv_nil]
    exact reps.computes _ (cliffR_sup V)
  | cons q b ih =>
    rw [List.flatMap_cons, List.append_assoc, wmR_append, ih, nv_cons]
    cases q
    · simp [syl, wmR_cons, wmR_nil, gmR, cR_val, Matrix.mul_assoc]
    · simp [syl, wmR_cons, wmR_nil, gmR, cSR_val, Matrix.mul_assoc]

lemma nfwRR_val (reps : Representatives .rp) (M : NormalForm) : wmR (nfwRR reps M) = normalValue cR cSR M := by
  obtain ⟨lead, b, V⟩ := M
  rw [nfwRR, List.append_assoc, wmR_append, bodyR_val, nv_split cR cSR lead]
  cases lead <;> simp [wmR_cons, wmR_nil, gmR]

lemma normal_repR (reps : Representatives .rp) (C : CircuitWord) (hC : IsNormalWord .rp reps C) :
    ∃ M : NormalForm, C = nfwRR reps M := by
  induction hC with
  | tail U hU =>
    exact ⟨⟨false, [], ⟨U, cliffR_sub hU⟩⟩, by simp [nfwRR]⟩
  | withT w hw hhead ih =>
    obtain ⟨M, rfl⟩ := ih
    cases hl : M.leadingT
    · exact ⟨⟨true, M.body, M.terminal⟩, by simp [nfwRR, hl]⟩
    · exact absurd (by simp [nfwRR, hl]) hhead
  | withHT w hw hhead ih =>
    obtain ⟨M, rfl⟩ := ih
    cases hl : M.leadingT
    · exact ⟨⟨false, false :: M.body, M.terminal⟩, by simp [nfwRR, hl, syl]⟩
    · exact absurd (by simp [nfwRR, hl]) hhead
  | withPHT w hw hhead ih =>
    obtain ⟨M, rfl⟩ := ih
    cases hl : M.leadingT
    · exact ⟨⟨false, true :: M.body, M.terminal⟩, by simp [nfwRR, hl, syl]⟩
    · exact absurd (by simp [nfwRR, hl]) hhead

lemma body_normal (reps : Representatives .rp) (b : List Bool) (V : Clifford) :
    IsNormalWord .rp reps (b.flatMap syl ++ reps.word V.val) ∧
      (b.flatMap syl ++ reps.word V.val).head? ≠ some .t := by
  induction b with
  | nil =>
    refine ⟨IsNormalWord.tail _ (cliffR_sup V), ?_⟩
    have h := reps.clifford _ (cliffR_sup V)
    simp only [List.flatMap_nil, List.nil_append]
    intro e
    exact h (List.mem_of_head? e)
  | cons q b ih =>
    rw [List.flatMap_cons, List.append_assoc]
    cases q
    · exact ⟨IsNormalWord.withHT _ ih.1 ih.2, by simp [syl]⟩
    · exact ⟨IsNormalWord.withPHT _ ih.1 ih.2, by simp [syl]⟩

lemma nfwRR_normal (reps : Representatives .rp) (M : NormalForm) : IsNormalWord .rp reps (nfwRR reps M) := by
  obtain ⟨lead, b, V⟩ := M
  have h := body_normal reps b V
  rw [nfwRR, List.append_assoc]
  cases lead
  · simpa using h.1
  · exact IsNormalWord.withT _ h.1 h.2

theorem r_unique (reps : Representatives .rp) (C : CircuitWord) :
    ∃! D : CircuitWord, IsNormalWord .rp reps D ∧ wmR D = wmR C := by
  obtain ⟨M, hM, -⟩ := Gap48.P10.ma_tcount_nonincrease (wmR C) (inputTCount (C.map toIR))
    ⟨C.map toIR, iwmR C, rfl⟩
  obtain ⟨N, hN⟩ := toR M
  refine ⟨nfwRR reps N, ⟨nfwRR_normal reps N, by rw [nfwRR_val, hN, hM]⟩, ?_⟩
  rintro D ⟨hD, e⟩
  obtain ⟨N', rfl⟩ := normal_repR reps D hD
  rw [nfwRR_val, ← hM, ← hN] at e
  obtain ⟨l, b, V⟩ := N
  obtain ⟨l', b', V'⟩ := N'
  obtain ⟨e1, e2, e3⟩ := r_inj b' l' l b V' V e
  subst e1 e2 e3
  rfl

end X4P12

open QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ
local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

theorem solution (reps : Representatives .rp) (C : CircuitWord) :
    ∃! D : CircuitWord, IsNormalWord .rp reps D ∧ wordMatrix .rp D = wordMatrix .rp C :=
  X4P12.r_unique reps C

end
