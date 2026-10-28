-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:55:25.497526+00:00
-- url     : https://prove2.me/submissions/0c7d3020-57bd-4b8e-9eb8-60b054d57aad

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

-- ===== P01Lib =====

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma rel {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitBMWRel P n a b) :
    presentationMap P n a = presentationMap P n b :=
  RingQuot.mkAlgHom_rel R h

lemma x_xi (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i false * X P n i true = 1 := by
  have := rel P n (NonsplitBMWRel.invL i hi); simpa [X, map_mul] using this

lemma xi_x (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i true * X P n i false = 1 := by
  have := rel P n (NonsplitBMWRel.invR i hi); simpa [X, map_mul] using this

lemma nearL (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    X P n i false * X P n j false * E P n i = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearL i j hi hj hd); simpa [X, E, map_mul] using this

lemma nearR (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n j * X P n i false * X P n j false = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearR i j hi hj hd); simpa [X, E, map_mul] using this

lemma tripleE (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n i * E P n j * E P n i = E P n i := by
  have := rel P n (NonsplitBMWRel.tripleE i j hi hj hd); simpa [E, map_mul] using this

lemma xeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    X P n i false * E P n j = E P n j * X P n i false := by
  have := rel P n (NonsplitBMWRel.xeFar i j hi hj hd); simpa [X, E, map_mul] using this

lemma xFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    X P n i false * X P n j false = X P n j false * X P n i false := by
  have := rel P n (NonsplitBMWRel.xFar i j hi hj hd); simpa [X, map_mul] using this

lemma braid (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) :
    X P n i false * X P n (i+1) false * X P n i false =
      X P n (i+1) false * X P n i false * X P n (i+1) false := by
  have := rel P n (NonsplitBMWRel.braid i hi); simpa [X, map_mul] using this

lemma ye (i : ℕ) (hi : 1 < i ∧ i < n) : Y P n false * E P n i = E P n i * Y P n false := by
  have := rel P n (NonsplitBMWRel.ye i hi); simpa [Y, E, map_mul] using this

lemma yx (i : ℕ) (hi : 1 < i ∧ i < n) : Y P n false * X P n i false = X P n i false * Y P n false := by
  have := rel P n (NonsplitBMWRel.yx i hi); simpa [Y, X, map_mul] using this

lemma skein (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
    X P n i false - X P n i true = skeinDelta P • (1 - E P n i) := by
  have h := rel P n (NonsplitBMWRel.skein i hi)
  simp only [map_sub, map_mul, map_one, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma xe (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i false * E P n i = (P.lam : R) • E P n i := by
  have h := rel P n (NonsplitBMWRel.xe i hi)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma ex (i : ℕ) (hi : 1 ≤ i ∧ i < n) : E P n i * X P n i false = (P.lam : R) • E P n i := by
  have h := rel P n (NonsplitBMWRel.ex i hi)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma sqE (i : ℕ) (hi : 1 ≤ i ∧ i < n) : E P n i * E P n i = loopZero P • E P n i := by
  have h := rel P n (NonsplitBMWRel.squareE i hi)
  simp only [map_pow, map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def, ← pow_two]; exact h

lemma affine (hn : 2 ≤ n) :
    X P n 1 false * Y P n false * X P n 1 false * Y P n false =
      Y P n false * X P n 1 false * Y P n false * X P n 1 false := by
  have := rel P n (NonsplitBMWRel.affine hn); simpa [X, Y, map_mul] using this

lemma unwrapL (hn : 2 ≤ n) :
    Y P n false * X P n 1 false * Y P n false * E P n 1 = (↑P.lam⁻¹ : R) • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.unwrapL hn)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma unwrapR (hn : 2 ≤ n) :
    E P n 1 * Y P n false * X P n 1 false * Y P n false = (↑P.lam⁻¹ : R) • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.unwrapR hn)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma yinv1 (hn : 0 < n) : Y P n false * Y P n true = 1 := by
  have := rel P n (NonsplitBMWRel.yInvL hn); simpa [Y, map_mul] using this

lemma yinv2 (hn : 0 < n) : Y P n true * Y P n false = 1 := by
  have := rel P n (NonsplitBMWRel.yInvR hn); simpa [Y, map_mul] using this

lemma cyc (hn : 0 < n) :
    Y P n false ^ k = ∑ j : Fin k, P.coeff j • Y P n false ^ j.val := by
  have h := rel P n (NonsplitBMWRel.cyclotomic hn)
  simp only [map_pow, map_sum, map_mul, AlgHom.commutes] at h
  simp only [Algebra.smul_def]; exact h

lemma loopr (m : Fin k) (hn : 2 ≤ n) :
    E P n 1 * Y P n false ^ m.val * E P n 1 = P.loop m • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.loop m hn)
  simp only [map_pow, map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma JM_succ (inv : Bool) (i : ℕ) (hi : 1 ≤ i) :
    JM P n inv (i+1) = X P n i inv * JM P n inv i * X P n i inv := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rfl

lemma jm_inv (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    JM P n false i * JM P n true i = 1 ∧ JM P n true i * JM P n false i = 1 := by
  induction i, hi using Nat.le_induction with
  | base => exact ⟨yinv1 P n (by omega), yinv2 P n (by omega)⟩
  | succ i hi ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [JM_succ P n false i hi, JM_succ P n true i hi]
    have a1 := x_xi P n i ⟨hi, by omega⟩
    have a2 := xi_x P n i ⟨hi, by omega⟩
    constructor
    · calc X P n i false * JM P n false i * X P n i false * (X P n i true * JM P n true i * X P n i true)
          = X P n i false * JM P n false i * (X P n i false * X P n i true) * JM P n true i * X P n i true := by
            simp only [mul_assoc]
        _ = 1 := by rw [a1, mul_one, mul_assoc (X P n i false), h1, mul_one, a1]
    · calc X P n i true * JM P n true i * X P n i true * (X P n i false * JM P n false i * X P n i false)
          = X P n i true * JM P n true i * (X P n i true * X P n i false) * JM P n false i * X P n i false := by
            simp only [mul_assoc]
        _ = 1 := by rw [a2, mul_one, mul_assoc (X P n i true), h2, mul_one, a2]

lemma jx_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j + 1 ≤ m → m < n →
    JM P n false j * X P n m false = X P n m false * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base => intro m hm hmn; exact yx P n m ⟨by omega, hmn⟩
  | succ j hj ih =>
    intro m hm hmn
    have h1 := ih m (by omega) hmn
    have h2 := xFar P n j m ⟨hj, by omega⟩ ⟨by omega, hmn⟩ (Or.inl (by omega))
    rw [JM_succ P n false j hj]
    exact ((Commute.mul_left (Commute.mul_left h2 h1) h2) : Commute _ _).eq

lemma je_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j + 1 ≤ m → m < n →
    JM P n false j * E P n m = E P n m * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base => intro m hm hmn; exact ye P n m ⟨by omega, hmn⟩
  | succ j hj ih =>
    intro m hm hmn
    have h1 := ih m (by omega) hmn
    have h2 := xeFar P n j m ⟨hj, by omega⟩ ⟨by omega, hmn⟩ (Or.inl (by omega))
    rw [JM_succ P n false j hj]
    exact ((Commute.mul_left (Commute.mul_left h2 h1) h2) : Commute _ _).eq

lemma jj_succ (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 ≤ n) :
    JM P n false j * JM P n false (j+1) = JM P n false (j+1) * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [JM_succ P n false 1 le_rfl]
    show Y P n false * (X P n 1 false * Y P n false * X P n 1 false) =
      X P n 1 false * Y P n false * X P n 1 false * Y P n false
    have := (affine P n (by omega)).symm
    simpa only [mul_assoc] using this
  | succ j hj ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false (j+1) (by omega), JM_succ P n false j hj] at *
    set a := X P n j false
    set b := X P n (j+1) false
    set c := JM P n false j
    have br0 : a * (b * a) = b * (a * b) := by
      have := braid P n j ⟨hj, by omega⟩; simpa only [mul_assoc] using this
    have br : ∀ z, a * (b * (a * z)) = b * (a * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc a, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n j hj (j+1) le_rfl (by omega), mul_assoc]
    have ih' : ∀ z, c * (a * (c * (a * z))) = a * (c * (a * (c * z))) := by
      intro z; have := congrArg (· * z) ih; simpa only [mul_assoc] using this
    simp only [mul_assoc]
    conv_lhs => rw [br (c * (a * b)), cb (a * (b * (c * (a * b)))), ← cb (a * b), ← br0,
      ih' (b * a), br (c * (a * (c * (b * a))))]
    conv_rhs => rw [br (c * a), cb (a * (b * (c * a))), ← cb a]

lemma jj_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j < m → m ≤ n →
    JM P n false j * JM P n false m = JM P n false m * JM P n false j := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro h; exact jj_succ P n j hj h
  | succ m hm ih =>
    intro hmn
    have h1 : Commute (JM P n false j) (JM P n false m) := ih (by omega)
    have h2 : Commute (JM P n false j) (X P n m false) := jx_comm P n j hj m hm (by omega)
    rw [JM_succ P n false m (by omega)]
    exact ((h2.mul_right h1).mul_right h2).eq

lemma p1dL (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    JM P n false a * X P n a false * JM P n false a * E P n a = (↑P.lam⁻¹ : R) • E P n a := by
  induction a, ha using Nat.le_induction with
  | base => exact unwrapL P n (by omega)
  | succ a ha ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false a ha]
    set x := X P n a false
    set b := X P n (a+1) false
    set c := JM P n false a
    set e := E P n a
    set f := E P n (a+1)
    have br0 : x * (b * x) = b * (x * b) := by
      have := braid P n a ⟨ha, han⟩; simpa only [mul_assoc] using this
    have br : ∀ z, x * (b * (x * z)) = b * (x * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc x, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n a ha (a+1) le_rfl han, mul_assoc]
    have nl1 : b * (x * f) = e * f := by
      have := nearL P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have nl2 : x * (b * (e * f)) = f * (e * f) := by
      have := nearL P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
      have := congrArg (· * f) this; simpa only [mul_assoc] using this
    have tr : f * (e * f) = f := by
      have := tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have ih' : c * (x * (c * (e * f))) = (↑P.lam⁻¹ : R) • (e * f) := by
      have := congrArg (· * f) ih; simpa only [mul_assoc, smul_mul_assoc] using this
    simp only [mul_assoc]
    rw [br (c * (x * f)), cb (x * (b * (c * (x * f)))), ← cb (x * f), nl1, ih',
      mul_smul_comm, mul_smul_comm, nl2, tr]

lemma p1dR (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    E P n a * JM P n false a * X P n a false * JM P n false a = (↑P.lam⁻¹ : R) • E P n a := by
  induction a, ha using Nat.le_induction with
  | base => exact unwrapR P n (by omega)
  | succ a ha ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false a ha]
    set x := X P n a false
    set b := X P n (a+1) false
    set c := JM P n false a
    set e := E P n a
    set f := E P n (a+1)
    have br0 : x * (b * x) = b * (x * b) := by
      have := braid P n a ⟨ha, han⟩; simpa only [mul_assoc] using this
    have br : ∀ z, x * (b * (x * z)) = b * (x * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc x, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n a ha (a+1) le_rfl han, mul_assoc]
    have nr1 : ∀ z, f * (x * (b * z)) = f * (e * z) := by
      intro z
      have := nearR P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
      have := congrArg (· * z) this; simpa only [mul_assoc] using this
    have nr2 : e * (b * x) = e * f := by
      have := nearR P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have tr : f * (e * f) = f := by
      have := tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have ih' : ∀ z, e * (c * (x * (c * z))) = (↑P.lam⁻¹ : R) • (e * z) := by
      intro z; have := congrArg (· * z) ih; simpa only [mul_assoc, smul_mul_assoc] using this
    simp only [mul_assoc]
    rw [br (c * x), cb (x * (b * (c * x))), ← cb x, nr1, ih', mul_smul_comm, nr2, tr]

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01

-- ===== P01Main =====

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X4P01

set_option linter.unusedSectionVars false

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma xsq (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    X P n i false ^ 2 = 1 + algebraMap R _ (skeinDelta P) * X P n i false -
      algebraMap R _ (skeinDelta P * (P.lam : R)) * E P n i := by
  have h := congrArg (· * X P n i false) (skein P n i ⟨hi, hin⟩)
  simp only [sub_mul, smul_mul_assoc, one_mul, xi_x P n i ⟨hi, hin⟩] at h
  rw [ex P n i ⟨hi, hin⟩] at h
  rw [pow_two, ← Algebra.smul_def, ← Algebra.smul_def, sub_eq_iff_eq_add.mp h, smul_sub,
    smul_smul]
  abel

lemma exi (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    E P n i * X P n i true = (↑P.lam⁻¹ : R) • E P n i := by
  have h := ex P n i ⟨hi, hin⟩
  have h2 : E P n i = (P.lam : R) • (E P n i * X P n i true) := by
    rw [← smul_mul_assoc, ← h, mul_assoc, x_xi P n i ⟨hi, hin⟩, mul_one]
  conv_rhs => rw [h2, smul_smul]
  simp

lemma exe (i j : ℕ) (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j) (hjn : j < n)
    (hd : i + 1 = j ∨ j + 1 = i) :
    E P n i * X P n j false * E P n i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i := by
  have nl := nearL P n i j ⟨hi, hin⟩ ⟨hj, hjn⟩ hd
  have h1 : X P n j false * E P n i = X P n i true * (E P n j * E P n i) := by
    calc X P n j false * E P n i = (X P n i true * X P n i false) * (X P n j false * E P n i) := by
          rw [xi_x P n i ⟨hi, hin⟩, one_mul]
      _ = X P n i true * (X P n i false * X P n j false * E P n i) := by simp only [mul_assoc]
      _ = _ := by rw [nl]
  rw [mul_assoc, h1, ← mul_assoc, exi P n i hi hin, smul_mul_assoc, ← mul_assoc,
    tripleE P n i j ⟨hi, hin⟩ ⟨hj, hjn⟩ hd, Algebra.smul_def]

lemma jm2 (i : ℕ) (hi : 1 ≤ i) :
    JM P n false (i+2) = X P n (i+1) false * (X P n i false * JM P n false i * X P n i false) *
      X P n (i+1) false := by
  rw [JM_succ P n false (i+1) (by omega), JM_succ P n false i hi]

lemma xj_far (i : ℕ) (hi : 1 ≤ i) : ∀ j, i + 2 ≤ j → j ≤ n →
    X P n i false * JM P n false j = JM P n false j * X P n i false := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hn
    rw [jm2 P n i hi]
    set a := X P n i false
    set b := X P n (i+1) false
    set c := JM P n false i
    have br0 : a * (b * a) = b * (a * b) := by
      have := braid P n i ⟨hi, by omega⟩; simpa only [mul_assoc] using this
    have br : ∀ z, a * (b * (a * z)) = b * (a * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc a, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n i hi (i+1) le_rfl (by omega), mul_assoc]
    simp only [mul_assoc]
    rw [br (c * (a * b)), ← cb (a * b), ← br0]
  | succ j hj ih =>
    intro hjn
    have h1 := ih (by omega)
    have h2 := xFar P n i j ⟨hi, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega))
    rw [JM_succ P n false j (by omega)]
    exact ((Commute.mul_right (Commute.mul_right h2 h1) h2) : Commute _ _).eq

lemma ej_far (i : ℕ) (hi : 1 ≤ i) : ∀ j, i + 2 ≤ j → j ≤ n →
    E P n i * JM P n false j = JM P n false j * E P n i := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hn
    rw [jm2 P n i hi]
    set a := X P n i false
    set b := X P n (i+1) false
    set c := JM P n false i
    set e := E P n i
    set f := E P n (i+1)
    have hI : 1 ≤ i ∧ i < n := ⟨hi, by omega⟩
    have hJ : 1 ≤ i + 1 ∧ i + 1 < n := ⟨by omega, by omega⟩
    have r1 : ∀ z, e * (b * (a * z)) = e * (f * z) := by
      intro z
      have := nearR P n (i+1) i hJ hI (Or.inr rfl)
      have := congrArg (· * z) this; simpa only [mul_assoc] using this
    have r2 : f * (a * b) = f * e := by
      have := nearR P n i (i+1) hI hJ (Or.inl rfl); simpa only [mul_assoc] using this
    have l1 : a * (b * e) = f * e := by
      have := nearL P n i (i+1) hI hJ (Or.inl rfl); simpa only [mul_assoc] using this
    have l2 : ∀ z, b * (a * (f * z)) = e * (f * z) := by
      intro z
      have := nearL P n (i+1) i hJ hI (Or.inr rfl)
      have := congrArg (· * z) this; simpa only [mul_assoc] using this
    have cf : ∀ z, c * (f * z) = f * (c * z) := by
      intro z; rw [← mul_assoc, je_comm P n i hi (i+1) le_rfl (by omega), mul_assoc]
    simp only [mul_assoc]
    rw [r1, ← cf, r2, l1, cf, l2]
  | succ j hj ih =>
    intro hjn
    have h1 := ih (by omega)
    have h2 := (xeFar P n j i ⟨by omega, by omega⟩ ⟨hi, by omega⟩ (Or.inr (by omega))).symm
    rw [JM_succ P n false j (by omega)]
    exact ((Commute.mul_right (Commute.mul_right h2 h1) h2) : Commute _ _).eq

lemma unit_shift {A : Type*} [Monoid A] (u v : Aˣ) (huv : Commute u v) (e : A)
    (h : e * (u : A) * v = e) (p : ℤ) : e * ↑(v ^ p) = e * ↑(u ^ (-p)) := by
  have h1 : e * ↑((u * v) ^ p) = e := by
    have h0 : e * ((u * v : Aˣ) : A) = e := by rw [Units.val_mul, ← mul_assoc, h]
    have h0' : e * (↑(u * v)⁻¹ : A) = e := by
      calc e * (↑(u * v)⁻¹ : A) = (e * ↑(u * v)) * ↑(u * v)⁻¹ := by rw [h0]
      _ = e := by rw [mul_assoc, Units.mul_inv, mul_one]
    induction p using Int.induction_on with
    | zero => simp
    | succ t ih =>
      rw [show (t:ℤ) + 1 = 1 + t by ring, zpow_add, zpow_one, Units.val_mul, ← mul_assoc, h0, ih]
    | pred t ih =>
      rw [show (-(t:ℤ) - 1) = -1 + -(t:ℤ) by ring, zpow_add, zpow_neg_one, Units.val_mul,
        ← mul_assoc, h0', ih]
  have hv : v ^ p = (u * v) ^ p * u ^ (-p) := by
    rw [huv.mul_zpow, mul_assoc, ← (huv.zpow_zpow (-p) p).eq, ← mul_assoc, ← zpow_add,
      add_neg_cancel, zpow_zero, one_mul]
  rw [hv, Units.val_mul, ← mul_assoc, h1]

lemma unit_shift' {A : Type*} [Monoid A] (u v : Aˣ) (huv : Commute u v) (e : A)
    (h : (u : A) * v * e = e) (p : ℤ) : ↑(v ^ p) * e = ↑(u ^ (-p)) * e := by
  have h1 : ↑((u * v) ^ p) * e = e := by
    have h0 : ((u * v : Aˣ) : A) * e = e := by rw [Units.val_mul, h]
    have h0' : (↑(u * v)⁻¹ : A) * e = e := by
      calc (↑(u * v)⁻¹ : A) * e = ↑(u * v)⁻¹ * (↑(u * v) * e) := by rw [h0]
      _ = e := by rw [← mul_assoc, Units.inv_mul, one_mul]
    induction p using Int.induction_on with
    | zero => simp
    | succ t ih => rw [zpow_add_one, Units.val_mul, mul_assoc, h0, ih]
    | pred t ih => rw [zpow_sub_one, Units.val_mul, mul_assoc, h0', ih]
  have hv : v ^ p = u ^ (-p) * (u * v) ^ p := by
    rw [huv.mul_zpow, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
  rw [hv, Units.val_mul, mul_assoc, h1]

end X4P01
end QAlgorithms.Papers.Independent.Gap48.P01

-- ===== P01Sol =====

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X4P01

set_option linter.unusedSectionVars false

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

def uu (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) : (NonsplitBMW P n)ˣ :=
  ⟨JM P n false i, JM P n true i, (jm_inv P n i h.1 h.2).1, (jm_inv P n i h.1 h.2).2⟩

lemma JPower_uu (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) (p : ℤ) :
    JPower P n i p = (↑(uu P n i h ^ p) : NonsplitBMW P n) := by
  unfold JPower
  split_ifs with hp
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    simp [zpow_natCast, Units.val_pow_eq_pow_val, uu]
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, p = -(q:ℤ) := ⟨(-p).toNat, by omega⟩
    subst hq
    simp [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, uu]

lemma m9L (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    JM P n false a * JM P n false (a+1) * E P n a = E P n a := by
  rw [JM_succ P n false a ha]
  have p := p1dL P n a ha han
  simp only [mul_assoc] at p ⊢
  rw [xe P n a ⟨ha, han⟩, mul_smul_comm, mul_smul_comm, mul_smul_comm, p, smul_smul,
    Units.mul_inv, one_smul]

lemma m9R (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    E P n a * JM P n false a * JM P n false (a+1) = E P n a := by
  rw [JM_succ P n false a ha]
  have p := congrArg (· * X P n a false) (p1dR P n a ha han)
  simp only [mul_assoc, smul_mul_assoc] at p ⊢
  rw [p, ex P n a ⟨ha, han⟩, smul_smul, Units.inv_mul, one_smul]

lemma uu_comm (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    Commute (uu P n a ⟨ha, by omega⟩) (uu P n (a+1) ⟨by omega, by omega⟩) := by
  apply Units.ext
  exact jj_comm P n a ha (a+1) (by omega) (by omega)

theorem main :
    (∀ i, 1 ≤ i → i < n → X P n i false ^ 2 =
      1 + algebraMap R _ (skeinDelta P) * X P n i false -
        algebraMap R _ (skeinDelta P * (P.lam : R)) * E P n i) ∧
    (∀ i j, 1 ≤ i → i < n → 1 ≤ j → j < n → (i+1=j ∨ j+1=i) →
      E P n i * X P n j false * E P n i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i) ∧
    (∀ i j, 1 ≤ i → i < n → 1 ≤ j → j ≤ n → i ≠ j → i+1 ≠ j →
      X P n i false * JM P n false j = JM P n false j * X P n i false ∧
      E P n i * JM P n false j = JM P n false j * E P n i) ∧
    (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      JM P n false i * JM P n false j = JM P n false j * JM P n false i) ∧
    (∀ i, 1 ≤ i → i < n →
      JM P n false i * X P n i false * JM P n false i * E P n i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i ∧
      E P n i * JM P n false i * X P n i false * JM P n false i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i) ∧
    (∀ i, 1 ≤ i → i < n → ∀ p : ℤ,
      E P n i * JPower P n (i+1) p = E P n i * JPower P n i (-p) ∧
      JPower P n (i+1) p * E P n i = JPower P n i (-p) * E P n i) := by
  refine ⟨fun i hi hin => xsq P n i hi hin, fun i j hi hin hj hjn hd => exe P n i j hi hin hj hjn hd,
    ?_, ?_, ?_, ?_⟩
  · intro i j hi hin hj hjn hij hij'
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨xj_far P n i hi j (by omega) hjn, ej_far P n i hi j (by omega) hjn⟩
    · exact ⟨(jx_comm P n j hj i (by omega) hin).symm, (je_comm P n j hj i (by omega) hin).symm⟩
  · intro i j hi hin hj hjn
    rcases lt_trichotomy i j with h | rfl | h
    · exact jj_comm P n i hi j h hjn
    · rfl
    · exact (jj_comm P n j hj i h hin).symm
  · intro i hi hin
    exact ⟨by rw [p1dL P n i hi hin, Algebra.smul_def], by rw [p1dR P n i hi hin, Algebra.smul_def]⟩
  · intro i hi hin p
    rw [JPower_uu P n (i+1) ⟨by omega, by omega⟩, JPower_uu P n i ⟨hi, by omega⟩]
    refine ⟨unit_shift _ _ (uu_comm P n i hi hin) _ ?_ p, unit_shift' _ _ (uu_comm P n i hi hin) _ ?_ p⟩
    · exact m9R P n i hi hin
    · exact m9L P n i hi hin

end X4P01
end QAlgorithms.Papers.Independent.Gap48.P01

open QAlgorithms.Papers.Independent.Gap48.P01 in
theorem solution {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :
    (∀ i, 1 ≤ i → i < n → X P n i false ^ 2 =
      1 + algebraMap R _ (skeinDelta P) * X P n i false -
        algebraMap R _ (skeinDelta P * (P.lam : R)) * E P n i) ∧
    (∀ i j, 1 ≤ i → i < n → 1 ≤ j → j < n → (i+1=j ∨ j+1=i) →
      E P n i * X P n j false * E P n i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i) ∧
    (∀ i j, 1 ≤ i → i < n → 1 ≤ j → j ≤ n → i ≠ j → i+1 ≠ j →
      X P n i false * JM P n false j = JM P n false j * X P n i false ∧
      E P n i * JM P n false j = JM P n false j * E P n i) ∧
    (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      JM P n false i * JM P n false j = JM P n false j * JM P n false i) ∧
    (∀ i, 1 ≤ i → i < n →
      JM P n false i * X P n i false * JM P n false i * E P n i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i ∧
      E P n i * JM P n false i * X P n i false * JM P n false i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i) ∧
    (∀ i, 1 ≤ i → i < n → ∀ p : ℤ,
      E P n i * JPower P n (i+1) p = E P n i * JPower P n i (-p) ∧
      JPower P n (i+1) p * E P n i = JPower P n i (-p) * E P n i) :=
  X4P01.main P n
