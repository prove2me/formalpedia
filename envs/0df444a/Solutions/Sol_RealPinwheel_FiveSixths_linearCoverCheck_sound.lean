-- Prove2me | solution 1 for RealPinwheel.FiveSixths.linearCoverCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:31:29.969472+00:00
-- url     : https://prove2.me/submissions/8b35528e-8198-426f-a1d7-0125ee8d06fe

import Definitions.Def_RealPinwheel_FiveSixths_LinearCertificate
open RealPinwheel.FiveSixths

private lemma atom_nonpos {n : ℕ} (a : LinearAtom n) (d : Fin n → ℝ)
    (h : a.Holds d) : a.eval d ≤ 0 := by
  unfold LinearAtom.Holds at h
  split_ifs at h
  · exact h.le
  · exact h

private lemma context_holds {n : ℕ} (Γ : List (LinearAtom n)) (d : Fin n → ℝ)
    (hΓ : ∀ a ∈ Γ, a.Holds d) (j : ℕ) : (contextAtom Γ j).Holds d := by
  unfold contextAtom
  cases h : Γ[j]? with
  | none => simp [Option.getD, LinearAtom.Holds, LinearAtom.eval, zeroAtom]
  | some a =>
    simp only [Option.getD_some]
    exact hΓ a (List.mem_of_getElem? h)

private lemma weighted_nonpos {n : ℕ} (Γ : List (LinearAtom n)) (d : Fin n → ℝ)
    (hΓ : ∀ a ∈ Γ, a.Holds d) (ts : List (ℕ × ℕ)) :
    (ts.map fun x => (x.2 : ℝ) * (contextAtom Γ x.1).eval d).sum ≤ 0 := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
      (atom_nonpos _ d (context_holds Γ d hΓ x.1))) ih

private lemma weighted_neg {n : ℕ} (Γ : List (LinearAtom n)) (d : Fin n → ℝ)
    (hΓ : ∀ a ∈ Γ, a.Holds d) (ts : List (ℕ × ℕ))
    (h : ts.any (fun x => decide (0 < x.2) && (contextAtom Γ x.1).strict) = true) :
    (ts.map fun x => (x.2 : ℝ) * (contextAtom Γ x.1).eval d).sum < 0 := by
  induction ts with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with h | h
    · have ha := context_holds Γ d hΓ x.1
      simp only [LinearAtom.Holds, h.2, ↓reduceIte] at ha
      have hw : (0 : ℝ) < x.2 := by exact_mod_cast h.1
      exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hw ha) (weighted_nonpos Γ d hΓ xs)
    · exact add_neg_of_nonpos_of_neg
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
          (atom_nonpos _ d (context_holds Γ d hΓ x.1))) (ih h)

private lemma weighted_eval {n : ℕ} (Γ : List (LinearAtom n)) (d : Fin n → ℝ)
    (c : LinearCombination) :
    (c.terms.map fun x => (x.2 : ℝ) * (contextAtom Γ x.1).eval d).sum =
      (combinationConstant Γ c : ℝ) + ∑ i, (combinationCoeff Γ c i : ℝ) * d i := by
  rcases c with ⟨den, ts⟩
  induction ts with
  | nil => simp [combinationConstant, combinationCoeff]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, combinationConstant, combinationCoeff,
      Int.cast_add, Int.cast_mul, Int.cast_natCast] at ih ⊢
    simp only [LinearAtom.eval] at ih ⊢
    simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc]
    rw [← Finset.mul_sum]
    rw [ih]
    ring

private lemma combination_sound {n : ℕ} (Γ : List (LinearAtom n)) (c : LinearCombination)
    (target : LinearAtom n) (hc : combinationCheck Γ c target = true)
    (d : Fin n → ℝ) (hΓ : ∀ a ∈ Γ, a.Holds d) : target.Holds d := by
  simp only [combinationCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_true_left] at hc
  rcases hc with ⟨⟨⟨hden, hcoef⟩, hconst⟩, hstrict⟩
  have hd : (0 : ℝ) < c.denominator := by exact_mod_cast hden
  have he : ∀ i, (c.denominator : ℝ) * (target.coeff i : ℝ) = (combinationCoeff Γ c i : ℝ) := by
    intro i
    exact_mod_cast hcoef i
  have hC : (c.denominator : ℝ) * (target.constant : ℝ) ≤ (combinationConstant Γ c : ℝ) := by
    exact_mod_cast hconst
  have hv := weighted_nonpos Γ d hΓ c.terms
  have hsum := weighted_eval Γ d c
  have hEval : (c.denominator : ℝ) * target.eval d =
      (c.denominator : ℝ) * (target.constant : ℝ) +
        ∑ i, (combinationCoeff Γ c i : ℝ) * d i := by
    simp only [LinearAtom.eval, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, he]
  unfold LinearAtom.Holds
  cases hs : target.strict with
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    apply (mul_le_mul_iff_right₀ hd).mp
    simp only [mul_zero]
    linarith
  | true =>
    simp only [hs, ↓reduceIte]
    simp only [hs, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hstrict
    apply (mul_lt_mul_iff_right₀ hd).mp
    simp only [mul_zero]
    rcases hstrict with hgap | hneg
    · have hg : (c.denominator : ℝ) * (target.constant : ℝ) < (combinationConstant Γ c : ℝ) := by
        exact_mod_cast hgap
      linarith
    · have hn := weighted_neg Γ d hΓ c.terms hneg
      linarith

private lemma complement_holds {n : ℕ} (a : LinearAtom n) (d : Fin n → ℝ)
    (h : ¬ a.Holds d) : (complementAtom a).Holds d := by
  have he : (complementAtom a).eval d = -a.eval d := by
    simp [LinearAtom.eval, complementAtom, Finset.sum_neg_distrib]
    ring
  cases hs : a.strict
  · simp only [LinearAtom.Holds, hs, Bool.false_eq_true, ↓reduceIte, not_le] at h
    simp only [LinearAtom.Holds, complementAtom, hs, Bool.not_false, ↓reduceIte]
    change (complementAtom a).eval d < 0
    rw [he]
    linarith
  · simp only [LinearAtom.Holds, hs, ↓reduceIte, not_lt] at h
    simp only [LinearAtom.Holds, complementAtom, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (complementAtom a).eval d ≤ 0
    rw [he]
    linarith

private lemma upper_holds_iff {n : ℕ} (i : Fin n) (p q : ℕ) (strict : Bool)
    (hq : 0 < q) (d : Fin n → ℝ) :
    (upperAtom i p q strict).Holds d ↔
      (if strict then d i < (p : ℝ) / q else d i ≤ (p : ℝ) / q) := by
  have he : (upperAtom i p q strict).eval d = (q : ℝ) * d i - p := by
    simp [LinearAtom.eval, upperAtom]
    ring
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  change (if strict then (upperAtom i p q strict).eval d < 0 else
    (upperAtom i p q strict).eval d ≤ 0) ↔ _
  rw [he]
  cases strict
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [le_div_iff₀ hqR]
    constructor <;> intro h <;> nlinarith
  · simp only [↓reduceIte]
    rw [lt_div_iff₀ hqR]
    constructor <;> intro h <;> nlinarith

private theorem cover_sound {n : ℕ} (N : ℕ) (codes : ℕ → CycleCode) (Γ : List (LinearAtom n))
    (tree : LinearCoverTree n) (hc : linearCoverCheck N codes Γ tree = true)
    (d : Fin n → ℝ) (hΓ : ∀ a ∈ Γ, a.Holds d) :
    ∃ j : Fin N, codeBox (codes j.val) d := by
  induction tree generalizing Γ with
  | empty c =>
    have h := combination_sound Γ c (falseAtom n) hc d hΓ
    simp [LinearAtom.Holds, LinearAtom.eval, falseAtom] at h
  | word j cs =>
    simp only [linearCoverCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_finRange, forall_true_left] at hc
    refine ⟨⟨j, hc.1⟩, ?_⟩
    intro i
    have hi := hc.2 i
    exact (upper_holds_iff i _ _ _ hi.1 d).mp (combination_sound Γ (cs i) _ hi.2 d hΓ)
  | split i p q strict l r ihl ihr =>
    simp only [linearCoverCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    let a := upperAtom i p q strict
    by_cases h : a.Holds d
    · apply ihl (a :: Γ) hc.1.2
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb
      · exact hba ▸ h
      · exact hΓ b hb
    · apply ihr (complementAtom a :: Γ) hc.2
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb
      · exact hba ▸ complement_holds a d h
      · exact hΓ b hb

private lemma initial_holds {n k : ℕ} (d : Fin n → ℝ)
    (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : (∑ i, if i.val < k then d i else 0) ≤ (5 : ℝ) / 6) :
    ∀ a ∈ initialAtoms n k, a.Holds d := by
  intro a ha
  simp only [initialAtoms, List.mem_append, List.mem_map, List.mem_finRange,
    true_and, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl
  · have he : (positiveAtom i).eval d = -d i := by simp [LinearAtom.eval, positiveAtom]
    simp only [LinearAtom.Holds, positiveAtom, ↓reduceIte]
    change (positiveAtom i).eval d < 0
    rw [he]
    exact neg_neg_of_pos (hpos i)
  · have he : (orderAtom (⟨i.val, by omega⟩ : Fin n) ⟨i.val + 1, by omega⟩).eval d =
        d ⟨i.val + 1, by omega⟩ - d ⟨i.val, by omega⟩ := by
      simp [LinearAtom.eval, orderAtom, sub_mul, Finset.sum_sub_distrib]
    simp only [LinearAtom.Holds, orderAtom, Bool.false_eq_true, ↓reduceIte]
    change (orderAtom _ _).eval d ≤ 0
    rw [he]
    exact sub_nonpos.mpr (hord (by change i.val ≤ i.val + 1; omega))
  · have he : (densityAtom n k).eval d =
        6 * (∑ i, if i.val < k then d i else 0) - 5 := by
      simp [LinearAtom.eval, densityAtom, Finset.mul_sum, mul_ite, ite_mul] <;> ring
    simp only [LinearAtom.Holds, densityAtom, Bool.false_eq_true, ↓reduceIte]
    change (densityAtom n k).eval d ≤ 0
    rw [he]
    linarith

theorem solution {n : ℕ} (k : ℕ) (N : ℕ) (codes : ℕ → CycleCode) (tree : LinearCoverTree n)
    (hc : linearCoverCheck N codes (initialAtoms n k) tree = true)
    (d : Fin n → ℝ) (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : (∑ i, if i.val < k then d i else 0) ≤ (5 : ℝ) / 6) :
    ∃ j : Fin N, codeBox (codes j.val) d := by
  exact cover_sound N codes (initialAtoms n k) tree hc d (initial_holds d hpos hord hsum)
