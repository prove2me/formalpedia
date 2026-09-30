-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_anchor_candidate_selection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T06:56:28.717437+00:00
-- url     : https://prove2.me/submissions/640cbb18-e693-49a7-9709-9d9b9b87ec0d

import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
import Theorems.Thm_WeierstrassEllipticZeta_finite_elementary_locus_vanishing
import Theorems.Thm_WeierstrassEllipticZeta_finite_locus_candidate_selection
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

private def restrictionPoly (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1, T, Polynomial.C (S 0 b), Polynomial.C (S 1 b), Polynomial.C (S 2 b),
      Polynomial.C (S 3 b) + U * Polynomial.C (S 0 b),
      Polynomial.C (S 4 b) + U * Polynomial.C (S 2 b)] Q

private lemma substitution_degree (H : Fin 7 → Polynomial ℂ) (w : Fin 7 → ℕ)
    (hH : ∀ i, (H i).natDegree ≤ w i) (Q : MvPolynomial (Fin 7) ℂ)
    (N : ℕ) (hQ : ∀ d ∈ Q.support, ∑ i : Fin 7, d i * w i ≤ N) :
    (MvPolynomial.eval₂Hom Polynomial.C H Q).natDegree ≤ N := by
  rw [Q.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  calc
    _ ≤ (∏ i : Fin 7, H i ^ d i).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i : Fin 7, (H i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i : Fin 7, d i * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hH i))
    _ ≤ N := hQ d hd

private lemma restriction_degree (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (restrictionPoly S b T U Q).natDegree ≤ m * T.natDegree + n * U.natDegree := by
  refine substitution_degree _ ![0, T.natDegree, 0, 0, 0, U.natDegree, U.natDegree] ?_ Q _ ?_
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one]
    · simp
    · exact le_rfl
    · simp
    · simp
    · simp
    · exact Polynomial.natDegree_add_le_of_degree_le (by simp)
        (Polynomial.natDegree_mul_C_le _ _)
    · exact Polynomial.natDegree_add_le_of_degree_le (by simp)
        (Polynomial.natDegree_mul_C_le _ _)
  · intro d hd
    obtain ⟨hm, hn⟩ := hQ d hd
    calc
      _ = d 1 * T.natDegree + (d 5 + d 6) * U.natDegree := by
        simp [Fin.sum_univ_succ]
        ring
      _ ≤ m * T.natDegree + n * U.natDegree :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
          (Nat.mul_le_mul_right _ (by omega))

private lemma restriction_eval (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) (s : ℂ) :
    (restrictionPoly S b T U Q).eval s =
      MvPolynomial.eval ![1, T.eval s, S 0 b, S 1 b, S 2 b,
        S 3 b + U.eval s * S 0 b, S 4 b + U.eval s * S 2 b] Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [restrictionPoly]
  | add P Q hP hQ => simp_all [restrictionPoly, map_add]
  | mul_X P i hP =>
    simp only [restrictionPoly, map_mul, MvPolynomial.eval₂Hom_X] at *
    rw [Polynomial.eval_mul, hP]
    congr 1
    fin_cases i <;> simp

private lemma polynomial_zero_from_range (p : Polynomial ℂ) (N : ℕ)
    (hp : p.natDegree ≤ N) (hz : ∀ j ∈ Finset.range (N + 1), p.eval (j : ℂ) = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun j : Fin (N + 1) => (j.val : ℂ))
  · intro i j hij
    exact Fin.ext (Nat.cast_injective hij)
  · intro j
    exact hz j.val (Finset.mem_range.mpr j.isLt)
  · simpa using Nat.lt_succ_of_le hp

private def locusValue (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (w : Fin 3 → ℂ) : ℂ :=
  MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
    S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q

private lemma linear_degree (a b : ℂ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))


private lemma anchor_slice_eval (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (b α t β : ℂ) :
    (anchorSlice S Q b α t).eval β = locusValue S Q ![t, b, α * t + β] := by
  change (restrictionPoly S b (Polynomial.C t)
    (Polynomial.C (α * t) + Polynomial.X) Q).eval β = _
  rw [restriction_eval]
  simp only [Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
  rfl

private lemma anchor_slice_degree (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α t : ℂ) :
    (anchorSlice S Q b α t).natDegree ≤ n := by
  have h := restriction_degree S b (Polynomial.C t)
    (Polynomial.C (α * t) + Polynomial.X) Q m n hQ
  have hd : (Polynomial.C (α * t) + Polynomial.X).natDegree ≤ 1 := by
    simpa using linear_degree (α * t) 1
  simp only [Polynomial.natDegree_C, mul_zero, zero_add] at h
  exact h.trans ((Nat.mul_le_mul_left n hd).trans_eq (Nat.mul_one n))

theorem anchor_obstruction_degree (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α : ℂ) :
    (anchorObstruction S Q m b α).natDegree ≤ n := by
  unfold anchorObstruction
  split_ifs with h
  · exact anchor_slice_degree S Q m n hQ b α _
  · simp

theorem anchor_obstruction_zero_iff (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α : ℂ) :
    anchorObstruction S Q m b α = 0 ↔
      ∀ t u : ℂ, locusValue S Q ![t, b, u] = 0 := by
  constructor
  · intro hz
    have hslices (j : ℕ) (hj : j ≤ m) : anchorSlice S Q b α j = 0 := by
      by_contra hne
      have hex : ∃ j : ℕ, j ≤ m ∧ anchorSlice S Q b α j ≠ 0 := ⟨j, hj, hne⟩
      have hn := (Nat.find_spec hex).2
      apply hn
      simpa only [anchorObstruction, dif_pos hex] using hz
    intro t u
    let p := restrictionPoly S b Polynomial.X (Polynomial.C u) Q
    have hp : p.natDegree ≤ m := by
      simpa [p] using restriction_degree S b Polynomial.X (Polynomial.C u) Q m n hQ
    have hp0 : p = 0 := polynomial_zero_from_range p m hp (by
      intro j hj
      have hv := congrArg (fun p : Polynomial ℂ => p.eval (u - α * j))
        (hslices j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      rw [anchor_slice_eval] at hv
      simpa [p, restriction_eval, locusValue] using hv)
    have hv := congrArg (fun p : Polynomial ℂ => p.eval t) hp0
    simpa [p, restriction_eval, locusValue] using hv
  · intro hz
    have hslices (j : ℕ) : anchorSlice S Q b α j = 0 := by
      apply Polynomial.funext
      intro β
      simpa only [anchor_slice_eval, Polynomial.eval_zero] using hz j (α * j + β)
    simp only [anchorObstruction, hslices, ne_eq, not_true_eq_false, and_false,
      exists_const, dite_false]

theorem line_anchor_roots_card (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α : ℂ) :
    (lineAnchorRoots S Q m n b α).card ≤ n := by
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (anchor_obstruction_degree S Q m n hQ b α)))

private lemma line_anchor_of_vanishing (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α β : ℂ)
    (hp : anchorObstruction S Q m b α ≠ 0)
    (hz : ∀ t : ℂ, locusValue S Q ![t, b, α * t + β] = 0) :
    β ∈ lineAnchorRoots S Q m n b α := by
  refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots hp).mpr ?_), ?_⟩
  · change (anchorObstruction S Q m b α).eval β = 0
    unfold anchorObstruction
    split_ifs with h
    · rw [anchor_slice_eval]
      exact hz _
    · simp
  · rintro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    simpa [locusValue, add_comm] using hz j

private lemma fibre_values_of_samples (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ)
    (hz : ∀ w ∈ elementaryLocusSamples .fibre r m n, locusValue S Q w = 0) :
    ∀ t u : ℂ, locusValue S Q ![t, r 1, u] = 0 := by
  have hall := ((finite_elementary_locus_vanishing S Q m n hQ .fibre r).2.2).mpr hz
  intro t u
  have hv := hall (r + ![t - r 0, 0, u - r 2])
    ⟨![t - r 0, 0, u - r 2], by simp [elementaryDirections], rfl⟩
  simpa [locusValue] using hv

private lemma line_values_of_samples (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ) (α : ℂ)
    (hz : ∀ w ∈ elementaryLocusSamples (.line α) r m n, locusValue S Q w = 0) :
    ∀ t : ℂ, locusValue S Q ![t, r 1, α * t + (r 2 - α * r 0)] = 0 := by
  have hall := ((finite_elementary_locus_vanishing S Q m n hQ (.line α) r).2.2).mpr hz
  intro t
  have heq : r + ![t - r 0, 0, α * (t - r 0)] =
      ![t, r 1, α * t + (r 2 - α * r 0)] := by
    ext i
    fin_cases i <;> simp <;> ring
  exact heq ▸ hall (r + ![t - r 0, 0, α * (t - r 0)])
    ⟨![t - r 0, 0, α * (t - r 0)], by simp [elementaryDirections], rfl⟩

private lemma fibre_choice_of_values (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b : ℂ)
    (hz : ∀ t u : ℂ, locusValue S Q ![t, b, u] = 0) :
    () ∈ fibreAnchorChoices S Q m n b := by
  refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
  rintro w hw
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hw
  simpa [locusValue] using hz ij.1 ij.2

private lemma quotient_class_count_mono (X : Finset ℂ) (K H : Submodule ℤ ℂ)
    (hKH : K ≤ H) : (X.image H.mkQ).card ≤ (X.image K.mkQ).card := by
  let f : (ℂ ⧸ K) →ₗ[ℤ] (ℂ ⧸ H) :=
    K.liftQ H.mkQ (by
      intro z hz
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hKH hz))
  have heq : X.image H.mkQ = (X.image K.mkQ).image f := by
    rw [Finset.image_image]
    rfl
  rw [heq]
  exact Finset.card_image_le

private lemma finite_anchor_card (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b : ℂ) :
    Fintype.card (FiniteAnchorCandidate Λ η X S Q m n b) ≤
      2 + X.card * (X.card - 1) * n := by
  have hf : (fibreAnchorChoices S Q m n b).card ≤ 1 :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_singleton ())
  have hs : (∑ p : ↥(periodPairCandidates Λ X),
      (lineAnchorRoots S Q m n b (periodPairSlope Λ η X p)).card) ≤
      (periodPairCandidates Λ X).card * n := by
    calc
      _ ≤ ∑ _p : ↥(periodPairCandidates Λ X), n :=
        Finset.sum_le_sum fun p _ => line_anchor_roots_card S Q m n hQ b _
      _ = _ := by simp
  have hp : (periodPairCandidates Λ X).card ≤ X.card * (X.card - 1) := by
    have h : (periodPairCandidates Λ X).card ≤ X.offDiag.card := Finset.card_filter_le _ _
    simpa [Nat.mul_sub_left_distrib] using h
  have hpn := Nat.mul_le_mul_right n hp
  simp only [FiniteAnchorCandidate, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, Fintype.card_coe]
  omega

private lemma finite_anchor_valid (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hzero : MvPolynomial.eval ![1, 0, S 0 0, S 1 0, S 2 0, S 3 0, S 4 0] Q = 0)
    (b : ℂ) (a : FiniteAnchorCandidate Λ η X S Q m n b) :
    ∀ w ∈ candidateLocusSamples Λ η X (anchorCandidateLocus Λ η X S Q m n b a)
        (anchorCandidatePoint Λ η X S Q m n b a) m n,
      locusValue S Q w = 0 := by
  rcases a with u | u | ⟨p, β⟩
  · simpa [anchorCandidateLocus, anchorCandidatePoint, candidateLocusSamples,
      locusValue] using hzero
  · exact (Finset.mem_filter.mp u.property).2
  · apply ((finite_locus_candidate_selection Λ η X S Q m n hQ).2.1 _ _).mpr
    exact (Finset.mem_filter.mp β.property).2


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hzero : MvPolynomial.eval ![1, 0, S 0 0, S 1 0, S 2 0, S 3 0, S 4 0] Q = 0) :
    (∀ b : ℂ,
      Fintype.card (FiniteAnchorCandidate Λ η X S Q m n b) ≤
        2 + X.card * (X.card - 1) * n ∧
      ∀ a : FiniteAnchorCandidate Λ η X S Q m n b,
        ∀ w ∈ candidateLocusSamples Λ η X (anchorCandidateLocus Λ η X S Q m n b a)
            (anchorCandidatePoint Λ η X S Q m n b a) m n,
          MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
            S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
    (∀ (k : FiniteLocusCandidate Λ X) (r : Fin 3 → ℂ),
      (∀ w ∈ candidateLocusSamples Λ η X k r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) →
      ∃ (b : ℂ) (a : FiniteAnchorCandidate Λ η X S Q m n b),
        (X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X
          (anchorCandidateLocus Λ η X S Q m n b a))).mkQ).card ≤
          (X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X k)).mkQ).card ∧
        elementaryDegree (candidateLocusShape Λ η X
          (anchorCandidateLocus Λ η X S Q m n b a)) m =
          elementaryDegree (candidateLocusShape Λ η X k) m) := by
  refine ⟨fun b => ⟨finite_anchor_card Λ η X S Q m n hQ b,
    finite_anchor_valid Λ η X S Q m n hQ hzero b⟩, ?_⟩
  intro k r hz
  have hcanonical := ((finite_locus_candidate_selection Λ η X S Q m n hQ).2.1 k r).mp hz
  rcases k with u | u | p
  · exact ⟨0, .inl (), le_rfl, rfl⟩
  · have hf := fibre_values_of_samples S Q m n hQ r hcanonical
    exact ⟨r 1, .inr (.inl ⟨(), fibre_choice_of_values S Q m n (r 1) hf⟩),
      le_rfl, rfl⟩
  · let α := periodPairSlope Λ η X p
    have hl := line_values_of_samples S Q m n hQ r α hcanonical
    by_cases hp : anchorObstruction S Q m (r 1) α = 0
    · have hf := (anchor_obstruction_zero_iff S Q m n hQ (r 1) α).mp hp
      refine ⟨r 1, .inr (.inl ⟨(), fibre_choice_of_values S Q m n (r 1) hf⟩), ?_, rfl⟩
      exact quotient_class_count_mono X (resonantPeriods Λ η α) Λ (by
        rintro z ⟨v, hv, rfl⟩
        exact v.property)
    · have hβ := line_anchor_of_vanishing S Q m n (r 1) α (r 2 - α * r 0) hp hl
      exact ⟨r 1, .inr (.inr ⟨p, ⟨r 2 - α * r 0, hβ⟩⟩), le_rfl, rfl⟩
