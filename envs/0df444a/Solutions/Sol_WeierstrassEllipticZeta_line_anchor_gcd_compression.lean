-- Prove2me | solution 1 for WeierstrassEllipticZeta.line_anchor_gcd_compression
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T18:23:58.803384+00:00
-- url     : https://prove2.me/submissions/898d37c9-97e7-4e1f-b624-3679a6b14bb5

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Polynomial.Div
import Definitions.Def_WeierstrassEllipticZeta_SparseLineAnchorGCD
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace TranscendenceTheory

/-- Starting from any nonzero member, each necessary new GCD input lowers
the degree. The sum of the selected cardinality and final degree is bounded. -/
theorem polynomial_gcd_subfamily {ι K : Type*} [Field K]
    (f : ι → Polynomial K) (i : ι) (hi : f i ≠ 0) (s : Finset ι) :
    ∃ t : Finset ι, t ⊆ insert i s ∧ i ∈ t ∧
      t.gcd f = (insert i s).gcd f ∧
      t.card + (t.gcd f).natDegree ≤ (f i).natDegree + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨{i}, by simp, by simp, rfl, ?_⟩
      have hd : (normalize (f i)).natDegree ≤ (f i).natDegree :=
        Polynomial.natDegree_le_of_dvd (normalize_associated _).dvd hi
      simpa [Nat.add_comm] using Nat.add_le_add_left hd 1
  | @insert j s hj ih =>
      obtain ⟨t, hts, hit, ht, hbound⟩ := ih
      have hq : t.gcd f ≠ 0 := by
        intro h
        exact hi ((Finset.gcd_eq_zero_iff.mp h) i hit)
      by_cases hdiv : t.gcd f ∣ f j
      · refine ⟨t, ?_, hit, ?_, hbound⟩
        · intro k hk
          have := hts hk
          simp only [Finset.mem_insert] at this ⊢
          tauto
        · rw [Finset.insert_comm, Finset.gcd_insert, ← ht]
          exact ((gcd_eq_right_iff (f j) (t.gcd f) Finset.normalize_gcd).mpr hdiv).symm
      · have hdrop : (GCDMonoid.gcd (f j) (t.gcd f)).natDegree <
            (t.gcd f).natDegree := by
          by_contra! hle
          have hassoc := Polynomial.associated_of_dvd_of_natDegree_le
            (gcd_dvd_right (f j) (t.gcd f)) hq hle
          exact hdiv (hassoc.symm.dvd.trans (gcd_dvd_left _ _))
        refine ⟨insert j t, ?_, Finset.mem_insert_of_mem hit, ?_, ?_⟩
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · simp
          · have := hts hk
            simp only [Finset.mem_insert] at this ⊢
            tauto
        · rw [Finset.insert_comm i j s, Finset.gcd_insert, Finset.gcd_insert, ht]
        · rw [Finset.gcd_insert]
          have hc : (insert j t).card ≤ t.card + 1 := Finset.card_insert_le _ _
          omega

theorem polynomialGCDCore_spec {ι K : Type*} [Field K]
    (f : ι → Polynomial K) (s : Finset ι) :
    polynomialGCDCore f s ⊆ s ∧
    (polynomialGCDCore f s).gcd f = s.gcd f ∧
    ∀ t : Finset ι, t ⊆ s → t.gcd f = s.gcd f →
      (polynomialGCDCore f s).card ≤ t.card := by
  classical
  have hc := Classical.choose_spec (Finset.exists_min_image
    (s.powerset.filter (fun t => t.gcd f = s.gcd f)) Finset.card
    (show (s.powerset.filter (fun t => t.gcd f = s.gcd f)).Nonempty from ⟨s, by simp⟩))
  change polynomialGCDCore f s ∈ _ ∧ _ at hc
  have hm := Finset.mem_filter.mp hc.1
  refine ⟨Finset.mem_powerset.mp hm.1, hm.2, ?_⟩
  intro t hts ht
  exact hc.2 t (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, ht⟩)

theorem polynomialGCDCore_card_degree {ι K : Type*} [Field K]
    (f : ι → Polynomial K) (s : Finset ι) (i : ι)
    (his : i ∈ s) (hi : f i ≠ 0) :
    (polynomialGCDCore f s).card + (s.gcd f).natDegree ≤
      (f i).natDegree + 1 := by
  classical
  obtain ⟨t, hts, _, heq, hb⟩ := polynomial_gcd_subfamily f i hi s
  rw [Finset.insert_eq_of_mem his] at hts heq
  have hc := (polynomialGCDCore_spec f s).2.2 t hts heq
  rw [heq] at hb
  omega

end TranscendenceTheory


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

private lemma linear_degree (a b : ℂ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))

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

private lemma obstruction_sample (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ)
    (hp : anchorObstruction S Q m b α ≠ 0) :
    ∃ j ∈ Finset.range (m + n + 1),
      anchorObstruction S Q m b α = anchorSlice S Q b α j ∧
      anchorSlice S Q b α j ≠ 0 := by
  have hex : ∃ j : ℕ, j ≤ m ∧ anchorSlice S Q b α j ≠ 0 := by
    by_contra hz
    exact hp (by simp [anchorObstruction, hz])
  refine ⟨Nat.find hex, Finset.mem_range.mpr ?_, ?_, (Nat.find_spec hex).2⟩
  · have hj := (Nat.find_spec hex).1
    omega
  · simp only [anchorObstruction, dif_pos hex]

theorem sparseLineAnchorGCD_eq (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ) :
    sparseLineAnchorGCD S Q m n b α = lineAnchorGCD S Q m n b α := by
  by_cases h : anchorObstruction S Q m b α = 0
  · simp [sparseLineAnchorGCD, lineAnchorGCDCore, lineAnchorGCD, h]
  · simpa [sparseLineAnchorGCD, lineAnchorGCDCore, lineAnchorGCD, h] using
      (TranscendenceTheory.polynomialGCDCore_spec
        (fun j : ℕ => anchorSlice S Q b α j) (Finset.range (m + n + 1))).2.1

private theorem line_core_subset (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ) :
    lineAnchorGCDCore S Q m n b α ⊆ Finset.range (m + n + 1) := by
  by_cases h : anchorObstruction S Q m b α = 0
  · simp [lineAnchorGCDCore, h]
  · simpa [lineAnchorGCDCore, h] using
      (TranscendenceTheory.polynomialGCDCore_spec
        (fun j : ℕ => anchorSlice S Q b α j) (Finset.range (m + n + 1))).1

private theorem line_core_card_degree (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α : ℂ) :
    (lineAnchorGCDCore S Q m n b α).card +
      (lineAnchorGCD S Q m n b α).natDegree ≤ n + 1 := by
  by_cases h : anchorObstruction S Q m b α = 0
  · simp [lineAnchorGCDCore, lineAnchorGCD, h]
  · obtain ⟨j, hj, _, hne⟩ := obstruction_sample S Q m n b α h
    have hc := TranscendenceTheory.polynomialGCDCore_card_degree
      (fun j : ℕ => anchorSlice S Q b α j) (Finset.range (m + n + 1)) j hj hne
    have hd := anchor_slice_degree S Q m n hQ b α j
    simp only [lineAnchorGCDCore, lineAnchorGCD, if_neg h]
    omega

private theorem line_core_minimal (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (m + n + 1))
    (heq : J.gcd (fun j : ℕ => anchorSlice S Q b α j) = lineAnchorGCD S Q m n b α) :
    (lineAnchorGCDCore S Q m n b α).card ≤ J.card := by
  by_cases h : anchorObstruction S Q m b α = 0
  · simp [lineAnchorGCDCore, h]
  · simp only [lineAnchorGCDCore, if_neg h]
    apply (TranscendenceTheory.polynomialGCDCore_spec
      (fun j : ℕ => anchorSlice S Q b α j) (Finset.range (m + n + 1))).2.2 J hJ
    simpa [lineAnchorGCD, h] using heq


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (∀ b α : ℂ,
      lineAnchorGCDCore S Q m n b α ⊆ Finset.range (m + n + 1) ∧
      sparseLineAnchorGCD S Q m n b α = lineAnchorGCD S Q m n b α ∧
      (lineAnchorGCDCore S Q m n b α).card +
        (lineAnchorGCD S Q m n b α).natDegree ≤ n + 1 ∧
      (0 < (lineAnchorGCD S Q m n b α).natDegree →
        (lineAnchorGCDCore S Q m n b α).card ≤ n) ∧
      (∀ J : Finset ℕ, J ⊆ Finset.range (m + n + 1) →
        J.gcd (fun j : ℕ => anchorSlice S Q b α j) = lineAnchorGCD S Q m n b α →
        (lineAnchorGCDCore S Q m n b α).card ≤ J.card)) ∧
    ∀ (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
      (K : Set ℂ) (Z : Finset ℂ) (P : FiniteLocusCandidate Λ X → Prop),
      (∃ a : GCDAnchorCandidate Λ η X S Q m n K Z,
        P (gcdAnchorLocus Λ η X S Q m n K Z a)) ↔
      (∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        P (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro b α
    have hb := line_core_card_degree S Q m n hQ b α
    exact ⟨line_core_subset S Q m n b α, sparseLineAnchorGCD_eq S Q m n b α,
      hb, by omega, line_core_minimal S Q m n b α⟩
  · intro Λ η X K Z P
    constructor
    · rintro ⟨a, ha⟩
      rcases a with a | a
      · exact ⟨.inl (), ha⟩
      rcases a with b | ⟨p, b⟩
      · exact ⟨.inr (.inl b), ha⟩
      · have hd : 0 < (sparseLineAnchorGCD S Q m n b.val.val
            (periodPairSlope Λ η X p)).natDegree := by
          rw [sparseLineAnchorGCD_eq]
          exact b.property
        exact ⟨.inr (.inr ⟨p, ⟨b.val, hd⟩⟩), ha⟩
    · rintro ⟨a, ha⟩
      rcases a with a | a
      · exact ⟨.inl (), ha⟩
      rcases a with b | ⟨p, b⟩
      · exact ⟨.inr (.inl b), ha⟩
      · have hd : 0 < (lineAnchorGCD S Q m n b.val.val
            (periodPairSlope Λ η X p)).natDegree := by
          rw [← sparseLineAnchorGCD_eq]
          exact b.property
        exact ⟨.inr (.inr ⟨p, ⟨b.val, hd⟩⟩), ha⟩
