-- Prove2me | solution 1 for TranscendenceTheory.bounded_resultant_family_selection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T15:50:53.680761+00:00
-- url     : https://prove2.me/submissions/b821f1a9-c619-4f2c-9b55-a609ac474921

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Complex.Basic

noncomputable section
open Polynomial
open scoped Classical

private lemma bounded_family_nonvanishing
    (L : Type*) [Field L] [CharZero L] (V : Finset L) (k : ℕ)
    (v : V → Fin k → L) (hv : ∀ z, ∃ j, v z j ≠ 0) :
    ∃ a : ℕ, a ≤ V.card * (k - 1) ∧
      ∀ z, (∑ j : Fin k, (a : L) ^ j.val * v z j) ≠ 0 := by
  classical
  let P : V → Polynomial L := fun z => ∑ j : Fin k, monomial j.val (v z j)
  have hc (z : V) (j : Fin k) : (P z).coeff j.val = v z j := by
    simp [P, finsetSum_coeff, coeff_monomial, Fin.val_inj]
  have hP (z : V) : P z ≠ 0 := by
    obtain ⟨j, hj⟩ := hv z
    intro hz
    apply hj
    rw [← hc z j, hz, coeff_zero]
  have hnz : (∏ z : V, P z) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun z _ => hP z)
  have hd (z : V) : (P z).natDegree ≤ k - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt j.isLt)
  have hdegree : (∏ z : V, P z).natDegree ≤ V.card * (k - 1) := by
    apply (natDegree_prod_le _ _).trans
    calc
      ∑ z : V, (P z).natDegree ≤ ∑ _z : V, (k - 1) :=
        Finset.sum_le_sum fun z _ => hd z
      _ = V.card * (k - 1) := by simp
  obtain ⟨a, ha⟩ : ∃ a : Fin (V.card * (k - 1) + 1),
      (∏ z : V, P z).eval (a.val : L) ≠ 0 := by
    by_contra! hz
    apply hnz
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ?_ hz ?_
    · intro a b hab
      exact Fin.ext (Nat.cast_inj.mp hab)
    · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hdegree
  refine ⟨a.val, Nat.le_of_lt_succ a.isLt, ?_⟩
  intro z
  have hall : ∏ w : V, (P w).eval (a.val : L) ≠ 0 := by
    simpa only [eval_prod] using ha
  have hz := Finset.prod_ne_zero_iff.mp hall z (Finset.mem_univ z)
  simpa [P, eval_finsetSum, eval_monomial, mul_comm] using hz

theorem solution
    (L : Type*) [Field L] [CharZero L]
    (φ : Polynomial ℂ →+* L) (hφ : Function.Injective φ)
    (F : Polynomial (Polynomial ℂ)) (k b s : ℕ)
    (H : Fin k → Polynomial (Polynomial ℂ))
    (hF : F ≠ 0) (hsplit : (F.map φ).Splits)
    (hroots : ∀ z ∈ (F.map φ).roots, ∃ j, (H j).eval₂ φ z ≠ 0)
    (hdegree : ∀ j, (H j).natDegree ≤ s)
    (hcoeff : ∀ j i, ((H j).coeff i).natDegree ≤ b) :
    ∃ a : ℕ, a ≤ F.natDegree * (k - 1) ∧
      let Q := ∑ j : Fin k, (a ^ j.val) • H j
      F.resultant Q ≠ 0 ∧ Q.natDegree ≤ s ∧
        ∀ i, (Q.coeff i).natDegree ≤ b := by
  classical
  let V := (F.map φ).roots.toFinset
  obtain ⟨a, ha, hav⟩ := bounded_family_nonvanishing L V k
    (fun z j => (H j).eval₂ φ z.val)
    (fun z => hroots z.val (Multiset.mem_toFinset.mp z.property))
  have hcard : V.card ≤ F.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (card_roots_map_le_natDegree F)
  refine ⟨a, ha.trans (Nat.mul_le_mul_right _ hcard), ?_, ?_, ?_⟩
  · let Q := ∑ j : Fin k, (a ^ j.val) • H j
    have hmapF : F.map φ ≠ 0 := fun hz =>
      hF ((Polynomial.map_injective φ hφ) (by simpa using hz))
    have hprod : ((F.map φ).roots.map (Q.map φ).eval).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      intro hz
      obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp hz
      have h := hav ⟨w, Multiset.mem_toFinset.mpr hw⟩
      have he : (Q.map φ).eval w ≠ 0 := by
        simpa [Q, Polynomial.eval_map, eval₂_finsetSum, nsmul_eq_mul,
          eval₂_pow, eval₂_natCast] using h
      exact he hw0
    have hr : (F.map φ).resultant (Q.map φ) ≠ 0 := by
      rw [resultant_eq_prod_eval _ _ _ le_rfl hsplit]
      exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hmapF)) hprod
    intro hz
    apply hr
    change F.resultant Q = 0 at hz
    simpa only [natDegree_map_eq_of_injective hφ, resultant_map_map, map_zero] using
      congrArg φ hz
  · apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_smul_le _ _).trans (hdegree j)
  · intro i
    simp only [finsetSum_coeff, coeff_smul]
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_smul_le _ _).trans (hcoeff j i)
