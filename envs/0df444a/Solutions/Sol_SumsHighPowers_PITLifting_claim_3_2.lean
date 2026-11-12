-- Prove2me | solution 1 for SumsHighPowers.PITLifting.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:14:36.181425+00:00
-- url     : https://prove2.me/submissions/0f46edfd-741d-4b5f-ac00-5d86435ae3d9

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_SumPowClass
import Definitions.Def_SumsHighPowers_PITLifting_IsHittingSet
import Definitions.Def_SumsHighPowers_PITLifting_PairwiseNonAssociate

section
namespace SumsHighPowers.PITLifting

theorem Dev_eval_aeval {F : Type*} [Field F] {n : ℕ} (H : Fin n → Polynomial F) (a : F)
    (g : MvPolynomial (Fin n) F) :
    (MvPolynomial.aeval H g).eval a = MvPolynomial.eval (fun j => (H j).eval a) g := by
  have h1 : (MvPolynomial.aeval H g).eval a
      = MvPolynomial.eval₂ ((Polynomial.evalRingHom a).comp (algebraMap F (Polynomial F)))
          ((Polynomial.evalRingHom a) ∘ H) g := by
    rw [MvPolynomial.aeval_def]
    exact MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom a) _ _ _
  rw [h1]
  have : (Polynomial.evalRingHom a).comp (algebraMap F (Polynomial F)) = RingHom.id F := by
    ext x; simp
  rw [this]; rfl

theorem chk_claim_3_2 {F : Type*} [Field F] (n Δ s : ℕ)
    (C : Set (MvPolynomial (Fin n) F))
    (u : Fin s → Fin n → F) (hu : IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u)
    (a : Fin s → F) (ha : Function.Injective a)
    (H : Fin n → Polynomial F) (hHdeg : ∀ j, (H j).degree < s)
    (hHint : ∀ i j, (H j).eval (a i) = u i j)
    (A B : MvPolynomial (Fin n) F) (hA : A ∈ degBounded C Δ) (hB : B ∈ degBounded C Δ)
    (hAB : PairwiseNonAssociate (F := F) ![A, B]) :
    PairwiseNonAssociate (F := F) ![MvPolynomial.aeval H A, MvPolynomial.aeval H B] := by
  have h01 := hAB 0 1 (by decide)
  rw [LinearIndependent.pair_iff] at h01
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h01
  have key : ∀ s' t' : F, s' • MvPolynomial.aeval H A + t' • MvPolynomial.aeval H B = 0 →
      s' = 0 ∧ t' = 0 := by
    intro s' t' h
    apply h01
    by_contra hne
    have hmem : s' • A + t' • B ∈ sumPowClass 2 1 (degBounded C Δ) := by
      refine ⟨![s', t'], ![A, B], ?_, ?_⟩
      · intro i; fin_cases i <;> simpa using ‹_›
      · simp [Fin.sum_univ_two]
    obtain ⟨i, hi⟩ := hu _ hmem hne
    apply hi
    have : MvPolynomial.aeval H (s' • A + t' • B) = 0 := by simpa using h
    have h2 := Dev_eval_aeval H (a i) (s' • A + t' • B)
    rw [this] at h2
    simp only [hHint] at h2
    simpa using h2.symm
  intro i j hij
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [LinearIndependent.pair_iff]
    simpa using key
  · rw [LinearIndependent.pair_iff]
    intro s' t' h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
    have := key t' s' (by rw [add_comm]; simpa using h)
    exact ⟨this.2, this.1⟩

end SumsHighPowers.PITLifting
end

theorem solution : type_of% @SumsHighPowers.PITLifting.chk_claim_3_2 := @SumsHighPowers.PITLifting.chk_claim_3_2
