-- Prove2me | solution 1 for TranscendenceTheory.bounded_bivariate_relation_basis
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T16:19:07.233511+00:00
-- url     : https://prove2.me/submissions/b134e799-b0df-47c7-a045-368799448f86

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section
open Polynomial
open scoped Classical

private lemma finite_submodule_basis
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) [FiniteDimensional K W] :
    ∃ H : Fin (Module.finrank K W) → V,
      LinearIndependent K H ∧ Submodule.span K (Set.range H) = W := by
  let : Module.Free K W := Module.Free.of_divisionRing K W
  let B := Module.finBasis K W
  refine ⟨(fun i => (B i).val), ?_, ?_⟩
  · exact B.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr W.injective_subtype)
  · simpa only [← Set.range_comp, Function.comp_def] using
      (Submodule.span_val_image_eq_iff W (Set.range B)).mpr B.span_eq

theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (x y : A) (b s : ℕ) :
    ∃ k : ℕ, k ≤ (b + 1) * (s + 1) ∧
      ∃ H : Fin k → Polynomial (Polynomial K),
        LinearIndependent K H ∧ ∀ P : Polynomial (Polynomial K),
          P ∈ Submodule.span K (Set.range H) ↔
            P.natDegree ≤ s ∧ (∀ i, (P.coeff i).natDegree ≤ b) ∧
              P.eval₂ (Polynomial.aeval x).toRingHom y = 0 := by
  classical
  let E : Polynomial (Polynomial K) →ₐ[K] A := Polynomial.aevalTower (Polynomial.aeval x) y
  let W : Submodule K (Polynomial (Polynomial K)) :=
    { carrier := {P | P.natDegree ≤ s ∧ (∀ i, (P.coeff i).natDegree ≤ b) ∧ E P = 0}
      zero_mem' := by simp
      add_mem' := by
        intro P Q hP hQ
        refine ⟨(natDegree_add_le P Q).trans (max_le hP.1 hQ.1), ?_, ?_⟩
        · intro i
          rw [coeff_add]
          exact (natDegree_add_le (P.coeff i) (Q.coeff i)).trans
            (max_le (hP.2.1 i) (hQ.2.1 i))
        · rw [map_add, hP.2.2, hQ.2.2, zero_add]
      smul_mem' := by
        intro c P hP
        refine ⟨(natDegree_smul_le c P).trans hP.1, ?_, ?_⟩
        · intro i
          rw [coeff_smul]
          exact (natDegree_smul_le c (P.coeff i)).trans (hP.2.1 i)
        · rw [map_smul, hP.2.2, smul_zero] }
  let T : W →ₗ[K] (Fin (s + 1) × Fin (b + 1) → K) :=
    { toFun := fun P ij => (P.val.coeff ij.1.val).coeff ij.2.val
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hT : Function.Injective T := by
    intro P Q h
    apply Subtype.ext
    ext i j
    by_cases hi : i < s + 1
    · by_cases hj : j < b + 1
      · exact congrFun h (⟨i, hi⟩, ⟨j, hj⟩)
      · have hjb : b < j := lt_of_lt_of_le (Nat.lt_succ_self b) (Nat.le_of_not_gt hj)
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (P.property.2.1 i) hjb),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (Q.property.2.1 i) hjb)]
    · have his : s < i := lt_of_lt_of_le (Nat.lt_succ_self s) (Nat.le_of_not_gt hi)
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt P.property.1 his),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt Q.property.1 his)]
  let : FiniteDimensional K W := FiniteDimensional.of_injective T hT
  obtain ⟨H, hH, hspan⟩ := finite_submodule_basis K (Polynomial (Polynomial K)) W
  refine ⟨Module.finrank K W, ?_, H, hH, ?_⟩
  · have h := LinearMap.finrank_le_finrank_of_injective hT
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
      mul_one, Nat.mul_comm] using h
  · intro P
    rw [hspan]
    rfl
