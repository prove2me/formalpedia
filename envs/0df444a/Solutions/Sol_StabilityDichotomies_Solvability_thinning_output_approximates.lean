-- Prove2me | solution 1 for StabilityDichotomies.Solvability.thinning_output_approximates
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:53:03.116497+00:00
-- url     : https://prove2.me/submissions/48d44c3e-3456-4655-95f2-7adc025a8798

import Theorems.Thm_StabilityDichotomies_Solvability_integrated_occurrence_violation
import Theorems.Thm_StabilityDichotomies_Solvability_approximation_of_constraint_bounds
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

private theorem thinning_output_per_constraint (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (i : Fin I.constraints.card) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A : Solver Γ) (hLaw : ThinningOutputLaw Γ b ε A) :
    (∑ x : V → Bool, (A V I x).toReal *
      (if (occurrenceAt I i).Satisfied x then 0 else 1)) ≤ ε / 2 := by
  let g : (V → Bool) → ℝ := fun x => if (occurrenceAt I i).Satisfied x then 0 else 1
  let f : (V → Bool) → ℝ → ℝ := fun x p => ∑ mask : Fin I.constraints.card → Bool,
    retentionWeight p mask * (if extremalSolution (thinnedInstance I mask) b = x then 1 else 0)
  have hc (mask : Fin I.constraints.card → Bool) : Continuous (fun p : ℝ => retentionWeight p mask) := by
    unfold retentionWeight
    apply continuous_finsetProd
    intro j hj
    cases hm : mask j <;> simp only [hm, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub continuous_id
    · exact continuous_id
  have hcont (x : V → Bool) : Continuous (fun p => f x p * g x) := by
    dsimp [f,g]
    fun_prop
  have hs (p : ℝ) : (∑ x : V → Bool, f x p * g x) =
      ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
      (if (occurrenceAt I i).Satisfied (extremalSolution (thinnedInstance I mask) b) then 0 else 1) := by
    dsimp [f]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro mask hm
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [Fintype.sum_ite_eq]
  have heq : (∑ x : V → Bool, (A V I x).toReal * g x) = ε⁻¹ *
      ∫ p in (1-ε)..1, ∑ x : V → Bool, f x p * g x := by
    simp_rw [hLaw V I hSat]
    change (∑ x : V → Bool, (ε⁻¹ * ∫ p in (1-ε)..1, f x p) * g x) = _
    simp_rw [mul_assoc, ← intervalIntegral.integral_mul_const]
    rw [← Finset.mul_sum, intervalIntegral.integral_finset_sum (fun x hx => (hcont x).intervalIntegrable _ _)]
  rw [show (∑ x : V → Bool, (A V I x).toReal *
      (if (occurrenceAt I i).Satisfied x then 0 else 1)) =
      (∑ x : V → Bool, (A V I x).toReal * g x) from rfl, heq]
  simp_rw [hs]
  exact integrated_occurrence_violation Γ b hΓ V I hSat i ε hε hε1


theorem solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A : Solver Γ) (hLaw : ThinningOutputLaw Γ b ε A) : Approximates A ε := by
  apply approximation_of_constraint_bounds Γ A ε
  intro V _ I hI c hc
  obtain ⟨j,hj⟩ := List.get_of_mem (Multiset.mem_toList.mpr hc)
  let i : Fin I.constraints.card := ⟨j.val, by simpa using j.isLt⟩
  have hi : occurrenceAt I i = c := by simpa [occurrenceAt, i] using hj
  have hb := thinning_output_per_constraint Γ b hΓ V I hI i ε hε hε1 A hLaw
  rw [hi] at hb
  have he : ε / 2 ≤ ε := by linarith
  exact (by simpa only [ite_not] using hb.trans he)
