-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_operatorBasis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:25:04.768988+00:00
-- url     : https://prove2.me/submissions/07bbd438-1616-44d7-b322-7e3009481826

import Theorems.Thm_QAlgorithms_Papers_RoadmapX07_averageFidelity_eq_entanglementFidelity
import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_entanglementFidelity_operatorBasis

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P10

private lemma output_conjugate_channel {d : ℕ}
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsChannel (conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ E) := by
  obtain ⟨m, K, hK, hE⟩ := hE
  refine ⟨m, fun j => star (U : Matrix (Fin d) (Fin d) ℂ) * K j, ?_, ?_⟩
  · unfold IsKrausFamily at hK ⊢
    convert hK using 1
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (K j)ᴴ * ((U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ)) * K j := by
        simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [(Matrix.mem_unitaryGroup_iff.mp U.property), Matrix.mul_one]
  · intro X
    simp only [Function.comp_apply, conjSuperop, hE, krausApply,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Nielsen Eq. (17), from Eq. (3) and Eq. (16) applied to the output-conjugated channel. -/
theorem solution (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (B : OrthogonalUnitaryOperatorBasis d) :
    gateFidelity d hd E U =
      ((∑ j, ((U : Matrix (Fin d) (Fin d) ℂ)*star (B.basis j)*
        star (U : Matrix (Fin d) (Fin d) ℂ)*E (B.basis j)).trace.re)+(d : ℝ)^2) /
          ((d : ℝ)^2*((d : ℝ)+1)) := by
  have hC := output_conjugate_channel E hE U
  unfold gateFidelity
  rw [QAlgorithms.Papers.RoadmapX07.averageFidelity_eq_entanglementFidelity d hd _ hC,
    entanglementFidelity_operatorBasis d hd _ hC B]
  have hs : (∑ j, (star (B.basis j) *
      (conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ E) (B.basis j)).trace.re) =
      ∑ j, ((U : Matrix (Fin d) (Fin d) ℂ)*star (B.basis j)*
        star (U : Matrix (Fin d) (Fin d) ℂ)*E (B.basis j)).trace.re := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [Function.comp_apply, conjSuperop, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hs]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  field_simp [hd0]
