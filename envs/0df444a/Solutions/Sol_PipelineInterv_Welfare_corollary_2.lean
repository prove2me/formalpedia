-- Prove2me | solution 1 for PipelineInterv.Welfare.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:52:05.447003+00:00
-- url     : https://prove2.me/submissions/7cca4f60-6f9c-4f4f-a950-20d00c439e02

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

open Matrix

open PipelineInterv.Welfare in
theorem solution {w : ℕ} (R : Fin w → ℝ) (D D' : Fin w → ℝ) (hD : IsDist D) (hD' : IsDist D')
    (ε : ℝ) (hDD' : l1 (D - D') ≤ ε) (M : Matrix (Fin w) (Fin w) ℝ)
    (hM : M ∈ colStochastic ℝ (Fin w)) :
    R ⬝ᵥ (M *ᵥ D') - supNorm R * ε ≤ R ⬝ᵥ (M *ᵥ D) := by
  obtain ⟨hM0, hcol⟩ := mem_colStochastic_iff_sum.1 hM
  set s := supNorm R with hs
  have hR : ∀ i, |R i| ≤ s := fun i => by
    rw [hs, supNorm]; exact le_ciSup (f := fun i => |R i|) (Finite.bddAbove_range _) i
  have hs0 : 0 ≤ s := by
    rw [hs, supNorm]; exact Real.iSup_nonneg fun i => abs_nonneg (R i)
  have key : R ⬝ᵥ (M *ᵥ (D' - D)) ≤ s * l1 (D - D') := by
    calc R ⬝ᵥ (M *ᵥ (D' - D)) = ∑ i, ∑ j, R i * (M i j * (D' - D) j) := by
          simp only [dotProduct, mulVec, Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, s * |(D' - D) j| * M i j := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have h1 : R i * (D' - D) j ≤ s * |(D' - D) j| := by
            calc R i * (D' - D) j ≤ |R i * (D' - D) j| := le_abs_self _
              _ = |R i| * |(D' - D) j| := abs_mul _ _
              _ ≤ s * |(D' - D) j| := mul_le_mul_of_nonneg_right (hR i) (abs_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_right h1 (hM0 i j)]
      _ = ∑ j, s * |(D' - D) j| * ∑ i, M i j := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ = s * l1 (D - D') := by
          simp only [hcol, mul_one]
          rw [l1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Pi.sub_apply, Pi.sub_apply, abs_sub_comm]
  have h2 : R ⬝ᵥ (M *ᵥ (D' - D)) = R ⬝ᵥ (M *ᵥ D') - R ⬝ᵥ (M *ᵥ D) := by
    rw [mulVec_sub, dotProduct_sub]
  have h3 : s * l1 (D - D') ≤ s * ε := mul_le_mul_of_nonneg_left hDD' hs0
  linarith
