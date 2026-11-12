-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P92.ideal_sifting_variants
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:01:29.551206+00:00
-- url     : https://prove2.me/submissions/a991316c-840f-4090-89a9-6c96a2f4cd5e

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Intake100.P92 in
theorem solution (mu : ℝ) (hmu : 0 ≤ mu) :
    QAlgorithms.mutualInfoBits idealBitLaw = 1 ∧
    idealSiftingCoefficient 0 mu = mu/2 ∧
    idealSiftingCoefficient 1 mu = mu/2 ∧
    idealSiftingCoefficient 2 mu = mu/2 ∧
    idealSiftingCoefficient 3 mu = mu/4 ∧
    idealSiftingCoefficient 4 mu = mu/4 ∧
    (∀ (q x f0 : ℝ), q ∈ Set.Icc (0:ℝ) 1 → x ∈ Set.Icc (0:ℝ) 1 →
      q*x < 1 → f0 ∈ Set.Icc (0:ℝ) (1-q*x) →
      (∑ ab, announcedLaw q x f0 ab) = q*x+f0) := by
  have hl : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  have hsum : (∑ x : Bool × Bool, if x.1 ≠ x.2 then (1/4:ℝ) else 0) = 1/2 := by
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold QAlgorithms.mutualInfoBits idealBitLaw
    simp only [Fintype.sum_bool]
    norm_num [hl]
  · unfold idealSiftingCoefficient
    rw [if_pos (show (0 : Fin 5).val < 3 by decide)]
  · unfold idealSiftingCoefficient
    rw [if_pos (show (1 : Fin 5).val < 3 by decide)]
  · unfold idealSiftingCoefficient
    rw [if_pos (show (2 : Fin 5).val < 3 by decide)]
  · unfold idealSiftingCoefficient
    rw [if_neg (show ¬ (3 : Fin 5).val < 3 by decide), hsum]
    ring
  · unfold idealSiftingCoefficient
    rw [if_neg (show ¬ (4 : Fin 5).val < 3 by decide), hsum]
    ring
  · intro q x f0 _ _ hqx _
    have hne : 1 - q*x ≠ 0 := by
      intro h; linarith
    rw [Fintype.sum_prod_type]
    simp [Fintype.sum_bool, announcedLaw, zLaw]
    field_simp <;> ring

end
