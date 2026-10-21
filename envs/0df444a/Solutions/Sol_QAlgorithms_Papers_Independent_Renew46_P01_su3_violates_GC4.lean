-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P01.su3_violates_GC4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:38:30.968235+00:00
-- url     : https://prove2.me/submissions/8dc854b8-076f-420a-bda3-dbfcc02365ac

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

lemma g64i_s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma g64i_s6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
lemma g64i_s23 : Real.sqrt (2/3) ^ 2 = 2/3 := Real.sq_sqrt (by norm_num)
lemma g64i_s12 : Real.sqrt 12 = Real.sqrt 2 * Real.sqrt 6 := by
  rw [← Real.sqrt_mul (by norm_num)]; norm_num

theorem solution :
    ¬ UniqueParent su3OctetCoefficients ∧
    su3OctetCoefficients 0 (0, 2) ≠ 0 ∧
    su3OctetCoefficients 1 (0, 2) ≠ 0 ∧
    (∀ M N : Fin 2,
      (∑ x : Fin 3 × Fin 3,
        star (su3OctetCoefficients M x) * su3OctetCoefficients N x) =
          if M = N then 1 else 0) := by
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have h6 : (0:ℝ) < Real.sqrt 6 := by positivity
  have a0 : su3OctetCoefficients 0 (0, 2) ≠ 0 := by
    simp [su3OctetCoefficients]
  have a1 : su3OctetCoefficients 1 (0, 2) ≠ 0 := by
    simp [su3OctetCoefficients]
  refine ⟨fun h => absurd (h _ 0 1 a0 a1) (by decide), a0, a1, ?_⟩
  intro M N
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
  have e3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have e23 : Real.sqrt (2/3) = Real.sqrt 2 / Real.sqrt 3 := Real.sqrt_div' _ (by norm_num)
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have c2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [← Complex.ofReal_pow, g64i_s2]; norm_num
  have c3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by rw [← Complex.ofReal_pow, s3]; norm_num
  have n2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  have n3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h3.ne'
  fin_cases M <;> fin_cases N <;>
    simp [su3OctetCoefficients, e3, e23] <;> field_simp <;> simp only [show (4:ℕ) = 2*2 from rfl, pow_mul, c2, c3] <;> norm_num
