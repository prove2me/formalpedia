-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P11.totalMixture_initializer_unital
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:47:29.599097+00:00
-- url     : https://prove2.me/submissions/a83b54f9-031d-45da-be04-c3ccb3404e87

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P11

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section IV, PDF pp.4–5: a maximally mixed finite initializer induces a unital
one-use channel. No repeatability assumption, or equality of the dimensions, is required. -/
theorem solution {d m : ℕ} (hd : 0 < d) (D : MemoryDevice d m)
    (hInit : D.initial = totalMixture m) :
    IsUnital (fun X => traceLeft (jointStep D D.initial X)) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast D.memory_pos.ne'
  have hU : (D.unitary : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) *
      (D.unitary : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp D.unitary.2
  have hJ : jointStep D D.initial 1 = ((m : ℂ)⁻¹) • (1 : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) := by
    have hk : Matrix.kronecker (((m : ℂ)⁻¹) • (1 : Matrix (Fin m) (Fin m) ℂ))
        (1 : Matrix (Fin d) (Fin d) ℂ) = ((m : ℂ)⁻¹) • (1 : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) := by
      ext ⟨a, b⟩ ⟨a', b'⟩
      by_cases h1 : a = a' <;> by_cases h2 : b = b' <;>
        simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, h1, h2]
    rw [jointStep, hInit, totalMixture, hk, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]
  show traceLeft (jointStep D D.initial 1) = 1
  rw [hJ]
  ext b b'
  simp only [traceLeft, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
    true_and, smul_eq_mul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  split_ifs <;> field_simp
