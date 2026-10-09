-- Prove2me | solution 1 for OCB2012.cj_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:08:56.273169+00:00
-- url     : https://prove2.me/submissions/3ae7906b-69b1-4465-b3bb-d831a8df6471

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

open OCB2012 in
theorem solution {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1] [DecidableEq x2]
    (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) (ρ : Matrix x1 x1 ℂ) :
    Φ ρ = (ptrace₁ ((ρ ⊗ₖ (1 : Matrix x2 x2 ℂ)) * cjMatrix Φ))ᵀ := by
  -- expand `ρ = ∑ᵢⱼ ρᵢⱼ • Eᵢⱼ` in the matrix units `Eᵢⱼ = single i j 1`
  have hρ : ρ = ∑ i, ∑ j, ρ i j • single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
    simp only [smul_single, smul_eq_mul, mul_one]
  ext k l
  conv_lhs => rw [hρ]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    transpose_apply, ptrace₁, of_apply, mul_apply, kroneckerMap_apply, one_apply, cjMatrix,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
