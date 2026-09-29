-- Prove2me | solution 1 for SiegelFields.commutator_eq_cross
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:57:26.781985+00:00
-- url     : https://prove2.me/submissions/f6855fe5-6cf6-4d1e-8f85-1d25c9676f39

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

set_option autoImplicit false

open Matrix Complex

/-- Unnormalised Pauli-type matrix `v₀σ₃ + v₁σ₁ + v₂σ₂`. -/
noncomputable def sfPauliM_6f314db1 (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 0 : ℂ), (v 1 : ℂ) - I * (v 2 : ℂ); (v 1 : ℂ) + I * (v 2 : ℂ), -(v 0 : ℂ)]

lemma sfPauliM_comm_6f314db1 (v w : Fin 3 → ℝ) :
    sfPauliM_6f314db1 v * sfPauliM_6f314db1 w - sfPauliM_6f314db1 w * sfPauliM_6f314db1 v =
      (2 * I) • sfPauliM_6f314db1 (crossProduct v w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sfPauliM_6f314db1, cross_apply] <;>
    ring_nf <;> simp [I_sq] <;> ring_nf

lemma sfVec_eq_6f314db1 (v : Fin 3 → ℝ) :
    SiegelFields.vecToMatrix v = ((Real.sqrt 2 : ℂ)⁻¹) • sfPauliM_6f314db1 v := rfl

open Matrix Complex SiegelFields in
theorem solution (v w : Fin 3 → ℝ) :
    vecToMatrix v * vecToMatrix w - vecToMatrix w * vecToMatrix v =
      ((Real.sqrt 2 : ℂ) * I) • vecToMatrix (crossProduct v w) := by
  rw [sfVec_eq_6f314db1, sfVec_eq_6f314db1, sfVec_eq_6f314db1]
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, sfPauliM_comm_6f314db1,
    smul_smul, smul_smul]
  congr 1
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  field_simp
  linear_combination (-1 : ℂ) * hs
