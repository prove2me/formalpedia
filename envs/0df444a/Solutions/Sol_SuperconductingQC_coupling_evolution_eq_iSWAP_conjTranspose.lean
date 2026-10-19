-- Prove2me | solution 1 for SuperconductingQC.coupling_evolution_eq_iSWAP_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:15:00.968663+00:00
-- url     : https://prove2.me/submissions/561c9c76-2916-41dc-af38-d56e4beb2b0a

import Mathlib
import Definitions.Def_SuperconductingQC_Gates

open scoped Matrix Kronecker
open Matrix

namespace SCAux
open SuperconductingQC

def P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun p q =>
  if p = q ∧ p.1 = p.2 then 1
  else if p.1 ≠ p.2 ∧ q.1 ≠ q.2 then (if q = (0, 1) then 1 else if p = (0, 1) then 1 else -1) else 0

noncomputable def Pinv : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun p q =>
  if p = q ∧ p.1 = p.2 then 1
  else if p.1 ≠ p.2 ∧ q.1 ≠ q.2 then (1 / 2) * (if q = (0, 1) then 1 else if p = (0, 1) then 1 else -1)
  else 0

noncomputable def dv (q : Fin 2 × Fin 2) : ℂ :=
  if q = (0, 1) then -Real.pi / 2 * Complex.I else if q = (1, 0) then Real.pi / 2 * Complex.I else 0

noncomputable def ev (q : Fin 2 × Fin 2) : ℂ :=
  if q = (0, 1) then -Complex.I else if q = (1, 0) then Complex.I else 1

lemma P_mul_Pinv : P * Pinv = 1 := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, P, Pinv, Matrix.one_apply] <;> norm_num

lemma Pinv_mul_P : Pinv * P = 1 := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, P, Pinv] <;> norm_num

lemma exp_dv : NormedSpace.exp (diagonal dv) = diagonal ev := by
  rw [Matrix.exp_diagonal, Pi.exp_def]
  congr 1; funext q
  rw [← Complex.exp_eq_exp_ℂ]
  unfold dv ev
  split_ifs <;> simp

lemma gen_eq (hbar J : ℝ) (hhbar : hbar ≠ 0) (hJ : J ≠ 0) :
    (-(Complex.I * (((Real.pi / (2 * J)) / hbar : ℝ) : ℂ))) • couplingHamiltonian hbar J =
      P * diagonal dv * Pinv := by
  have hb : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar
  have hj : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, P, Pinv, dv, couplingHamiltonian, pauliX, pauliY,
      Matrix.kroneckerMap_apply, Matrix.diagonal_apply] <;> field_simp <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

lemma final : P * diagonal ev * Pinv = iSWAPᴴ := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, P, Pinv, ev, iSWAP, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply] <;> ring

end SCAux

open SuperconductingQC SCAux in
theorem solution (hbar J : ℝ) (hhbar : hbar ≠ 0)
    (hJ : J ≠ 0) :
    timeEvolution hbar (Real.pi / (2 * J)) (couplingHamiltonian hbar J) = iSWAPᴴ := by
  unfold timeEvolution
  have hinv : P⁻¹ = Pinv := Matrix.inv_eq_right_inv P_mul_Pinv
  have hu : IsUnit P := ⟨⟨P, Pinv, P_mul_Pinv, Pinv_mul_P⟩, rfl⟩
  rw [gen_eq hbar J hhbar hJ, ← hinv, Matrix.exp_conj P _ hu, exp_dv, hinv, final]
