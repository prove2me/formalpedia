-- Prove2me | solution 1 for SuperconductingQC.cnot_eq_locals_two_iSWAP
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:17:33.497062+00:00
-- url     : https://prove2.me/submissions/0dfbc8bf-7f7c-48f8-8bef-8edad1f2286b

import Mathlib
import Definitions.Def_SuperconductingQC_Gates

open scoped Matrix Kronecker
open Matrix

namespace SCAux2
open SuperconductingQC

noncomputable def r : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma r_sq : r * r = 1 / 2 := by
  unfold r
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

lemma r_conj : starRingEnd ℂ r = r := by unfold r; simp

def Sg : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]
noncomputable def Bg : Matrix (Fin 2) (Fin 2) ℂ := !![r, r; -(Complex.I * r), Complex.I * r]
noncomputable def Cg : Matrix (Fin 2) (Fin 2) ℂ := !![r, -(Complex.I * r); -(Complex.I * r), r]
def Zg : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

lemma uni (U : Matrix (Fin 2) (Fin 2) ℂ) (h : U * star U = 1) : U ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff]; exact h

lemma Sg_u : Sg ∈ unitaryGroup (Fin 2) ℂ := uni _ (by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sg, Matrix.mul_apply, Fin.sum_univ_two])
lemma Zg_u : Zg ∈ unitaryGroup (Fin 2) ℂ := uni _ (by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Zg, Matrix.mul_apply, Fin.sum_univ_two])
lemma Bg_u : Bg ∈ unitaryGroup (Fin 2) ℂ := uni _ (by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Bg, Matrix.mul_apply, Fin.sum_univ_two, r_conj] <;> ring_nf <;>
    simp [Complex.I_sq, r_sq, sq] <;> ring_nf <;> simp [r_sq] <;> ring)
lemma Cg_u : Cg ∈ unitaryGroup (Fin 2) ℂ := uni _ (by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Cg, Matrix.mul_apply, Fin.sum_univ_two, r_conj] <;> ring_nf <;>
    simp [Complex.I_sq, r_sq, sq] <;> ring_nf <;> simp [r_sq] <;> ring)

lemma main_eq : CNOT = (Sg ⊗ₖ Bg) * iSWAP * (Cg ⊗ₖ Zg) * iSWAP * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Sg) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, iSWAP,
      CNOT, Sg, Bg, Cg, Zg, Matrix.one_apply] <;> ring_nf <;> simp [Complex.I_sq, r_sq, sq] <;>
    ring_nf <;> simp [r_sq, Complex.I_sq] <;> ring_nf

end SCAux2

open SuperconductingQC SCAux2 in
theorem solution :
    ∃ A B C D E F : Matrix (Fin 2) (Fin 2) ℂ,
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ D ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      E ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ F ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      CNOT = (A ⊗ₖ B) * iSWAP * (C ⊗ₖ D) * iSWAP * (E ⊗ₖ F) :=
  ⟨Sg, Bg, Cg, Zg, 1, Sg, Sg_u, Bg_u, Cg_u, Zg_u, one_mem _, Sg_u, main_eq⟩
