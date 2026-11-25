-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.isAdmissible_rankOneGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:08.069642+00:00
-- url     : https://prove2.me/submissions/5f9e29f7-d58f-466e-9c33-a9b957c89462

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_eq_vecMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_coe_rankOneGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_coe_rankOneGL_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_one_add_smul_vecMulVec_mulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_vecMul_one_add_smul_vecMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_smem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
section Pr
variable {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K)
end Pr
section Rk1
variable {R : Type} [CommRing R] {n : ℕ}
end Rk1
section Good
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
private theorem smul_vecMul' (b : K) (v : Fin n → K) (M : Matrix (Fin n) (Fin n) K) :
    (b • v) ᵥ* M = b • (v ᵥ* M) := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
end Good
end PI.UnitaryGroupMassFormula.ScXuExists
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
variable {O P Λ1 Λ2 a a' α α'}
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) (w γ : Fin n → K) (c d : K)
    (h : c + d + c * d * ((γ ᵥ* P) ⬝ᵥ w) = 0) (hc : c ∈ O) (hd : d ∈ O) (hw : w ∈ Λ1) (hγ : γ ∈ Λ2)
    (hwα : ∀ i, pr P (α i) w = 0 ∧ pr P (α' i) w = 0) (hγa : ∀ i, pr P γ (a i) = 0 ∧ pr P γ (a' i) = 0) :
    Good O P Λ1 Λ2 a a' α α' (rankOneUnitGL w (γ ᵥ* P) c d h) := by
  unfold Good
  rw [coe_rankOneGL_inv, coe_rankOneGL]
  have hm : ∀ {u v : K}, u ∈ O → v ∈ O → u * v ∈ O := by
    intro u v hu hv
    first
    | exact mul_mem hu hv
    | exact O.mul_mem _ _ hu hv
    | exact O.toSubring.mul_mem hu hv
  have hO : ∀ x ∈ Λ1, (γ ᵥ* P) ⬝ᵥ x ∈ O := fun x hx => by
    rw [← pr_eq_vecMul]
    exact hP γ hγ x hx
  have hO' : ∀ β ∈ Λ2, (β ᵥ* P) ⬝ᵥ w ∈ O := fun β hβ => by
    rw [← pr_eq_vecMul]
    exact hP β hβ w hw
  have hvec : ∀ (e : K) (β : Fin n → K),
      (β + (e * ((β ᵥ* P) ⬝ᵥ w)) • γ) ᵥ* P = (β ᵥ* P) ᵥ* (1 + e • vecMulVec w (γ ᵥ* P)) := by
    intro e β
    rw [vecMul_one_add_smul_vecMulVec, Matrix.add_vecMul, smul_vecMul']
  refine ⟨fun x hx => ⟨?_, ?_⟩,
    fun β hβ => ⟨⟨β + (c * ((β ᵥ* P) ⬝ᵥ w)) • γ, ?_, hvec c β⟩,
      ⟨β + (d * ((β ᵥ* P) ⬝ᵥ w)) • γ, ?_, hvec d β⟩⟩, fun i => ?_⟩
  · rw [one_add_smul_vecMulVec_mulVec]
    exact Λ1.add_mem hx (smem O (hm hc (hO x hx)) hw)
  · rw [one_add_smul_vecMulVec_mulVec]
    exact Λ1.add_mem hx (smem O (hm hd (hO x hx)) hw)
  · exact Λ2.add_mem hβ (smem O (hm hc (hO' β hβ)) hγ)
  · exact Λ2.add_mem hβ (smem O (hm hd (hO' β hβ)) hγ)
  · have e1 : (γ ᵥ* P) ⬝ᵥ a i = 0 := by rw [← pr_eq_vecMul]; exact (hγa i).1
    have e2 : (γ ᵥ* P) ⬝ᵥ a' i = 0 := by rw [← pr_eq_vecMul]; exact (hγa i).2
    have e3 : (α i ᵥ* P) ⬝ᵥ w = 0 := by rw [← pr_eq_vecMul]; exact (hwα i).1
    have e4 : (α' i ᵥ* P) ⬝ᵥ w = 0 := by rw [← pr_eq_vecMul]; exact (hwα i).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [one_add_smul_vecMulVec_mulVec, e1, mul_zero, zero_smul, add_zero]
    · rw [one_add_smul_vecMulVec_mulVec, e2, mul_zero, zero_smul, add_zero]
    · rw [vecMul_one_add_smul_vecMulVec, e3, mul_zero, zero_smul, add_zero]
    · rw [vecMul_one_add_smul_vecMulVec, e4, mul_zero, zero_smul, add_zero]
end PI.UnitaryGroupMassFormula.ScXuExists
