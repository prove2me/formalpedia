-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.leg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:52.807137+00:00
-- url     : https://prove2.me/submissions/2be26e51-435b-4950-9f1e-704422e60757

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_inv_memO_of_v
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_ne_zero_of_v
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_coe_rankOneGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_good_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_isAdmissible_rankOneGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_one_add_smul_vecMulVec_mulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_eq_vecMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_smul_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_sub_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_sub_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_smem
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_vecMul_one_add_smul_vecMulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
variable {O P Λ1 Λ2 a a' α α'}
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) {up φp uq φq : Fin n → K}
    (hp : Pair O P Λ1 Λ2 a a' α α' up φp) (hq : Pair O P Λ1 Λ2 a a' α α' uq φq)
    (hcp : O.valuation (pr P φp up) = 1) (hcq : O.valuation (pr P φq uq) = 1)
    (hd : O.valuation (pr P φp uq) = 1) :
    ∃ T : GL (Fin n) K, Good O P Λ1 Λ2 a a' α α' T ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ up = uq ∧
      (φq ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = (pr P φq uq / pr P φp up) • (φp ᵥ* P) := by
  unfold Pair at hp hq
  obtain ⟨hup, hφp, hupα, hφpa⟩ := hp
  obtain ⟨huq, hφq, huqα, hφqa⟩ := hq
  have hcp0 : pr P φp up ≠ 0 := ne_zero_of_v O hcp
  have hcq0 : pr P φq uq ≠ 0 := ne_zero_of_v O hcq
  have hd0 : pr P φp uq ≠ 0 := ne_zero_of_v O hd
  have hcpi : (pr P φp up)⁻¹ ∈ O := inv_memO_of_v O hcp
  have hcqi : (pr P φq uq)⁻¹ ∈ O := inv_memO_of_v O hcq
  have hdi : (pr P φp uq)⁻¹ ∈ O := inv_memO_of_v O hd
  have hb : pr P φq up ∈ O := hP φq hφq up hup
  have e1 : pr P φp uq * (pr P φp uq)⁻¹ = 1 := mul_inv_cancel₀ hd0
  have e2 : pr P φp up * (pr P φp up)⁻¹ = 1 := mul_inv_cancel₀ hcp0
  have e3 : pr P φq uq * (pr P φq uq)⁻¹ = 1 := mul_inv_cancel₀ hcq0
  have hXup : (φq ᵥ* P) ⬝ᵥ up = pr P φq up := (pr_eq_vecMul P φq up).symm
  have hYup : (φp ᵥ* P) ⬝ᵥ up = pr P φp up := (pr_eq_vecMul P φp up).symm
  have hD1 : (φq ᵥ* P) ⬝ᵥ (uq - up) = pr P φq uq - pr P φq up := by
    rw [← pr_eq_vecMul, pr_sub_right]
  have hdot : ∀ (V W : Fin n → K) (t : K), (V + t • W) ⬝ᵥ up = V ⬝ᵥ up + t * (W ⬝ᵥ up) := by
    intro V W t
    first
    | (simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]; done)
    | (simp; done)
    | (simp [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]; done)
  obtain ⟨γ2, hγ2⟩ : ∃ γ2 : Fin n → K, γ2 = φq - (pr P φq up * (pr P φp up)⁻¹) • φp := ⟨_, rfl⟩
  have hγ2u : (γ2 ᵥ* P) ⬝ᵥ up = 0 := by
    rw [← pr_eq_vecMul, hγ2, pr_sub_left, pr_smul_left]
    linear_combination (-pr P φq up) * e2
  have hγ2P : γ2 ᵥ* P = φq ᵥ* P - (pr P φq up * (pr P φp up)⁻¹) • (φp ᵥ* P) := by
    subst hγ2
    first
    | (simp only [sub_vecMul, vecMul_smul]; done)
    | (simp only [sub_vecMul, smul_vecMul]; done)
    | (simp [sub_vecMul]; done)
    | (ext j; simp [vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]; done)
  have hγ2mem : γ2 ∈ Λ2 := by
    have hs : pr P φq up * (pr P φp up)⁻¹ ∈ O := by
      first | exact mul_mem hb hcpi | exact O.mul_mem _ _ hb hcpi
    rw [hγ2]
    exact Λ2.sub_mem hφq (smem O hs hφp)
  have hγ2a : ∀ i, pr P γ2 (a i) = 0 ∧ pr P γ2 (a' i) = 0 := fun i => by
    simp only [hγ2, pr_sub_left, pr_smul_left, (hφqa i).1, (hφqa i).2, (hφpa i).1, (hφpa i).2,
      mul_zero, sub_zero, and_self]
  have hwα1 : ∀ i, pr P (α i) (uq - up) = 0 ∧ pr P (α' i) (uq - up) = 0 := fun i =>
    ⟨by rw [pr_sub_right, (huqα i).1, (hupα i).1, sub_self],
      by rw [pr_sub_right, (huqα i).2, (hupα i).2, sub_self]⟩
  have h1 : (pr P φp up)⁻¹ + -(pr P φp uq)⁻¹ +
      (pr P φp up)⁻¹ * -(pr P φp uq)⁻¹ * ((φp ᵥ* P) ⬝ᵥ (uq - up)) = 0 := by
    rw [← pr_eq_vecMul, pr_sub_right]
    linear_combination (pr P φp uq)⁻¹ * e2 - (pr P φp up)⁻¹ * e1
  have h2 : -(pr P φq uq)⁻¹ + (pr P φq uq)⁻¹ +
      -(pr P φq uq)⁻¹ * (pr P φq uq)⁻¹ * ((γ2 ᵥ* P) ⬝ᵥ up) = 0 := by
    rw [hγ2u]
    ring
  have hn1 : -(pr P φp uq)⁻¹ ∈ O := by
    first | exact neg_mem hdi | exact O.neg_mem _ hdi
  have hn2 : -(pr P φq uq)⁻¹ ∈ O := by
    first | exact neg_mem hcqi | exact O.neg_mem _ hcqi
  have hT1 := isAdmissible_rankOneGL hP (uq - up) φp _ _ h1 hcpi hn1 (Λ1.sub_mem huq hup) hφp hwα1 hφpa
  have hT2 := isAdmissible_rankOneGL hP up γ2 _ _ h2 hn2 hcqi hup hγ2mem hupα hγ2a
  refine ⟨rankOneUnitGL (uq - up) (φp ᵥ* P) _ _ h1 * rankOneUnitGL up (γ2 ᵥ* P) _ _ h2,
    good_mul _ _ _ _ _ _ _ _ hT1 hT2, ?_, ?_⟩
  · simp only [Units.val_mul, ← mulVec_mulVec, coe_rankOneGL, one_add_smul_vecMulVec_mulVec, hγ2u, mul_zero,
      zero_smul, add_zero, hYup, inv_mul_cancel₀ hcp0, one_smul]
    abel
  · simp only [Units.val_mul, ← vecMul_vecMul, coe_rankOneGL, vecMul_one_add_smul_vecMulVec]
    rw [hD1, hdot, hXup, hYup, hγ2P]
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((φq ᵥ* P) j - pr P φq up * (pr P φp up)⁻¹ * (φp ᵥ* P) j) *
      (-(pr P φq uq)⁻¹ * (pr P φq uq - pr P φq up) * e2 - e3)
end PI.UnitaryGroupMassFormula.ScXuExists
