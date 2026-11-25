-- Prove2me | solution 1 for PI.SymDistWork.symDist_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:34.974973+00:00
-- url     : https://prove2.me/submissions/2321c965-9edc-45c6-a2b6-473bb3e6b6b7

import Definitions.Def_Formalism_PeriodIntegrals_SymDist
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Theorems.Thm_PI_SymDistWork_kset_inv
import Theorems.Thm_PI_SymDistWork_kset_ct
import Theorems.Thm_PI_SymDistWork_symD_eq
import Theorems.Thm_PI_SymDistWork_inUJ_coe
import Theorems.Thm_Formalism_REAL_hermitian_of_mem_hermitian_part
import Theorems.Thm_Formalism_REAL_hermitian_small_ball
import Theorems.Thm_Formalism_REAL_matrix_exp_neg_mul_exp
import Theorems.Thm_Formalism_REAL_mul_exp_neg_polarLog_mem_compact
import Theorems.Thm_Formalism_REAL_polarLog_mem_hermitian_part


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.SymDistWork
open Formalism.REAL
variable {n : ℕ}
namespace PI.SymDistWork
theorem _root_.solution (hE : PI.ExpTri) : PI.SymDist := by
  intro n ε g h
  have hpol : ∀ x : UJ ε, ∃ k X, k ∈ Kset ε ∧ inP ε X ∧
      ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X := by
    intro x
    refine ⟨((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      NormedSpace.exp (-polarLog ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)),
      polarLog _, mul_exp_neg_polarLog_mem_compact (inUJ_coe x), polarLog_mem_hermitian_part (inUJ_coe x), ?_⟩
    rw [Matrix.mul_assoc, matrix_exp_neg_mul_exp, Matrix.mul_one]
  have hUJmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, inUJ ε A → inUJ ε B → inUJ ε (A * B) := by
    intro A B hA hB
    unfold inUJ at *
    rw [Matrix.conjTranspose_mul]
    calc Bᴴ * Aᴴ * Jm ε * (A * B) = Bᴴ * (Aᴴ * Jm ε * A) * B := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hA, hB]
  have hUJk : ∀ k, k ∈ Kset ε → inUJ ε k := by
    intro k hk
    unfold inUJ
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, (kset_inv hk).1, Matrix.one_mul]
  have hKmul : ∀ a b, a ∈ Kset ε → b ∈ Kset ε → a * b ∈ Kset ε := by
    intro a b ha hb
    refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hcancel : ∀ k, k ∈ Kset ε → ∀ X : Matrix (Fin n) (Fin n) ℂ, kᴴ * (k * X) = X := by
    intro k hk X
    rw [← Matrix.mul_assoc, (kset_inv hk).1, Matrix.one_mul]
  obtain ⟨k1, X1, hk1, hX1, hg1⟩ := hpol g
  obtain ⟨k2, X2, hk2, hX2, hh1⟩ := hpol h
  obtain ⟨hk2a, hk2b⟩ := kset_inv hk2
  let u2 : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨k2, k2ᴴ, hk2b, hk2a⟩
  have hexpc : NormedSpace.exp (k2ᴴ * X1 * k2) = k2ᴴ * NormedSpace.exp X1 * k2 :=
    Matrix.exp_units_conj' u2 X1
  have hconj : NormedSpace.exp X1 * k2 = k2 * NormedSpace.exp (k2ᴴ * X1 * k2) := by
    rw [hexpc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hk2b, Matrix.one_mul]
  have hgh : (((g * h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      (k1 * k2) * (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2) := by
    rw [Subgroup.coe_mul, Units.val_mul, hg1, hh1]
    calc k1 * NormedSpace.exp X1 * (k2 * NormedSpace.exp X2)
        = k1 * (NormedSpace.exp X1 * k2) * NormedSpace.exp X2 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hconj]; simp only [Matrix.mul_assoc]
  have hM : inUJ ε (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2) := by
    have e : NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 =
        (k2ᴴ * k1ᴴ) * (((g * h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hgh]
      simp only [Matrix.mul_assoc, hcancel _ hk1, hcancel _ hk2]
    rw [e]
    exact hUJmul _ _ (hUJmul _ _ (hUJk _ (kset_ct hk2)) (hUJk _ (kset_ct hk1))) (inUJ_coe _)
  have hk3 := mul_exp_neg_polarLog_mem_compact hM
  have hX3 := polarLog_mem_hermitian_part hM
  have hM3 : NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 =
      (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2 *
        NormedSpace.exp (-polarLog (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2))) *
      NormedSpace.exp (polarLog (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2)) := by
    rw [Matrix.mul_assoc _ (NormedSpace.exp (-_)), matrix_exp_neg_mul_exp, Matrix.mul_one]
  have hYh : (k2ᴴ * X1 * k2)ᴴ = k2ᴴ * X1 * k2 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hermitian_of_mem_hermitian_part hX1, Matrix.mul_assoc]
  have htri := hE n (k2ᴴ * X1 * k2) X2 _ _ hYh (hermitian_of_mem_hermitian_part hX2) (hermitian_of_mem_hermitian_part hX3) hk3.1 hM3
  have hsY : hs (k2ᴴ * X1 * k2) = hs X1 := by
    rw [((hermitian_small_ball n ε).2 (k2ᴴ * X1) k2 hk2).1, ((hermitian_small_ball n ε).2 X1 k2ᴴ (kset_ct hk2)).2]
  have hd1 := symD_eq g hk1 hX1 hg1
  have hd2 := symD_eq h hk2 hX2 hh1
  have hd3 := symD_eq (g * h) (hKmul _ _ (hKmul _ _ hk1 hk2) hk3) hX3 (by
    rw [hgh, Matrix.mul_assoc (k1 * k2), Matrix.mul_assoc (NormedSpace.exp (k2ᴴ * X1 * k2) * NormedSpace.exp X2),
      matrix_exp_neg_mul_exp, Matrix.mul_one])
  rw [hd1, hd2, hd3]
  have e2 : Real.sqrt (hs (k2ᴴ * X1 * k2)) = Real.sqrt (hs X1) := by rw [hsY]
  rw [← e2]
  exact htri
end PI.SymDistWork
