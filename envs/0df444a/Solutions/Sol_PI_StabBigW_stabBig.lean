-- Prove2me | solution 1 for PI.StabBigW.stabBig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:56.94196+00:00
-- url     : https://prove2.me/submissions/5eb2a315-f802-4e70-8421-9098f757e698

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_ut_of_mem
import Theorems.Thm_PI_StabBigW_hb_sq
import Theorems.Thm_PI_StabBigW_g_left_inv
import Theorems.Thm_PI_StabBigW_eq_one_of

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
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution : PI.StabBig := by
  intro k r c μ hc hμ
  have hL : (Hb k * μᴴ * Hb k) * μ = 1 := by
    calc (Hb k * μᴴ * Hb k) * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hμ, hb_sq]
  have hR : μ * (Hb k * μᴴ * Hb k) = 1 := by
    rw [← Matrix.inv_eq_left_inv hL]
    exact Matrix.mul_nonsing_inv μ (Matrix.isUnit_det_of_left_inverse hL)
  have hG : bigCell k r (fun a => star (c a)) (Hb k * μᴴ * Hb k) * bigCell k r c μ = 1 :=
    g_left_inv hc hL
  have hdet : IsUnit (bigCell k r c μ).det := Matrix.isUnit_det_of_left_inverse hG
  have hGr : bigCell k r c μ * (bigCell k r c μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h1N : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r := by
    unfold Nset UH
    simp [Matrix.one_apply]
  ext a
  simp only [RStab, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hb⟩
    have E : a * bigCell k r c μ =
        bigCell k r c μ * ((bigCell k r c μ)⁻¹ * a * bigCell k r c μ) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGr, Matrix.one_mul]
    exact eq_one_of hc hR (ut_of_mem ha) (ut_of_mem hb) E
  · rintro rfl
    refine ⟨h1N, ?_⟩
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hdet]
    exact h1N
end PI.StabBigW
