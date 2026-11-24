-- Prove2me | solution 1 for PI.MultFromLatWork.kset_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:58:19.15297+00:00
-- url     : https://prove2.me/submissions/8ba4b490-0113-46ab-8b30-bbba17e7e2bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Theorems.Thm_PI_MultFromLatWork_kset_unitary
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
open PI PI.MultFromLatWork
open Formalism.REAL
namespace PI.MultFromLatWork
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  obtain ⟨h1, h2⟩ := kset_unitary hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  show kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Jm ε = Jm ε * kᴴ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact h1
  · calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, Matrix.mul_one]
      _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
      _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hk'.2]
      _ = (kᴴ * k) * Jm ε * kᴴ := by simp only [Matrix.mul_assoc]
      _ = Jm ε * kᴴ := by rw [h1, Matrix.one_mul]
end PI.MultFromLatWork
