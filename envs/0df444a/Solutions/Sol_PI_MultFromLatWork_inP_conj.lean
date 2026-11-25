-- Prove2me | solution 1 for PI.MultFromLatWork.inP_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:57:13.829066+00:00
-- url     : https://prove2.me/submissions/d354cc4b-e551-46dd-b354-347180264468

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Theorems.Thm_PI_MultFromLatWork_kset_conjTranspose
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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hX : inP ε X) : inP ε (k * X * kᴴ) := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkh : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Jm ε = Jm ε * kᴴ := kset_conjTranspose hk
  have hJkh := hkh.2
  have hJk := hk'.2
  have hG : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  have hX2 : X * Jm ε = -(Jm ε * X) := hX.2
  have e1 : (k * X * kᴴ)ᴴ * Jm ε = k * (Xᴴ * Jm ε) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hJkh]
  have e2 : Jm ε * (k * X * kᴴ) = k * (Jm ε * X) * kᴴ := by
    calc Jm ε * (k * X * kᴴ) = (Jm ε * k) * X * kᴴ := by simp only [Matrix.mul_assoc]
      _ = (k * Jm ε) * X * kᴴ := by rw [← hJk]
      _ = k * (Jm ε * X) * kᴴ := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · show (k * X * kᴴ)ᴴ * Jm ε + Jm ε * (k * X * kᴴ) = 0
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hG, Matrix.mul_zero, Matrix.zero_mul]
  · calc k * X * kᴴ * Jm ε = k * (X * Jm ε) * kᴴ := by simp only [Matrix.mul_assoc, hJkh]
      _ = k * (-(Jm ε * X)) * kᴴ := by rw [hX2]
      _ = -(k * (Jm ε * X) * kᴴ) := by rw [Matrix.mul_neg, Matrix.neg_mul]
      _ = -(Jm ε * (k * X * kᴴ)) := by rw [e2]
end PI.MultFromLatWork
