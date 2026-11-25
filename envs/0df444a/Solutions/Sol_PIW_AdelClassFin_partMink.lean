-- Prove2me | solution 1 for PIW.AdelClassFin.partMink
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:03.871972+00:00
-- url     : https://prove2.me/submissions/4305e14a-8610-47db-bce4-0fb1c79461c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor
import Theorems.Thm_PIW_AdelClassFin_hmk_factor
import Theorems.Thm_PIW_AdelClassFin_hmk_box
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
noncomputable section
open PIW PIW.AdelClassFin
open MeasureTheory Matrix Module
open scoped MatrixOrder
namespace PIW.AdelClassFin
theorem _root_.solution : PartMink := by
  intro N hN
  refine ⟨4 * N, fun G hG => ?_⟩
  obtain ⟨B, rfl⟩ := hmk_factor G hG
  have hdet : (Bᵀ * B).det = B.det ^ 2 := by rw [det_mul, det_transpose, sq]
  have hpos := hG.det_pos
  have hB : B.det ≠ 0 := by
    intro h0; rw [hdet, h0] at hpos; simp at hpos
  obtain ⟨c, hc0, hc⟩ := hmk_box hN B hB
  refine ⟨c, hc0, ?_⟩
  set v : Fin N → ℝ := fun i => (c i : ℝ)
  set d := |B.det|
  have hd0 : 0 < d := abs_pos.mpr hB
  have hq : v ⬝ᵥ ((Bᵀ * B) *ᵥ v) = ∑ i, (B *ᵥ v) i ^ 2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, sq]
  have hdetG : (Bᵀ * B).det = d ^ 2 := by rw [hdet, sq_abs]
  have hpow : (d ^ ((1 : ℝ) / N)) ^ 2 = (d ^ 2) ^ ((1 : ℝ) / N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast d, ← Real.rpow_mul hd0.le, ← Real.rpow_mul hd0.le,
      mul_comm]
  rw [hq, hdetG, ← hpow]
  calc ∑ i, (B *ᵥ v) i ^ 2 ≤ ∑ _i : Fin N, (2 * d ^ ((1 : ℝ) / N)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq' (abs_le.mp (hc i)).1 (abs_le.mp (hc i)).2
    _ = 4 * N * (d ^ ((1 : ℝ) / N)) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]; ring
end PIW.AdelClassFin
