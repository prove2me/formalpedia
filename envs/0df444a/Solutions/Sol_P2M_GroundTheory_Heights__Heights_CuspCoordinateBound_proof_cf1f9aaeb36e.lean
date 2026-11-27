-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_proof_cf1f9aaeb36e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:06.045438+00:00
-- url     : https://prove2.me/submissions/8a1f0aa9-81a8-4ffd-aff4-c97f3740f98a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCoordinateBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_coord_sq_le_6e27dd9a7003
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_mulVec_sq_le_9aca54dee268
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CuspCoordinateBound
theorem _root_.solution (hImPos : ChartPeriodImPos.Statement)
    (hLow : ChartLowerBlockBound.Statement) (hPG : PeriodGramPosDef.Statement) :
    CuspCoordinateBound.Statement := by
  intro D T
  obtain ⟨M, hM, hMb⟩ := hLow D T
  have hc : 0 < D.c := D.c_pos
  set K : ℝ := 1 / D.c + 2 * M + 2 * D.g * M ^ 2 / D.c with hK
  have hK1 : 0 ≤ 1 / D.c := by positivity
  have hK2 : 0 ≤ 2 * (D.g : ℝ) * M ^ 2 / D.c := by positivity
  have hKpos : 0 < K := by positivity
  refine ⟨1 / K, by positivity, ?_⟩
  intro p hp hpU ℓ hℓ y i hi
  obtain ⟨hYpd, hYc⟩ := hImPos D p.1 hpU ℓ hℓ
  set τ := D.period p.1 ℓ with hτ
  set Y := τ.map Complex.im with hYdef
  set X := τ.map Complex.re with hXdef
  obtain ⟨-, hform⟩ := hPG D.g τ hYpd
  set α : Fin D.g → ℝ := fun k => y (Fin.castAdd D.g k) with hα
  set β : Fin D.g → ℝ := fun k => y (Fin.natAdd D.g k) with hβ
  have hA : 0 ≤ MCSchur.qf Y⁻¹ (α + X *ᵥ β) := MCCusp.qf_nonneg hYpd.inv.posSemidef _
  have hB : 0 ≤ MCSchur.qf Y β := MCCusp.qf_nonneg hYpd.posSemidef _
  suffices h : y i ^ 2 ≤ K * MCSchur.qf (periodGram τ) y by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hKpos]
    linarith
  rw [hform y]
  by_cases hig : i.val < D.g
  · set k : Fin D.g := ⟨i.val, hig⟩ with hkdef
    have hik : i = Fin.castAdd D.g k := Fin.ext rfl
    have hkr : T.r ≤ k.val := hi
    have hyk : y i = α k := congrArg y hik
    have hYkk : Y k k ≤ M :=
      calc Y k k = (τ k k).im := rfl
        _ ≤ |(τ k k).im| := le_abs_self _
        _ ≤ ‖τ k k‖ := Complex.abs_im_le_norm _
        _ ≤ M := hMb p hp ℓ k k hkr
    have hXk : ∀ l, |X k l| ≤ M := fun l =>
      (Complex.abs_re_le_norm _).trans (hMb p hp ℓ k l hkr)
    have hu : (α + X *ᵥ β) k ^ 2 ≤ M * MCSchur.qf Y⁻¹ (α + X *ᵥ β) := by
      have h1 := MCCusp.sq_le_inv_diag_mul_qf hYpd.inv (α + X *ᵥ β) k
      rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hYpd.isUnit)]
        at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hYkk hA)
    have hw := CuspCoordinateBound.mulVec_sq_le X M k hXk β
    have hsplit : α k = (α + X *ᵥ β) k - (X *ᵥ β) k := by simp
    have hw2 : (X *ᵥ β) k ^ 2 ≤ D.g * M ^ 2 / D.c * MCSchur.qf Y β := by
      refine hw.trans ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have h0 : 0 ≤ (D.g : ℝ) * M ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (hYc β) h0]
    rw [hyk, hsplit]
    have hab : ((α + X *ᵥ β) k - (X *ᵥ β) k) ^ 2 ≤
        2 * (α + X *ᵥ β) k ^ 2 + 2 * (X *ᵥ β) k ^ 2 := by
      nlinarith [sq_nonneg ((α + X *ᵥ β) k + (X *ᵥ β) k)]
    have hid : K * (MCSchur.qf Y⁻¹ (α + X *ᵥ β) + MCSchur.qf Y β) =
        2 * M * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 2 * (D.g * M ^ 2 / D.c) * MCSchur.qf Y β +
          (1 / D.c * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 1 / D.c * MCSchur.qf Y β +
            2 * D.g * M ^ 2 / D.c * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 2 * M * MCSchur.qf Y β) := by
      rw [hK]; ring
    have hM2 : 0 ≤ 2 * M := by positivity
    rw [hid]
    nlinarith [mul_nonneg hK1 hA, mul_nonneg hK1 hB, mul_nonneg hK2 hA, mul_nonneg hM2 hB]
  · set k : Fin D.g := ⟨i.val - D.g, by omega⟩ with hkdef
    have hik : i = Fin.natAdd D.g k := Fin.ext (by simp [hkdef]; omega)
    have hyk : y i = β k := congrArg y hik
    have h1 := CuspCoordinateBound.coord_sq_le Y D.c hc hYc β k
    have h2 : β k ^ 2 ≤ 1 / D.c * MCSchur.qf Y β := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      linarith
    have hid : K * (MCSchur.qf Y⁻¹ (α + X *ᵥ β) + MCSchur.qf Y β) =
        1 / D.c * MCSchur.qf Y β + (K * MCSchur.qf Y⁻¹ (α + X *ᵥ β) +
          (2 * M + 2 * D.g * M ^ 2 / D.c) * MCSchur.qf Y β) := by
      rw [hK]; ring
    have hM2 : 0 ≤ 2 * M + 2 * D.g * M ^ 2 / D.c := by positivity
    rw [hyk, hid]
    nlinarith [mul_nonneg hKpos.le hA, mul_nonneg hM2 hB]
end CuspCoordinateBound
end GroundTheory.Heights₂.Heights
