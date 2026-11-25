-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_det_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:07.228345+00:00
-- url     : https://prove2.me/submissions/cbe123eb-4311-4719-9a5e-2d7435164f2f

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_factor
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_det_ge_one
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_congr
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_quad_self
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_norm_det_sq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_det_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hY : Y.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).re ≤ (star v ⬝ᵥ (Y *ᵥ v)).re) :
    0 < X.det.re ∧ X.det.re ≤ Y.det.re := by
  obtain ⟨B, hXB, hu⟩ := sdd_factor hX
  obtain ⟨hYe, hq⟩ := sdd_congr B Y hu
  have hDh : ((B⁻¹)ᴴ * Y * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hY.eq, Matrix.mul_assoc]
  obtain ⟨hDr, hD1⟩ := sdd_det_ge_one hDh (fun w => by
    rw [hq w, sdd_quad_self B hu w, ← hXB]
    exact h _)
  have hdetX : X.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hXB, sdd_norm_det_sq]
  have hBpos : 0 < ‖B.det‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu.ne_zero) 2
  rw [hdetX, hYe, sdd_det_congr, hDr, Complex.ofReal_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact ⟨hBpos, le_mul_of_one_le_right hBpos.le hD1⟩
end ReciprocityTheory.MultiplicativeHeights
