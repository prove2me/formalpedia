-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_absDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:26.616336+00:00
-- url     : https://prove2.me/submissions/fdeb7ff0-a07b-4a22-957a-315958f6de45

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_factor
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_det_abs_le_one
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
theorem _root_.solution {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.IsHermitian)
    (h : ∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) :
    ‖C.det‖ ≤ A.det.re := by
  obtain ⟨B, hAB, hu⟩ := sdd_factor hA
  obtain ⟨hCe, hq⟩ := sdd_congr B C hu
  have hDh : ((B⁻¹)ᴴ * C * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hC.eq, Matrix.mul_assoc]
  have hD1 : ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ 1 := by
    apply sdd_det_abs_le_one hDh
    intro w
    rw [hq w, sdd_quad_self B hu w, ← hAB]
    exact h _
  have hdetA : A.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hAB, sdd_norm_det_sq]
  rw [hCe, sdd_det_congr, hdetA, Complex.ofReal_re, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖B.det‖ ^ 2 * ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ ‖B.det‖ ^ 2 * 1 := by gcongr
    _ = _ := mul_one _
end ReciprocityTheory.MultiplicativeHeights
