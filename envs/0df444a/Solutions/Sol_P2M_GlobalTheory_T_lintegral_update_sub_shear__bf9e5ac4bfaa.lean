-- Prove2me | solution 1 for P2M_GlobalTheory_T_lintegral_update_sub_shear__bf9e5ac4bfaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:12.885192+00:00
-- url     : https://prove2.me/submissions/cab837ba-f03e-4d6d-b513-7da39afab125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUpdateSubShear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUpdateSubShearStatement
import Theorems.Thm_GlobalTheory_lintegral_update_sub_shear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (g : (ι → ℂ) → ℂ), Measurable g → (∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v) → ∀ F : (ι → ℂ) → ℝ≥0∞, Measurable F → ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by
  first | exact @GlobalTheory.lintegral_update_sub_shear | exact GlobalTheory.lintegral_update_sub_shear | (intros; apply GlobalTheory.lintegral_update_sub_shear <;> assumption)
end _root_.GlobalTheory.T
