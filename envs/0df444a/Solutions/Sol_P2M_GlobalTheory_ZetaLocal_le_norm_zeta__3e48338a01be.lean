-- Prove2me | solution 1 for P2M_GlobalTheory_ZetaLocal_le_norm_zeta__3e48338a01be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:10.158145+00:00
-- url     : https://prove2.me/submissions/a66c5863-8a48-49bf-81de-9325f68593b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
import Theorems.Thm_P2M_GlobalTheory_ZetaLocal_zeta__eq_fc7653a25de8
import Theorems.Thm_GlobalTheory_LLower_norm_LFunction_ge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaLocal
namespace GlobalTheory.ZetaLocal
theorem _root_.solution (t : ℝ) : 1 / 6 ≤ ‖riemannZeta₁ (3/2 + t * I)‖ := by
  set w : ℂ := 3/2 + t * I with hw
  have hre : w.re = 3 / 2 := by simp [hw]
  have h : w ≠ 1 := by
    intro h; rw [h] at hre; norm_num at hre
  have h1 := GlobalTheory.LLower.norm_LFunction_ge 1 (1 : DirichletCharacter ℂ 1) w (by rw [hre]; norm_num)
  rw [LFunction_modOne_eq, hre] at h1
  have h2 : 1 / 2 ≤ ‖w - 1‖ := by
    refine le_trans ?_ (re_le_norm _)
    rw [sub_re, hre]; norm_num
  rw [zeta₁_eq h, norm_mul]
  nlinarith
end GlobalTheory.ZetaLocal
