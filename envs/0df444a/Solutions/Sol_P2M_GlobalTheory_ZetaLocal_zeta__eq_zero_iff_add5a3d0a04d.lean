-- Prove2me | solution 1 for P2M_GlobalTheory_ZetaLocal_zeta__eq_zero_iff_add5a3d0a04d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:23.247578+00:00
-- url     : https://prove2.me/submissions/514851ff-6736-4cd2-999d-556608165afe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
import Theorems.Thm_P2M_GlobalTheory_ZetaLocal_zeta__eq_fc7653a25de8

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
theorem _root_.solution (w : ℂ) : riemannZeta₁ w = 0 ↔ w ≠ 1 ∧ riemannZeta w = 0 := by
  by_cases h : w = 1
  · simp [h]
  · simp [zeta₁_eq h, sub_ne_zero.2 h, h]
end GlobalTheory.ZetaLocal
