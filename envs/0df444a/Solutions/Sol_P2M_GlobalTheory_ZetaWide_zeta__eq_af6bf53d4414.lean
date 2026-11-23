-- Prove2me | solution 1 for P2M_GlobalTheory_ZetaWide_zeta__eq_af6bf53d4414
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:03.366275+00:00
-- url     : https://prove2.me/submissions/1d989a82-3a89-48cd-997c-e189af6b839a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaWide
namespace GlobalTheory.ZetaWide
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]
end GlobalTheory.ZetaWide
