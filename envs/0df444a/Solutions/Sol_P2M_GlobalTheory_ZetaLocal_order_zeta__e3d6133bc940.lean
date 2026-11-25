-- Prove2me | solution 1 for P2M_GlobalTheory_ZetaLocal_order_zeta__e3d6133bc940
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:19.302473+00:00
-- url     : https://prove2.me/submissions/e2166d67-86aa-4361-aa5e-2e39a1accb7d

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
theorem _root_.solution {w : ℂ} (hw : w ≠ 1) :
    analyticOrderNatAt riemannZeta₁ w = analyticOrderNatAt riemannZeta w := by
  have h1 : riemannZeta₁ =ᶠ[nhds w] (fun s => s - 1) * riemannZeta := by
    filter_upwards [compl_singleton_mem_nhds hw] with s hs using zeta₁_eq hs
  have h2 : AnalyticAt ℂ riemannZeta w :=
    differentiableOn_riemannZeta.analyticAt (compl_singleton_mem_nhds hw)
  have h3 : AnalyticAt ℂ (fun s : ℂ => s - 1) w := by fun_prop
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr h1, analyticOrderAt_mul h3 h2,
    h3.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hw), zero_add]
end GlobalTheory.ZetaLocal
