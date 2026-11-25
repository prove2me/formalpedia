-- Prove2me | solution 1 for P2M_GlobalTheory_ZetaWide_order_zeta__eq_8b737bca923c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:26.636635+00:00
-- url     : https://prove2.me/submissions/c1cff9c4-450f-4001-9df1-0d5de6993c30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Theorems.Thm_P2M_GlobalTheory_ZetaWide_zeta__eq_af6bf53d4414

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
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt riemannZeta₁ s = analyticOrderNatAt riemannZeta s := by
  unfold analyticOrderNatAt
  have hev : riemannZeta₁ =ᶠ[nhds s] (fun z => z - 1) * riemannZeta := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact zeta₁_eq hz
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have h2 : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul h1 h2,
    h1.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hs), zero_add]
end GlobalTheory.ZetaWide
