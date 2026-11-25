-- Prove2me | solution 1 for PI.ZW.order_zeta1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:47.617819+00:00
-- url     : https://prove2.me/submissions/8eccd3eb-9e67-4085-bdb7-4b887c536a00

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
import Theorems.Thm_PI_ZW_zeta1_eq_sub_one_mul_riemannZeta_of_ne_one
import Theorems.Thm_PI_ZW_analyticAt_riemannZeta_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt zeta1 s = analyticOrderNatAt riemannZeta s := by
  have hev : zeta1 =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact zeta1_eq_sub_one_mul_riemannZeta_of_ne_one hz
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have h2 := analyticAt_riemannZeta_of_ne hs
  simp only [analyticOrderNatAt]
  rw [analyticOrderAt_congr hev,
    show (fun z => (z - 1) * riemannZeta z) = (fun z : ℂ => z - 1) * riemannZeta from rfl,
    analyticOrderAt_mul h1 h2]
  have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
    (analyticOrderAt_eq_zero).2 (Or.inr (by simpa [sub_eq_zero] using hs))
  rw [h0, zero_add]
end PI.ZW
