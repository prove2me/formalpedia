-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.weyl_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:47.433064+00:00
-- url     : https://prove2.me/submissions/4cd9dabf-e8bf-4f55-9686-d55ee0fad2d4

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Theorems.Thm_PositivityTheory_ThKR_LL_csmul
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {V : Sch l →L[ℂ] Sch l} {w v : l ⊕ l → ℝ} (h : ∀ f, dRho w (V f) = V (dRho v f))
    (A : Sch l →L[ℂ] Sch l) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (V f)) = ∑ a, v a • schwartzToL2 l (A (V (dRho (Pi.single a 1) f))) := by
  rw [ContinuousLinearMap.mul_apply, h, dRho_eq_sum v]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  simp only [csmul]
end PositivityTheory.ThKR.LL
