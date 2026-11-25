-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_NefRestrict_proof_5f3005d2aa4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:52.099889+00:00
-- url     : https://prove2.me/submissions/fc49aba0-810c-447a-b1b1-16310433c60a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_single_ace98b650546

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace NefRestrict
theorem _root_.solution (hRT : RestrictTwist.Statement.{u, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle M M' r hr hnef pp _ hpp
  have hx : IsSubvar x pp 1 := ⟨hpp.isPrime, hpp.homog, hle.trans hpp.le, hpp.relevant, hpp.dim⟩
  obtain ⟨r₀, hr₀⟩ := hRT.1 k Ω N x K' y hxy hle 0
  have hM := hRL k Ω N x K' y hxy hle pp 1 hpp M M' r hr
  have hO := hRL k Ω N x K' y hxy hle pp 1 hpp (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have heq : interSum pp ![M'.toSubSystem] =ᶠ[atTop] interSum pp ![M.toSubSystem] := by
    filter_upwards [hM, hO] with c hMc hOc
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tensorSub_single, tensorSub_single]
    split_ifs
    · rw [hMc]
    · exact congrArg _ hOc
  have hnum : interNum pp ![M'.toSubSystem] = interNum pp ![M.toSubSystem] := by
    unfold interNum limUnder
    rw [Filter.map_congr heq]
  rw [hnum]
  exact hnef pp bot_le hx
end NefRestrict
end GroundTheory.Heights₂.Heights.Kleiman
