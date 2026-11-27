-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankMeetsRegular_of_found_ebd6052fd369
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:58.40185+00:00
-- url     : https://prove2.me/submissions/c95eb867-1ccf-4199-a742-7e39ac1b7f25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjFullRankMeetsRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRankRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjFullRankMeetsRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjFullRankMeetsRegular
theorem _root_.solution (hT : ProjRankTransfer.Statement)
    (hM : ProjMaxRankMeetsPsi0.Statement) (hR : ProjMaxRankRegular.Statement) :
    ProjFullRankMeetsRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y, hyc, hy⟩ := hT K ι P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y', hyc', hy', h0⟩ := hM K ι P J n R Ψ V BV hH y hy
  refine ⟨y', ?_, hR K ι P J n R Ψ V BV hH y' hy' h0⟩
  rw [connectedComponent_eq hyc]
  exact hyc'
end ProjFullRankMeetsRegular
end GroundTheory.Heights₂.Heights.Targets
