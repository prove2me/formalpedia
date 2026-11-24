-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.om_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:50.868889+00:00
-- url     : https://prove2.me/submissions/adf81873-8819-4ca0-9b7e-9269c429a279

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
import Theorems.Thm_PositivityTheory_ThKF0_Geo_om_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {F : Type} [Field F] {κ : Type} [Fintype κ]
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution : (om F κ).IsRefl := fun x y h => by
  rw [om_apply] at h ⊢
  linear_combination -h
end PositivityTheory.ThKF0.Geo
