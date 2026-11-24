-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.om_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:48.543145+00:00
-- url     : https://prove2.me/submissions/0937bca2-db9b-41d4-8bdb-1e686d50ff3b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg

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
theorem _root_.solution (w w' : (κ → F) × (κ → F)) : om F κ w w' = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := rfl
end PositivityTheory.ThKF0.Geo
