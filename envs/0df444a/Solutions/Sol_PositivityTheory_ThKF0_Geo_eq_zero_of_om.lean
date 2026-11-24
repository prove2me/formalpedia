-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.eq_zero_of_om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:42.554013+00:00
-- url     : https://prove2.me/submissions/631f5371-dbd6-4d97-90e3-ed02f342bb77

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
theorem _root_.solution (w : (κ → F) × (κ → F)) (h : ∀ w', om F κ w' w = 0) : w = 0 := by
  classical
  have h1 : ∀ i, w.2 i = 0 := fun i => by
    have := h (Pi.single i 1, 0)
    simpa [om_apply, single_dotProduct] using this
  have h2 : ∀ i, w.1 i = 0 := fun i => by
    have := h (0, Pi.single i 1)
    simpa [om_apply, dotProduct_single] using this
  exact Prod.ext (funext h2) (funext h1)
end PositivityTheory.ThKF0.Geo
