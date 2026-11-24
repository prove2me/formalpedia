-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.emb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:36.743993+00:00
-- url     : https://prove2.me/submissions/01d55a04-8006-4744-bc2a-0297882f4ec4

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
variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution {κ : Type} (w : (κ → F) × (κ → F)) :
    emb A κ w = (fun i => algebraMap F A (w.1 i), fun i => algebraMap F A (w.2 i)) := rfl
end PositivityTheory.ThKF0.Geo
