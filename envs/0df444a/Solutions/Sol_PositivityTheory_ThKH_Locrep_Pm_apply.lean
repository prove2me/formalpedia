-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.Pm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:12.856259+00:00
-- url     : https://prove2.me/submissions/63b7d80c-b947-4ae7-9f8f-4adcf6bf7da2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution (φ : K → ℂ) (y : K) (Φ : A → ℂ) (x : A) : Pm ev ι φ y Φ x = φ (ev x) * Φ (put ev ι x y) := rfl
end PositivityTheory.ThKH.Locrep
