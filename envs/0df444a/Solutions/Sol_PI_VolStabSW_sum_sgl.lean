-- Prove2me | solution 1 for PI.VolStabSW.sum_sgl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:39.450453+00:00
-- url     : https://prove2.me/submissions/36971449-d914-4b4b-83cb-5155079a945d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensChLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabSW
open Classical
namespace PI.VolStabSW
theorem _root_.solution {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x := by
  simp only [sgl]
  exact Finset.univ_sum_single x
end PI.VolStabSW
