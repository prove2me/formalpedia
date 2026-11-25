-- Prove2me | solution 1 for PIW.HCFdeg.toL2Map_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:21:58.391579+00:00
-- url     : https://prove2.me/submissions/892bfbbf-aaca-4e3d-bc33-7f1525ccc6fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_ContinuousToL2Map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory Filter Topology
variable {X H : Type} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
namespace PIW.HCFdeg
theorem _root_.solution (c : H →ₗ[ℂ] (X → ℂ)) (hL : ∀ v, MemLp (c v) 2 μ) (v : H) :
    toL2Map c hL v = (hL v).toLp (c v) := rfl
end PIW.HCFdeg
