-- Prove2me | solution 1 for PI.HermitianEmbeddingSlice.Hb_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:51.775526+00:00
-- url     : https://prove2.me/submissions/b9025787-315d-4acc-86e3-7b7b435fa1d5

import Definitions.Def_Formalism_PeriodIntegrals_BordSlice
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HermitianEmbeddingSlice
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
variable {k r : ℕ}
namespace PI.HermitianEmbeddingSlice
theorem _root_.solution : Hb k = diagonal (dd k) := rfl
end PI.HermitianEmbeddingSlice
