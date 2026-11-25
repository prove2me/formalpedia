-- Prove2me | solution 1 for PI.HermitianEmbeddingSlice.dd_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:50.068905+00:00
-- url     : https://prove2.me/submissions/3b122bc3-55e3-4880-b84f-347b347b179f

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
theorem _root_.solution (j : Fin (k + 1)) : star (dd k j) = dd k j := by
  unfold dd
  split_ifs <;> simp
end PI.HermitianEmbeddingSlice
