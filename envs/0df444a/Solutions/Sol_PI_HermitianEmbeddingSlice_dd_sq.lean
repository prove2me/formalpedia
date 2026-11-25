-- Prove2me | solution 1 for PI.HermitianEmbeddingSlice.dd_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:41:34.365168+00:00
-- url     : https://prove2.me/submissions/8f6bbed8-2d68-408a-a264-f21d48d2ff5c

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
theorem _root_.solution (j : Fin (k + 1)) : dd k j * dd k j = 1 := by
  unfold dd
  split_ifs <;> norm_num
end PI.HermitianEmbeddingSlice
