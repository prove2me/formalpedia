-- Prove2me | solution 1 for PI.HermitianEmbeddingSlice.alg1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:41.46899+00:00
-- url     : https://prove2.me/submissions/2581f0f6-e523-4c22-b1ed-73b888efb823

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_StarSingleOne
import Theorems.Thm_PI_HermitianEmbeddingSlice_Hb_eq
import Theorems.Thm_PI_HermitianEmbeddingSlice_dd_sq


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
theorem _root_.solution (v : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : dd k j * (Hb k *ᵥ v) j = v j := by
  rw [Hb_eq, mulVec_diagonal, ← mul_assoc, dd_sq, one_mul]
end PI.HermitianEmbeddingSlice
