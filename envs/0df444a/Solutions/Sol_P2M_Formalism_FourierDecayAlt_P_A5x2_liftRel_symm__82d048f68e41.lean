-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm__82d048f68e41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:09.440517+00:00
-- url     : https://prove2.me/submissions/c79288df-8547-4fb3-809c-571a4c388716

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    {v v' : Fin n → R} (h : LiftRel R k Z' Z φ.symm v' v) : LiftRel R k Z Z' φ v v' :=
  ⟨by rw [← h.1, φ.apply_symm_apply], fun j hj => (h.2 j hj).symm⟩
end Formalism.FourierDecayAlt.P.A5x2
