-- Prove2me | solution 1 for QmCapCommW.col_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:21.042987+00:00
-- url     : https://prove2.me/submissions/c5067cfe-425b-439b-9356-b03b6475f8ac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open QmCapCommW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QmCapCommW
theorem _root_.solution {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (h : ∀ j, Y j c = 0) : Y *ᵥ bvec c = 0 := by
  funext j
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, h]
end QmCapCommW
