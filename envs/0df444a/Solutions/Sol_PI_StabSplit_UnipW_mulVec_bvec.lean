-- Prove2me | solution 1 for PI.StabSplit.UnipW.mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:45.963861+00:00
-- url     : https://prove2.me/submissions/5b909632-82fa-4a77-a28e-5429d33f2b5e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    A *ᵥ bvec j = fun i => A i j := by
  funext i
  simp [bvec, Matrix.mulVec, Pi.single_apply]
end PI.StabSplit.UnipW
