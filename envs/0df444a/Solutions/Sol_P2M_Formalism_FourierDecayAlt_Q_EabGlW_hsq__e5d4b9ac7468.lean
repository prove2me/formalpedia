-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:59:54.133091+00:00
-- url     : https://prove2.me/submissions/cc3f3af2-fb3d-48ba-84fe-f23fdfe74ddd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution (M : Mx k r) : Hpk k r * (Hpk k r * M) = M := by
  rw [← Matrix.mul_assoc, hsq, Matrix.one_mul]
end Formalism.FourierDecayAlt.Q.EabGlW
