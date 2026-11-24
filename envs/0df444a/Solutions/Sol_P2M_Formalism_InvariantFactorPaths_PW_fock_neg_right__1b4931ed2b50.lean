-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_PW_fock_neg_right__1b4931ed2b50
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:31.210241+00:00
-- url     : https://prove2.me/submissions/48ce2c00-cd62-42e5-9e88-925264a4c63c

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_smul_right__50546d9c35a2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) : fock p F (-G) = -fock p F G := by
  rw [← neg_one_smul ℚ_[p] G, fock_smul_right', neg_one_mul]
end Formalism.InvariantFactorPaths.PW
