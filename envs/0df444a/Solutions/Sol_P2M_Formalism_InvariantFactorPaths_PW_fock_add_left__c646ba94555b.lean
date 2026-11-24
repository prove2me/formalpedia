-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_PW_fock_add_left__c646ba94555b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:41.666135+00:00
-- url     : https://prove2.me/submissions/5bdf2e68-cf96-4b03-ab15-865dde537681

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_add_right__407452ae58c2

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
theorem _root_.solution (F F' G : MvPolynomial σ ℚ_[p]) : fock p (F + F') G = fock p F G + fock p F' G := by
  rw [fock_symm', fock_add_right', fock_symm' F, fock_symm' F']
end Formalism.InvariantFactorPaths.PW
