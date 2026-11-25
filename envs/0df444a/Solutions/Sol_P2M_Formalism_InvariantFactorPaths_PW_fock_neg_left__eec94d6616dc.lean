-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_PW_fock_neg_left__eec94d6616dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:11.734212+00:00
-- url     : https://prove2.me/submissions/6564084f-2805-45ce-a440-9a604c50c1de

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_neg_right__1b4931ed2b50

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
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) : fock p (-F) G = -fock p F G := by
  rw [fock_symm', fock_neg_right', fock_symm']
end Formalism.InvariantFactorPaths.PW
