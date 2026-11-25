-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_PW_fock_smul_left__f870cf5261a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:13.436352+00:00
-- url     : https://prove2.me/submissions/c6081c8c-4da1-4262-94f6-5029710b5d17

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
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
theorem _root_.solution (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p (c • F) G = c * fock p F G := by
  rw [fock_symm', fock_smul_right', fock_symm']
end Formalism.InvariantFactorPaths.PW
