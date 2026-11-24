-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:39.732037+00:00
-- url     : https://prove2.me/submissions/111c3b5e-5a9a-4d06-b7ff-555df4afc2d0

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_eq_sum__18511f081048

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
theorem _root_.solution (F G : MvPolynomial σ ℚ_[p]) : fock p F G = fock p G F := by
  classical
  rw [fock_eq_sum' F G (F.support ∪ G.support) Finset.subset_union_left,
    fock_eq_sum' G F (F.support ∪ G.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring
end Formalism.InvariantFactorPaths.PW
