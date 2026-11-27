-- Prove2me | solution 1 for P2M_Formalism_CL_W_Q___2d8d76d12fce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:49:34.131799+00:00
-- url     : https://prove2.me/submissions/701f29bb-dd94-4efe-a6db-6cc5466123dc

import Definitions.Def_Formalism_WachModuleLifts_StatementW
import Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CL Formalism.CL.W
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']
namespace Formalism.CL.W
theorem _root_.solution (W : WachMod B η D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x) := W.φ_N x hx
end Formalism.CL.W
