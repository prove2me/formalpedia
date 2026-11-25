-- Prove2me | solution 1 for P2M_Formalism_CoboundaryTransfers_chase_Q___f9ab1d245c0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:36.377994+00:00
-- url     : https://prove2.me/submissions/99cfd518-ecc2-4de3-b3d2-8b84a82454ba

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x) := by
  show B.Q ^ M • W.φ x ∈ W.N
  exact W.φ_N x hx
end Formalism.CoboundaryTransfers
