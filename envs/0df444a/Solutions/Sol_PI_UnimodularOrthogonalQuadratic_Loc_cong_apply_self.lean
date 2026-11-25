-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.cong_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:38.662173+00:00
-- url     : https://prove2.me/submissions/bc63d0dc-b081-474c-9b0f-71a3c93b2fc6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnimodularOrthogonalQuadratic PI.UnimodularOrthogonalQuadratic.Loc
open Matrix
variable {S : Type} [CommRing S] [StarRing S]
namespace PI.UnimodularOrthogonalQuadratic.Loc
theorem _root_.solution {n : ℕ} (P H : Matrix (Fin n) (Fin n) S) (a : Fin n) :
    (P * H * Pᴴ) a a = q H (P a) := by
  simp only [mul_apply, q, conjTranspose_apply]
end PI.UnimodularOrthogonalQuadratic.Loc
