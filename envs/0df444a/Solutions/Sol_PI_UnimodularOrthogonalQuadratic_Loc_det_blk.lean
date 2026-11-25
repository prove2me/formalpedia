-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.det_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:44.314439+00:00
-- url     : https://prove2.me/submissions/759ffc9c-97e6-4658-b597-e129241cdc24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_of_first_row_single

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
theorem _root_.solution {n : ℕ} (P : Matrix (Fin n) (Fin n) S) : (blk P).det = P.det := by
  rw [det_of_first_row_single _ (fun b => by simp [blk, Pi.single_apply])]
  congr 1
end PI.UnimodularOrthogonalQuadratic.Loc
