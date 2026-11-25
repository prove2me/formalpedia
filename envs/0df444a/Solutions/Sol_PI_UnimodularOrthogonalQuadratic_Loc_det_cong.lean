-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.det_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:49.187934+00:00
-- url     : https://prove2.me/submissions/3b51aa14-73bd-4bfd-95a1-1c9effe75464

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
theorem _root_.solution {n : ℕ} {P H : Matrix (Fin n) (Fin n) S} (hP : IsUnit P.det) (hH : IsUnit H.det) :
    IsUnit (P * H * Pᴴ).det := by
  rw [det_mul, det_mul, det_conjTranspose]
  exact (hP.mul hH).mul hP.star
end PI.UnimodularOrthogonalQuadratic.Loc
