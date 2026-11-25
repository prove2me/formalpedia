-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.herm_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:07.435301+00:00
-- url     : https://prove2.me/submissions/b08cc3a4-817d-44ef-9bdb-b42e61607cee

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
theorem _root_.solution {n : ℕ} (P : Matrix (Fin n) (Fin n) S) {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) :
    (P * H * Pᴴ)ᴴ = P * H * Pᴴ := by
  simp [conjTranspose_mul, hH, Matrix.mul_assoc]
end PI.UnimodularOrthogonalQuadratic.Loc
