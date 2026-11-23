-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.star_eq_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:52.79412+00:00
-- url     : https://prove2.me/submissions/931728b2-30f4-45e0-b2cc-24773dc8b6d8

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
theorem _root_.solution {n : ℕ} {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) (k l : Fin n) :
    star (H k l) = H l k := by
  rw [← conjTranspose_apply, hH]
end PI.UnimodularOrthogonalQuadratic.Loc
