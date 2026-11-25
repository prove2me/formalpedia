-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.q_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:10.867235+00:00
-- url     : https://prove2.me/submissions/b170a601-e472-4b03-9278-20eca13b042a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_star_eq_of_herm

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
theorem _root_.solution {n : ℕ} {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) (v : Fin n → S) :
    star (q H v) = q H v := by
  simp only [q, star_sum, star_mul', star_star, star_eq_of_herm hH, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end PI.UnimodularOrthogonalQuadratic.Loc
