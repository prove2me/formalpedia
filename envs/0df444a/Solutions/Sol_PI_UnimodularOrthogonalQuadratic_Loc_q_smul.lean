-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.q_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:14.420212+00:00
-- url     : https://prove2.me/submissions/20ed29da-3cb0-4140-9a05-07ce413c8532

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) S) (u : S) (v : Fin n → S) :
    q H (u • v) = u * star u * q H v := by
  simp only [q, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end PI.UnimodularOrthogonalQuadratic.Loc
