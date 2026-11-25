-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_maximalIdeal_le_span_of_le_sup_sq_ffe074678903
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:34.375258+00:00
-- url     : https://prove2.me/submissions/baeac635-7ffa-4411-b514-b459df96bad5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (T : Set R)
    (h : IsLocalRing.maximalIdeal R ≤ Ideal.span T ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R ≤ Ideal.span T := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rwa [Ideal.smul_eq_mul, ← pow_two]
end GroundTheory.Heights₂.Heights
