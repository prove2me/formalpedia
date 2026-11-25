-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_coneHom_eq_zero_iff_9bc14c5accda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:17.026808+00:00
-- url     : https://prove2.me/submissions/0a81f00e-e48e-46d1-aab9-2f23d25b3163

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
variable {k : Type u} [Field k] {N : ℕ}
variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]
namespace GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
theorem _root_.solution (f : OneRing k N) :
    coneHom.{u, w} pp f = 0 ↔ oneBlock (S := k) (N := N) f ∈ pp := by
  show (Shrink.algEquiv k (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom))).symm
    (algebraMap _ (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) (Ideal.Quotient.mk (pp.comap (oneBlock (S := k) (N := N)).toRingHom) f)) = 0 ↔ _
  rw [map_eq_zero_iff _ (AlgEquiv.injective _), IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
