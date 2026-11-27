-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isCohenMacaulayAt_point_bc8cbda9b5ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:40.003887+00:00
-- url     : https://prove2.me/submissions/117e8241-27e8-4b44-a392-4082f6f9f415

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_field_898ab0d164d2

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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (q : Fin n → ℂ) :
    IsCohenMacaulayAt (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) q := by
  unfold IsCohenMacaulayAt localRingAt
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  let _ := Ideal.Quotient.field
    (maximalIdeal (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))
  exact isCohenMacaulayLocalRing_of_field _
end GroundTheory.Heights₂.Heights
