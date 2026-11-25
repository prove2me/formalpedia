-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_cone_coe_8ba24d60fc2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:57:06.351208+00:00
-- url     : https://prove2.me/submissions/f76d9e92-9530-4b33-b1f2-487242033cf8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace degZeroLoc
theorem _root_.solution (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (x : degZeroLoc P {W}) :
    ((algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) x : coneLocal P W hPW) :
      FractionRing (MRing ι F ⧸ P)) = x :=
  rfl
end degZeroLoc
end GroundTheory.Heights₂.Heights.FieldNumbers
