-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue___apply_01e9e3406336
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:02.570843+00:00
-- url     : https://prove2.me/submissions/39e6c0e4-35e5-46b0-8151-f3eb64baf880

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocResidue

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000
open GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
variable {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
local notation "fr" Q:max h:max =>
  algebraMap (_ ⧸ Q) (FractionRing (_ ⧸ Q)) (Ideal.Quotient.mk Q h)
variable {P W : Ideal (MRing ι F)} [P.IsPrime] [W.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
theorem _root_.solution (hPW : P ≤ W) (x : degZeroLoc P {W}) : ρ hPW x = res P W x := rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
