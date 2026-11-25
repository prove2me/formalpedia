-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_contract_coe_ebf358cf7871
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:24.198422+00:00
-- url     : https://prove2.me/submissions/583aa858-9ee5-4569-a753-0d35c0b28f43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForwardLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc

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
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace degZeroLoc
theorem _root_.solution (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (x : degZeroLoc (contractPrime j P') {W}) :
    ((algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) x :
      degZeroLoc P' (fibrePrimes j P' W)) : FractionRing (MRing ι' F ⧸ P')) =
      contractFracMap j P' x :=
  rfl
end degZeroLoc
end GroundTheory.Heights₂.Heights.FieldNumbers
