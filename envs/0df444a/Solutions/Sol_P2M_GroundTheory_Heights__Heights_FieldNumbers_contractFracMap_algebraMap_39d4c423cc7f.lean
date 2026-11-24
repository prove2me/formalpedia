-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:48.351875+00:00
-- url     : https://prove2.me/submissions/56958363-f737-4ff7-8c78-051a472ba491

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree

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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
variable [DecidableEq K] [DecidableEq K']
variable {F : Type u} [Field F]
omit [DecidableEq K] [DecidableEq K']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (a : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') a)) =
      algebraMap _ (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') a)) := by
  unfold contractFracMap
  exact IsFractionRing.lift_algebraMap
    (g := ((IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (contractQuot j P')).toRingHom)
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      Ideal.quotientMap_injective) _
end GroundTheory.Heights₂.Heights.FieldNumbers
