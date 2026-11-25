-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isFractionRing_of_div_9823530e3be1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:21.069751+00:00
-- url     : https://prove2.me/submissions/258cbbbd-9eec-4288-a9f2-a38e8e10a3c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank

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
variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    (inj : Function.Injective (algebraMap A K))
    (surj : ∀ z : K, ∃ x y : A, z = algebraMap A K x / algebraMap A K y) : IsFractionRing A K :=
  haveI := (faithfulSMul_iff_algebraMap_injective A K).mpr inj
  IsFractionRing.of_field A K surj
end GroundTheory.Heights₂.Heights.FieldNumbers
