-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_intNum_eq_zero_of_eventually_fcf290f727c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:48:49.545508+00:00
-- url     : https://prove2.me/submissions/338b0eca-9bb4-42b1-856e-64694074b262

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_foldr_diffStep_eventually_zero_dcb9c5e04ce2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eventualValue_eq_zero_39edb4ed1474

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
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution {I : Ideal (MRing ι F)}
    (hI : ∀ᶠ m in Filter.atTop, hilbFn I m = 0) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F I bs = 0 :=
  eventualValue_eq_zero (foldr_diffStep_eventually_zero hI (List.ofFn bs))
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
