-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_foldr_diffStep_eventually_zero_dcb9c5e04ce2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:11.444357+00:00
-- url     : https://prove2.me/submissions/25709b5b-3dd0-4b5c-944f-0a01c11f7956

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_sub_const_atTop_5936cf0d3c49


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
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in Filter.atTop, h m = 0) :
    ∀ l : List (K → ℤ), ∀ᶠ m in Filter.atTop, l.foldr diffStep h m = 0
  | [] => hh
  | b :: l => by
    have ih := solution hh l
    filter_upwards [ih, (tendsto_sub_const_atTop b).eventually ih] with m h1 h2
    simp only [List.foldr_cons, diffStep, h1, h2, sub_self]
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
