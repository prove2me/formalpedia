-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_le_of_height_add_0297706b95e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:15.607436+00:00
-- url     : https://prove2.me/submissions/5903328c-9942-449c-a5f1-d6f02f6e3529

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular

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
theorem _root_.solution {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (hh : h ≤ 1)
    (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : ((e : ℕ) : WithBot ℕ∞) ≤ x := by
  cases x using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hsum
    exact WithBot.bot_ne_natCast _ hsum
  | coe y =>
    cases y using ENat.recTopCoe with
    | top => simp
    | coe y =>
      cases h using ENat.recTopCoe with
      | top => simp at hh
      | coe h =>
        have a1 : h + y = e + 1 := by exact_mod_cast hsum
        have a2 : h ≤ 1 := by exact_mod_cast hh
        have : e ≤ y := by omega
        exact_mod_cast this
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
