-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eq_of_add_one_le_of_le_9a68ecf72589
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:07:15.764801+00:00
-- url     : https://prove2.me/submissions/cffdd2b2-82cf-4db7-aa80-08eb3667c12b

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
theorem _root_.solution {x : WithBot ℕ∞} {e : ℕ}
    (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) (h2 : ((e : ℕ) : WithBot ℕ∞) ≤ x) :
    x = ((e : ℕ) : WithBot ℕ∞) := by
  cases x using WithBot.recBotCoe with
  | bot => simp at h2
  | coe y =>
    cases y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
      have h2' := WithBot.coe_le_coe.mp h1'
      rw [top_add, top_le_iff] at h2'
      exact ENat.natCast_ne_top _ h2'
    | coe y =>
      have a1 : y + 1 ≤ e + 1 := by exact_mod_cast h1
      have a2 : e ≤ y := by exact_mod_cast h2
      have : y = e := by omega
      subst this
      rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
