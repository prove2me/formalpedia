-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_top_234e7946562e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:12.530141+00:00
-- url     : https://prove2.me/submissions/de4009ec-97b1-4809-ab09-e426b2dce9e7

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
theorem _root_.solution (m : K → ℤ) : hilbFn (⊤ : Ideal (MRing ι F)) m = 0 := by
  unfold hilbFn
  split_ifs
  · have : gradedPiece (⊤ : Ideal (MRing ι F)) (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [Submodule.mem_bot]
      have : Subsingleton (MRing ι F ⧸ (⊤ : Ideal (MRing ι F))) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Subsingleton.elim _ _
    rw [this, finrank_bot, Nat.cast_zero]
  · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
