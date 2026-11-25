-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_relDim_eq_natCast_iff_cb89d927b72d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:27.299713+00:00
-- url     : https://prove2.me/submissions/cb180068-7512-4627-847b-b24c62594b5a

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
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution [Fintype K] (I : Ideal (MRing ι F)) (d : ℕ) :
    relDim I = ((d : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MRing ι F ⧸ I) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  unfold relDim
  cases hd : ringKrullDim (MRing ι F ⧸ I) using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.map_bot]
    exact iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)
  | coe y =>
    rw [WithBot.map_coe]
    cases y using ENat.recTopCoe with
    | top =>
      refine iff_of_false (fun h => ?_) (fun h => ?_)
      · exact WithTop.top_ne_coe (WithBot.coe_inj.mp h)
      · exact ENat.top_ne_natCast _ (WithBot.coe_inj.mp h)
    | coe e =>
      have key : WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) =
          (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := rfl
      rw [key]
      constructor
      · intro h
        have h1 : ((e : ℤ) - Fintype.card K : ℤ) = d := WithTop.coe_inj.mp (WithBot.coe_inj.mp h)
        have h2 : e = d + Fintype.card K := by omega
        rw [h2]
        rfl
      · intro h
        have h1 : (e : ℕ∞) = ((d + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_inj.mp h
        have h2 : e = d + Fintype.card K := by exact_mod_cast h1
        subst h2
        rw [show (((d + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = (d : ℤ) by push_cast; ring]
        rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
