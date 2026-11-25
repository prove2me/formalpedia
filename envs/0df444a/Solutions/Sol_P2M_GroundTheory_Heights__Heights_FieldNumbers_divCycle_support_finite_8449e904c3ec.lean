-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_divCycle_support_finite_8449e904c3ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:36.839651+00:00
-- url     : https://prove2.me/submissions/9c0f21e2-24e3-4c85-9d61-a09bd7b1d06a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational

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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (f : MRing ι F) :
    (Function.support (divCycle P f)).Finite := by
  apply (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F)
    (P ⊔ Ideal.span {f})).subset
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dif_neg (fun h' => h h'.1)]
end GroundTheory.Heights₂.Heights.FieldNumbers
