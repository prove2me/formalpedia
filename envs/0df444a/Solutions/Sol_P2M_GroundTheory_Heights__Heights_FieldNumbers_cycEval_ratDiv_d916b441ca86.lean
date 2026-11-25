-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_cycEval_ratDiv_d916b441ca86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:49.08161+00:00
-- url     : https://prove2.me/submissions/b8a2d8fa-fa84-40ca-9e13-a5cb28b5dd2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_divCycle_support_finite_8449e904c3ec

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
    {ι : K → Type} [∀ k, Fintype (ι k)] (N : Ideal (MRing ι F) → ℤ) (P : Ideal (MRing ι F))
    (f g : MRing ι F) :
    cycEval N (ratDiv P f g) = cycEval N (divCycle P f) - cycEval N (divCycle P g) := by
  simp only [cycEval, ratDiv, sub_mul]
  apply finsum_sub_distrib
  · exact (divCycle_support_finite P f).subset (Function.support_mul_subset_left _ _)
  · exact (divCycle_support_finite P g).subset (Function.support_mul_subset_left _ _)
end GroundTheory.Heights₂.Heights.FieldNumbers
