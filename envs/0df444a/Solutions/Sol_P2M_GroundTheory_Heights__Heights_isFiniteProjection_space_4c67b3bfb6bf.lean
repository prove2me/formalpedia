-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isFiniteProjection_space_4c67b3bfb6bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:12:54.594852+00:00
-- url     : https://prove2.me/submissions/873bb6a0-45cc-4d67-8e6e-341b79f8bae0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_projHom_space_6b28d75ea3da

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (n : ℕ) :
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [projHom_space]
    intro a b h
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at h
    exact h
  · rw [projHom_space]
    exact RingHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective ℂ _)
end GroundTheory.Heights₂.Heights
