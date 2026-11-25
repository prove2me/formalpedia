-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_projHom_cone_X_abd38f0c6846
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:04.339085+00:00
-- url     : https://prove2.me/submissions/77dd344d-9180-432d-89a1-bf03a58a6b96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (i : Fin 2) :
    projHom coneIdeal coneProj (X i) = Ideal.Quotient.mk coneIdeal (X i.succ) := by
  fin_cases i <;> simp [projHom, pullback, linPoly, coneProj, Fin.sum_univ_three]
end GroundTheory.Heights₂.Heights.ComplexSets
