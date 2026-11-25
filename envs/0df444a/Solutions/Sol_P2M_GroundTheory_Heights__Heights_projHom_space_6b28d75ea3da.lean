-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_projHom_space_6b28d75ea3da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:38:43.25956+00:00
-- url     : https://prove2.me/submissions/e3b4a5ee-0a1b-49eb-915f-d1b5ead36b44

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent

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
    projHom (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) =
      Ideal.Quotient.mkₐ ℂ ⊥ := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  simp [projHom, pullback, linPoly, Matrix.one_apply]
end GroundTheory.Heights₂.Heights
