-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linForm_single_not_mem_bot_952292a2748a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:37.908794+00:00
-- url     : https://prove2.me/submissions/37ba6683-5321-44f5-b33c-72151acb3b6d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b

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
theorem _root_.solution {n : ℕ} (i : Fin n) :
    linForm (Pi.single i (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) := by
  rw [linForm_single, Ideal.mem_bot]
  exact X_ne_zero i
end GroundTheory.Heights₂.Heights
