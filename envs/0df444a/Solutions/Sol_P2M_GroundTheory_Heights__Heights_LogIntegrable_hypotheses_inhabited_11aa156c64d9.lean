-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogIntegrable_hypotheses_inhabited_11aa156c64d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:13.138682+00:00
-- url     : https://prove2.me/submissions/2ee0a4ef-0c12-426d-8658-dd1458bd8826

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_X_zero_not_mem_coneIdeal_a1ec09729f1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_hyps_b9b793686593


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
namespace LogIntegrable
theorem _root_.solution :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧
      linForm (Pi.single 0 (1 : ℂ)) ∉ coneIdeal ∧
      (∀ i : Fin 2, SmoothNear (zeroSet coneIdeal) ((fun _ => euclPot) i)) := by
  refine ⟨cone_hyps, ?_, fun _ => smoothNear_of_contDiff (contDiff_euclPot 3)⟩
  rw [linForm_single]
  exact X_zero_not_mem_coneIdeal
end LogIntegrable
end GroundTheory.Heights₂.Heights
