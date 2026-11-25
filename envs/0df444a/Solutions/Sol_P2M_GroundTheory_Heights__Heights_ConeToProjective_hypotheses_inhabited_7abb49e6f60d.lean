-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeToProjective_hypotheses_inhabited_7abb49e6f60d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:22.438503+00:00
-- url     : https://prove2.me/submissions/8b3046d1-e53a-4d8d-8c10-9f2007dfc250

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isProjPrime_line_6c88d2fbf567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_linForm_line_66a12de41669


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
namespace ConeToProjective
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (1 + 1) LineChowForm.D2 ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      (∀ (t : ℂ) (x : Fin 2 → ℂ), t ≠ 0 → (fun _ => (1 : ℝ)) (t • x) = (fun _ => (1 : ℝ)) x) ∧
      ContinuousOn (fun _ : Fin 2 → ℂ => (1 : ℝ)) {x | x ≠ 0} :=
  ⟨LineChowForm.isProjPrime_line, LineChowForm.isChowForm_line, LineChowForm.linForm_line,
    fun _ _ _ => rfl, continuousOn_const⟩
end ConeToProjective
end GroundTheory.Heights₂.Heights
