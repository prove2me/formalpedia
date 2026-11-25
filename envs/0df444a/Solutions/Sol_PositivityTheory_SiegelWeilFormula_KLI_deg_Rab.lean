-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.deg_Rab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:38.41428+00:00
-- url     : https://prove2.me/submissions/bc2d543f-c038-4fd1-af95-af35ad210c66

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussianMomentRealCoords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution (α β : ℕ) : (Rab α β).totalDegree ≤ α + β := by
  have h1 : (X 0 + C I * X 1 : MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp only [totalDegree_X, le_refl]
    · refine (totalDegree_mul _ _).trans ?_
      simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  have h2 : (X 0 - C I * X 1 : MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp only [totalDegree_X, le_refl]
    · refine (totalDegree_mul _ _).trans ?_
      simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  unfold PositivityTheory.SiegelWeilFormula.KLI.Rab
  refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul le_rfl h1).trans_eq (mul_one _))
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul le_rfl h2).trans_eq (mul_one _))
end PositivityTheory.SiegelWeilFormula.KLI
