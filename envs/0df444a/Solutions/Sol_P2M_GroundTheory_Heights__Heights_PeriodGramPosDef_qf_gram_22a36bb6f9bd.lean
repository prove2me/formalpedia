-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_qf_gram_22a36bb6f9bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:26.092928+00:00
-- url     : https://prove2.me/submissions/9827283c-e11c-4104-9c97-cd2cb819e26e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodGramPosDef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_right_1caa0767354e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_left_42993b85aa56

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.PeriodGramPosDef
namespace GroundTheory.Heights₂.Heights.PeriodGramPosDef
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (b : κ → ι → ℂ)
    (x : κ → ℝ) :
    MCSchur.qf (Matrix.of fun i j => hermPair A (b i) (b j)) x =
      hermValue A (∑ i, (x i : ℂ) • b i) := by
  rw [hermValue, hermPair_sum_left]
  simp only [hermPair_sum_right, MCSchur.qf, dotProduct, mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end GroundTheory.Heights₂.Heights.PeriodGramPosDef
