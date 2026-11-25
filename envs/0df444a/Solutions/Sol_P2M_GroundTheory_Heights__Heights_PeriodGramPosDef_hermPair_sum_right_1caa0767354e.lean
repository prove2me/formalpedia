-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_right_1caa0767354e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:11.800697+00:00
-- url     : https://prove2.me/submissions/141609b9-4195-4dd2-9fa2-b0484668c94d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodGramPosDef

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ)
    (v : ι → ℂ) (w : κ → ι → ℂ) (x : κ → ℝ) :
    hermPair A v (∑ j, (x j : ℂ) • w j) = ∑ j, x j * hermPair A v (w j) := by
  simp only [hermPair]
  rw [mulVec_sum, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
end GroundTheory.Heights₂.Heights.PeriodGramPosDef
