-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_left_42993b85aa56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:10.249894+00:00
-- url     : https://prove2.me/submissions/797d7709-fa28-4311-b3bf-1d27e742bf1c

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
    (v : κ → ι → ℂ) (w : ι → ℂ) (x : κ → ℝ) :
    hermPair A (∑ i, (x i : ℂ) • v i) w = ∑ i, x i * hermPair A (v i) w := by
  simp only [hermPair]
  rw [star_sum, sum_dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct, smul_eq_mul,
    Complex.re_ofReal_mul]
end GroundTheory.Heights₂.Heights.PeriodGramPosDef
