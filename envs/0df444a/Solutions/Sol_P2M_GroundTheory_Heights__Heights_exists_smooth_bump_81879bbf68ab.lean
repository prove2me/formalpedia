-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_smooth_bump_81879bbf68ab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:54.863559+00:00
-- url     : https://prove2.me/submissions/ac4915f5-ff2c-4e2a-982b-6f7cd3cae0b0

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
    ∃ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f 0 = 1 := by
  obtain ⟨f, -, hc, hs, -, h0⟩ := exists_contDiff_tsupport_subset (E := Fin n → ℂ) (n := ⊤)
    (s := Metric.ball 0 1) (x := 0) (Metric.ball_mem_nhds 0 one_pos)
  exact ⟨f, hs, hc, h0⟩
end GroundTheory.Heights₂.Heights
