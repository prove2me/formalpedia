-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__anti_c3dd9c16a389
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:37.5398+00:00
-- url     : https://prove2.me/submissions/bf23340d-65d8-447b-9ffa-4735c50ebeef

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (k' : ℕ) (y y' : ℝ) (hy : 0 ≤ y) (h : y ≤ y') : fT' k' y' ≤ fT' k' y := by
  unfold fT'
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply one_div_le_one_div_of_le (by positivity) (by linarith)
end Formalism.InvariantFactorPaths.BranchingDimensions
