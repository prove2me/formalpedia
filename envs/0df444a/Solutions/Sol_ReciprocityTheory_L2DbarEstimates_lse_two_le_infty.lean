-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.lse_two_le_infty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:43:57.207867+00:00
-- url     : https://prove2.me/submissions/04145fd5-cc75-4815-814f-3b25b33aeb85

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_LseSmoothRIffReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact WithTop.coe_le_coe.mpr le_top
  | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  | simp
  | decide
end ReciprocityTheory.L2DbarEstimates
