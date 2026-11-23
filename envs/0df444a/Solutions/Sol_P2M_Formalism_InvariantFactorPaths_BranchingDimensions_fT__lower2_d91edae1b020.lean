-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower2_d91edae1b020
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:48.977297+00:00
-- url     : https://prove2.me/submissions/62c87466-cfe0-4aa9-bdbf-ee3fcd2c7ebf

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower_0adb6efea0e8

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
theorem _root_.solution (k' : ℕ) (y : ℝ) (hy : (k' : ℝ) ≤ y) (hk : 1 ≤ k') :
    (k' : ℝ) / (2 * y) ≤ fT' k' y := by
  have hk' : (0 : ℝ) < k' := by exact_mod_cast hk
  refine le_trans ?_ (fT'_lower k' y (by linarith))
  apply div_le_div_of_nonneg_left hk'.le (by linarith) (by linarith)
end Formalism.InvariantFactorPaths.BranchingDimensions
