-- Prove2me | solution 1 for PI.EF.two_le_arg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:28.660017+00:00
-- url     : https://prove2.me/submissions/bbdaf922-6778-4df3-8639-a02d9760c8d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_one_le_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (N : ℕ) [NeZero N] (t : ℝ) : (2 : ℝ) ≤ N * (|t| + 2) := by
  have h1 := one_le_level N
  have h2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  calc (2 : ℝ) = 1 * 2 := by ring
    _ ≤ N * (|t| + 2) := mul_le_mul h1 h2 (by norm_num) (by linarith)
end PI.EF
