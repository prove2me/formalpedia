-- Prove2me | solution 1 for PI.EF.Mfun_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:50.714942+00:00
-- url     : https://prove2.me/submissions/e71d7cbd-3c7b-456b-a251-e4a016806985

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_two_le_arg

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
theorem _root_.solution {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Mfun A C N t := by
  unfold Mfun
  have h := two_le_arg N t
  have h3 : 0 ≤ Real.log (4 * (N * (|t| + 2))) := Real.log_nonneg (by linarith)
  have h4 := abs_nonneg (Real.log (2 * C))
  have h5 := mul_nonneg hA.le h3
  linarith
end PI.EF
