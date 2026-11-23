-- Prove2me | solution 1 for PI.EF.one_le_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:15.755781+00:00
-- url     : https://prove2.me/submissions/89ed07bf-d02e-42df-8fc8-1d230b6e4e2b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr

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
theorem _root_.solution (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
end PI.EF
