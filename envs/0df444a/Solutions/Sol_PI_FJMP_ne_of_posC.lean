-- Prove2me | solution 1 for PI.FJMP.ne_of_posC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:21.90345+00:00
-- url     : https://prove2.me/submissions/a24425b0-24a8-4c31-b032-d49f7b250d2a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
namespace PI.FJMP
theorem _root_.solution {p q : ℕ} {a b : Ix p q} (h : posC a b) : a ≠ b := by
  intro hab
  subst hab
  rcases a with i | i <;> exact absurd h (by simp [posC])
end PI.FJMP
