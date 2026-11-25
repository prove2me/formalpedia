-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.Jpq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:12.881308+00:00
-- url     : https://prove2.me/submissions/f5fb279a-7341-4ef0-98e9-323a4236c8e6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (M : ℕ) : Jpq M 0 = 1 := by
  unfold PI.UJClassFin.Jpq
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0
end PI.UnitaryGroupMassFormula.UJClassFin
