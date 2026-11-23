-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.cons_comp_finRotate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:10.25892+00:00
-- url     : https://prove2.me/submissions/dccd250b-22d0-4945-94e1-421ecd4468c2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
theorem _root_.solution {n t : ℕ} (e : Fin n) (f : Fin t → Fin n) :
    bE e f ∘ (finRotate (t + 1) : Fin (t + 1) → Fin (t + 1)) = bS f e := by
  unfold bE bS
  rw [Fin.snoc_eq_cons_rotate]
  rfl
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
