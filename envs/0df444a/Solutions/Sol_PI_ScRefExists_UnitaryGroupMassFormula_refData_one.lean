-- Prove2me | solution 1 for PI.ScRefExists.UnitaryGroupMassFormula.refData_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:25.204653+00:00
-- url     : https://prove2.me/submissions/5107eb92-91da-4671-b868-3b0f9337043e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.UnitaryGroupMassFormula
theorem _root_.solution (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) :
    Nonempty (RefData I 1 r k e f) := ⟨frameOne I r k e f he⟩
end PI.ScRefExists.UnitaryGroupMassFormula
