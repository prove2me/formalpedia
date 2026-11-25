-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.linOf_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:46:14.028774+00:00
-- url     : https://prove2.me/submissions/390959fd-4acc-4628-9aa3-942c9b62a90b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : linOf b (1 : GL (Fin M) E) v = v := by
  simp [linOf]
end PI.UnitaryGroupMassFormula.UJClassMass
