-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.linOf_one_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:02.51016+00:00
-- url     : https://prove2.me/submissions/8a18a0e5-a435-4081-adf0-7286b4a873ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_one_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : (linOf b (1 : GL (Fin M) E)).symm v = v := by
  rw [LinearEquiv.symm_apply_eq, linOf_one_apply]
end PI.UnitaryGroupMassFormula.UJClassMass
