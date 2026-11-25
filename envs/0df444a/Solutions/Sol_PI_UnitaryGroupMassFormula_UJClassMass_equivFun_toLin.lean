-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.equivFun_toLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:06.122944+00:00
-- url     : https://prove2.me/submissions/142d69da-6a1c-4690-b7f7-eff48b62074c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA

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
    (b : Module.Basis (Fin M) E V) (A : Matrix (Fin M) (Fin M) E) (v : V) :
    b.equivFun (Matrix.toLin b b A v) = A.mulVec (b.equivFun v) := by
  rw [Matrix.toLin_apply, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rfl
end PI.UnitaryGroupMassFormula.UJClassMass
