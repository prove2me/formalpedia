-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.equivFun_linOf_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:46.51327+00:00
-- url     : https://prove2.me/submissions/e892cf18-58af-40c4-9029-3376b69985ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivFun_toLin

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
    (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (v : V) :
    b.equivFun ((linOf b U).symm v) = ((U⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by
  rw [← equivFun_toLin]
  rfl
end PI.UnitaryGroupMassFormula.UJClassMass
