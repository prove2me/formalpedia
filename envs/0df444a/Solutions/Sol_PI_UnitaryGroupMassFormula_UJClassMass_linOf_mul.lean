-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.linOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:15.221118+00:00
-- url     : https://prove2.me/submissions/4267a785-4b82-4803-a2b6-8d5eafbae00d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LatticesCloseLocally
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivFun_linOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (b : Module.Basis (Fin M) E V) (u w : GL (Fin M) E) :
    linOf b (u * w) = linOf b u * linOf b w := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, LinearEquiv.mul_apply, equivFun_linOf, equivFun_linOf, Units.val_mul,
    Matrix.mulVec_mulVec]
end PI.UnitaryGroupMassFormula.UJClassMass
