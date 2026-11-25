-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.linOf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:45:23.728088+00:00
-- url     : https://prove2.me/submissions/c26eef71-8e31-4cfd-8f6e-d9e4f8a94b4a

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
theorem _root_.solution (b : Module.Basis (Fin M) E V) : linOf b (1 : GL (Fin M) E) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, Units.val_one, Matrix.one_mulVec]
  rfl
end PI.UnitaryGroupMassFormula.UJClassMass
