-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.equivFun_osmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:03.504399+00:00
-- url     : https://prove2.me/submissions/3b4a0ab2-1e70-4002-9b80-1d3000e5e540

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) (s : 𝓞 E) (v : V) :
    b.equivFun (s • v) = (algebraMap (𝓞 E) E s) • b.equivFun v := by
  rw [← algebraMap_smul E s v, LinearEquiv.map_smul]
end PI.UnitaryGroupMassFormula.UJClassMass
