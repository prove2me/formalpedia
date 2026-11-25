-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.linOf_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:07.337975+00:00
-- url     : https://prove2.me/submissions/234f62ce-d9bf-4cd5-b89b-6153efbaa233

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) {U U' : GL (Fin M) E}
    (e : linOf b U = linOf b U') : U = U' := by
  apply Units.ext
  have := congrArg (fun w : V ≃ₗ[E] V => LinearMap.toMatrix b b (w : V →ₗ[E] V)) e
  simpa [linOf, LinearMap.toMatrix_toLin] using this
end PI.UnitaryGroupMassFormula.UJClassMass
