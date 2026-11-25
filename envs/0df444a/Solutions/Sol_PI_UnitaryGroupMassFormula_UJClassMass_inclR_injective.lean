-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.inclR_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:06.05733+00:00
-- url     : https://prove2.me/submissions/7d2ed83a-1ab4-4ea8-900c-82cd7f4060ee

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : Function.Injective (inclR (AF F) : E →+* AF F ⊗[F] E) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E)
    (algebraMap F (AF F)).injective
end PI.UnitaryGroupMassFormula.UJClassMass
