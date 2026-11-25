-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.bc_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:44.374718+00:00
-- url     : https://prove2.me/submissions/63aa2be5-fdf2-4754-97f6-54cccf24322f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_inclR_injective

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
theorem _root_.solution {M : ℕ} :
    Function.Injective (bc (n := Fin M) (inclR (AF F) : E →+* AF F ⊗[F] E)) := by
  intro a a' e
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL (Fin M) (AF F ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) e
  exact inclR_injective this
end PI.UnitaryGroupMassFormula.UJClassMass
