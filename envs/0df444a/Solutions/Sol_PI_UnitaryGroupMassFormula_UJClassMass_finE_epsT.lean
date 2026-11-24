-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.finE_epsT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:10:05.568133+00:00
-- url     : https://prove2.me/submissions/7fe1cd11-c7ab-4c6e-9cd3-a89a0d6b8f0d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (T : Set (HeightOneSpectrum (𝓞 F))) : finE F E (epsT E T) = evT T ⊗ₜ[F] (1 : E) := by
  unfold epsT
  rw [finE, Algebra.TensorProduct.map_tmul]
  rfl
end PI.UnitaryGroupMassFormula.UJClassMass
