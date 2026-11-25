-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.epsT_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:04.099335+00:00
-- url     : https://prove2.me/submissions/38e9e316-3211-4cdc-8407-c04c2da62eb1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_adT_idem

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
theorem _root_.solution (T : Set (HeightOneSpectrum (𝓞 F))) : epsT E T * epsT E T = epsT E T := by
  unfold epsT
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, adT_idem]
end PI.UnitaryGroupMassFormula.UJClassMass
