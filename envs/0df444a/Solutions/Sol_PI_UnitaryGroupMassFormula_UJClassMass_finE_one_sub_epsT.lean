-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.finE_one_sub_epsT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:55:50.022317+00:00
-- url     : https://prove2.me/submissions/8a2c6326-a388-452d-b8cf-f581911deb7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finE_epsT
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_compl


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
theorem _root_.solution (T : Set (HeightOneSpectrum (𝓞 F))) :
    finE F E (1 - epsT E T) = evT Tᶜ ⊗ₜ[F] (1 : E) := by
  rw [map_sub, map_one, finE_epsT, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
  congr 1
  rw [← evT_compl Tᶜ, compl_compl]
end PI.UnitaryGroupMassFormula.UJClassMass
