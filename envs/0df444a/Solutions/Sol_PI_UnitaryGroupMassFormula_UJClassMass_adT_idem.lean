-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.adT_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:47.915018+00:00
-- url     : https://prove2.me/submissions/594a1265-d70a-43b0-b339-039551849082

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_mul_of_subset


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
theorem _root_.solution (T : Set (HeightOneSpectrum (𝓞 F))) : adT T * adT T = adT T := by
  show ((0 : Ainf F), evT T) * ((0 : Ainf F), evT T) = ((0 : Ainf F), evT T)
  exact Prod.ext (mul_zero _) (evT_mul_of_subset (subset_refl T))
end PI.UnitaryGroupMassFormula.UJClassMass
