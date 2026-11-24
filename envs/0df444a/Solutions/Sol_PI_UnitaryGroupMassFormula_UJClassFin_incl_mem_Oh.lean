-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.incl_mem_Oh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:57:15.736408+00:00
-- url     : https://prove2.me/submissions/74f13a32-f3eb-499a-a823-fc71ef90839d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_intAf_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution {e : E} (he : IsIntegral ℤ e) : inclR (Af F) e ∈ Oh F E :=
  tmul_mem_Oh intAf_one he
end PI.UnitaryGroupMassFormula.UJClassFin
