-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.isIntegral_of_intOE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:53:11.434001+00:00
-- url     : https://prove2.me/submissions/ad327f5b-af81-4292-88d1-68609a6b98c8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE

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
theorem _root_.solution {e : E} (he : e ∈ Formalism.UG.intOE E) : IsIntegral ℤ e := by
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp he
  exact RingOfIntegers.isIntegral_coe a
end PI.UnitaryGroupMassFormula.UJClassFin
