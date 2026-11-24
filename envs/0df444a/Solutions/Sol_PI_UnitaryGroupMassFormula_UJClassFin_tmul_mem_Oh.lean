-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.tmul_mem_Oh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:58.744245+00:00
-- url     : https://prove2.me/submissions/98735397-cf59-4419-a17a-486616a52f7e

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
theorem _root_.solution {a : Af F} (ha : a ∈ intAf F) {e : E} (he : IsIntegral ℤ e) : a ⊗ₜ[F] e ∈ Oh F E := AddSubgroup.subset_closure ⟨a, ha, e, he, rfl⟩
end PI.UnitaryGroupMassFormula.UJClassFin
