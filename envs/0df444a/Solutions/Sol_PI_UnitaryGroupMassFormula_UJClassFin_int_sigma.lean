-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.int_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:16:38.832008+00:00
-- url     : https://prove2.me/submissions/33372a94-f7c9-4f0f-8195-ba5284c7368d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (σ : E →+* E) {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (σ a) := ha.map σ.toIntAlgHom
end PI.UnitaryGroupMassFormula.UJClassFin
