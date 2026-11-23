-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:34.585048+00:00
-- url     : https://prove2.me/submissions/b4351694-c0df-4c78-86f6-9d1e80293352

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (L0 : Submodule (𝓞 E) V) {e : E} (he : IsIntegral ℤ e) {v : V} (hv : v ∈ L0) :
    e • v ∈ L0 := by
  let a : 𝓞 E := ⟨e, he⟩
  have ha : algebraMap (𝓞 E) E a = e := rfl
  rw [← ha, algebraMap_smul]
  exact L0.smul_mem a hv
end PI.UnitaryGroupMassFormula.UJClassMass
