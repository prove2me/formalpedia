-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.crd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:08.318518+00:00
-- url     : https://prove2.me/submissions/f9149216-80ae-4c4c-af52-f8ae6328ca6b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivFun_osmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_iff_crdOf


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
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 F) (w : V) :
    algebraMap (𝓞 F) (𝓞 E) s • w ∈ L0 ↔ (algebraMap (𝓞 F) F s) • b.equivFun w ∈ crdOf b L0 := by
  rw [mem_iff_crdOf b L0, equivFun_osmul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 F) F E, algebraMap_smul]
end PI.UnitaryGroupMassFormula.UJClassMass
