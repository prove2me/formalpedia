-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.crd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:13.639882+00:00
-- url     : https://prove2.me/submissions/24a3e262-1e6e-4084-8831-0bd8d3879ae9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {ι : Type*} (s : Finset ι)
    (f : ι → Fin M → E) (hf : ∀ i ∈ s, f i ∈ crdOf b L0) : ∑ i ∈ s, f i ∈ crdOf b L0 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact crd_zero b L0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact crd_add b L0 (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end PI.UnitaryGroupMassFormula.UJClassMass
