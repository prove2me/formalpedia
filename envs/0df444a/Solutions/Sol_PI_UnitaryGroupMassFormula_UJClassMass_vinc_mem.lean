-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.vinc_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:58:08.653851+00:00
-- url     : https://prove2.me/submissions/421d424f-2cd1-4dbc-8995-a465577bdcde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_intAf_one


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
theorem _root_.solution (L : Set (Fin M → E)) {x : Fin M → E} (hx : x ∈ L) : vinc (F := F) x ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨1, intAf_one, x, hx, rfl⟩
end PI.UnitaryGroupMassFormula.UJClassMass
