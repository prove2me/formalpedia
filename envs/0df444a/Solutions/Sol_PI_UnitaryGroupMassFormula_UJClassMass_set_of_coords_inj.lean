-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.set_of_coords_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:34.344664+00:00
-- url     : https://prove2.me/submissions/5ab93e2e-5426-46b4-906b-fe8fa803a345

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) {A A' : Set (Fin M → E)}
    (e : {v : V | b.equivFun v ∈ A} = {v | b.equivFun v ∈ A'}) : A = A' := by
  ext x
  have h1 : b.equivFun.symm x ∈ {v : V | b.equivFun v ∈ A} ↔ b.equivFun.symm x ∈ {v : V | b.equivFun v ∈ A'} := by
    rw [e]
  simpa only [Set.mem_setOf_eq, LinearEquiv.apply_symm_apply] using h1
end PI.UnitaryGroupMassFormula.UJClassMass
