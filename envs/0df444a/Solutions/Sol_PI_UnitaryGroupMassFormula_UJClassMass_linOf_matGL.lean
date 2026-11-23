-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.linOf_matGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:29.313693+00:00
-- url     : https://prove2.me/submissions/c738c8bc-9b1f-4a35-9db8-e2df8deec9e8

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
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) (u : V ≃ₗ[E] V) : linOf b (matGL b u) = u := by
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin b b (LinearMap.toMatrix b b (u : V →ₗ[E] V)) v = u v
  rw [Matrix.toLin_toMatrix]
  rfl
end PI.UnitaryGroupMassFormula.UJClassMass
