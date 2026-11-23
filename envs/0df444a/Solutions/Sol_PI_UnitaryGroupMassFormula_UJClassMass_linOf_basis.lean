-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.linOf_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:04.064869+00:00
-- url     : https://prove2.me/submissions/3659b896-c04b-4933-bfae-1c53332e10b0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (i : Fin M) :
    linOf b u (b i) = ∑ k, (u : Matrix (Fin M) (Fin M) E) k i • b k := by
  unfold linOf
  first
  | simp [Matrix.toLin_self]
  | rw [LinearEquiv.ofLinear_apply, Matrix.toLin_self]
end PI.UnitaryGroupMassFormula.UJClassMass
