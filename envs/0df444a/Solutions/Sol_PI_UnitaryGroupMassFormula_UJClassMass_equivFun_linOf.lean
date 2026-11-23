-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.equivFun_linOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:41.396284+00:00
-- url     : https://prove2.me/submissions/0f7f9a3d-b731-4a8a-94f6-e5e0c0d48cad

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
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (v : V) :
    b.equivFun (linOf b u v) = (u : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by
  unfold linOf
  first
  | simp only [LinearEquiv.ofLinear_apply, Matrix.toLin_apply, Basis.equivFun_apply,
      Basis.repr_sum_self]
  | simp [Matrix.toLin_apply, Basis.repr_sum_self]
  | (simp [Matrix.toLin_apply]
     ext j
     simp [Finset.sum_apply, Finsupp.single_apply])
end PI.UnitaryGroupMassFormula.UJClassMass
