-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.hform_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:45.891306+00:00
-- url     : https://prove2.me/submissions/b8b64237-b483-4d25-a94c-afa14d73ef9a

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.HermLatFin PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
variable [StarRing E] {n : ℕ}
namespace PI.HermLatFin.UnitaryGroupMassFormula
theorem _root_.solution (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform J x y = ∑ i, ∑ j, star (x i) * J i j * y j := rfl
end PI.HermLatFin.UnitaryGroupMassFormula
