-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.hform_eq_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:52.152709+00:00
-- url     : https://prove2.me/submissions/8f104c6b-8d07-44c8-a18c-3016e28c9dd8

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hform_apply

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
theorem _root_.solution (σ : E →+* E) (hst : ∀ a : E, star a = σ a)
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : hform J x y = herm σ J x y := by
  simp only [hform_apply, herm, hst]
end PI.HermLatFin.UnitaryGroupMassFormula
