-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:34.76178+00:00
-- url     : https://prove2.me/submissions/888fbad2-1ff8-437e-a508-316d85c8efe2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (a : E) (x y : Fin M → E) : herm σ J x (a • y) = a * herm σ J x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.UnitaryGroupMassFormula.UJClassFin
