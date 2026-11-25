-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.diag_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:25.035116+00:00
-- url     : https://prove2.me/submissions/1f7e2a8b-959d-448c-a754-3fb72aeec066

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
theorem _root_.solution [CharZero k] (i j : Fin n) (hij : i ≠ j) (c : k) :
    diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j (2 * c) := by
  ext a b
  simp only [mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Function.update_apply, Pi.one_apply, eq_comm (a := i) (b := a),
    eq_comm (a := j) (b := b)]
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>
    by_cases hjb : b = j <;> simp_all
end PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
