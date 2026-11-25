-- Prove2me | solution 1 for PI.IsoDerivBFintype.applyAt0_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:11.355736+00:00
-- url     : https://prove2.me/submissions/c3c25e6a-2d83-4b38-82aa-56b0d4248dc1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Theorems.Thm_PI_IsoDerivBFintype_applyAt0_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ)
namespace PI.IsoDerivBFintype
theorem _root_.solution (P Q : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (P + Q) Θ = applyAt0 P Θ + applyAt0 Q Θ := by
  classical
  rw [applyAt0_eq_sum Θ (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    applyAt0_eq_sum Θ P (P.support ∪ Q.support) subset_union_left,
    applyAt0_eq_sum Θ Q (P.support ∪ Q.support) subset_union_right, ← sum_add_distrib]
  exact sum_congr rfl fun α _ => by rw [MvPolynomial.coeff_add]; ring
end PI.IsoDerivBFintype
