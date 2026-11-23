-- Prove2me | solution 1 for PI.IsoDerivBFintype.applyAt0_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:40.65098+00:00
-- url     : https://prove2.me/submissions/35b494fc-7f19-48f7-a156-5b290d757044

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
theorem _root_.solution (c : ℂ) (P : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (MvPolynomial.C c * P) Θ = c * applyAt0 P Θ := by
  classical
  rw [applyAt0_eq_sum Θ (MvPolynomial.C c * P) P.support ?_,
    applyAt0_eq_sum Θ P P.support subset_rfl, mul_sum]
  · exact sum_congr rfl fun α _ => by rw [MvPolynomial.coeff_C_mul]; ring
  · intro α hα
    rw [MvPolynomial.mem_support_iff] at hα ⊢
    rw [MvPolynomial.coeff_C_mul] at hα
    exact right_ne_zero_of_mul hα
end PI.IsoDerivBFintype
