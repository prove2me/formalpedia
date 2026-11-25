-- Prove2me | solution 1 for PI.IsoDerivBFintype.applyAt0_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:47.556824+00:00
-- url     : https://prove2.me/submissions/325d3908-5cba-4f67-a04a-71cbb2c59a36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Theorems.Thm_PI_IsoDerivBFintype_applyAt0_add
import Theorems.Thm_PI_IsoDerivBFintype_applyAt0_zero

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (∑ i ∈ s, P i) Θ = ∑ i ∈ s, applyAt0 (P i) Θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, applyAt0_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, applyAt0_add, ih]
end PI.IsoDerivBFintype
