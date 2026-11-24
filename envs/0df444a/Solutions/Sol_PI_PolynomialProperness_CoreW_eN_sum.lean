-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.eN_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:45.972518+00:00
-- url     : https://prove2.me/submissions/894266b2-b4f2-428e-bed4-5d7d09b86bd8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) :
    eN (∑ i ∈ s, f i) ≤ ∑ i ∈ s, eN (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eN]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (eN_add _ _).trans (add_le_add le_rfl ih)
end PI.PolynomialProperness.CoreW
