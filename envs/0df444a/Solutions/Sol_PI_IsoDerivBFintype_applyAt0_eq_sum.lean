-- Prove2me | solution 1 for PI.IsoDerivBFintype.applyAt0_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:13.096721+00:00
-- url     : https://prove2.me/submissions/84f5db47-c182-4928-99d5-3ea428f3ba8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum

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
theorem _root_.solution (P : MvPolynomial (Idx T N N') ℂ) (S : Finset (Mono T N N'))
    (hS : P.support ⊆ S) : applyAt0 P Θ = ∑ α ∈ S, MvPolynomial.coeff α P * wt Θ α := by
  have e : ∀ α, MvPolynomial.coeff α P * wt Θ α =
      MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor Θ α := fun α => by
    unfold wt; ring
  simp only [e]
  unfold applyAt0
  apply Finset.sum_subset hS
  intro α _ hα
  rw [MvPolynomial.notMem_support_iff.mp hα]
  ring
end PI.IsoDerivBFintype
