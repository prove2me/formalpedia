-- Prove2me | solution 1 for PI.FJMX.minorPolynomial_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:14:22.203707+00:00
-- url     : https://prove2.me/submissions/4c5b07c6-a136-4552-a0db-b2c734a99c61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.FJMX
theorem _root_.solution {k : ℕ} (g : Fin k → Fin k → σ) (S : Set σ) (hS : ∀ i j, g i j ∈ S) :
    minorPolynomial R g ∈ supported R S := by
  classical
  rw [minorPolynomial, Matrix.det_apply']
  apply Subalgebra.sum_mem
  intro τ _
  apply Subalgebra.mul_mem
  · exact Subalgebra.intCast_mem _ _
  · apply Subalgebra.prod_mem
    intro i _
    simp only [Matrix.of_apply]
    exact Algebra.subset_adjoin ⟨g (τ i) i, hS _ _, rfl⟩
end PI.FJMX
