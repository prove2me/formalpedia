-- Prove2me | solution 1 for PI.FJMX.deriv_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:16.17497+00:00
-- url     : https://prove2.me/submissions/dd92048f-9ac6-40e4-b698-b9951f996407

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
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace PI.FJMX
theorem _root_.solution {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (s : Finset ι)
    (f : ι → A) : D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    simp only [smul_eq_mul]
    rw [add_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring
end PI.FJMX
