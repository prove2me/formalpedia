-- Prove2me | solution 1 for PI.FJMX.deriv_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:02.50389+00:00
-- url     : https://prove2.me/submissions/19503d5f-bf6d-4b59-a94d-a9b9ae43b7cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Theorems.Thm_PI_FJMX_deriv_finset_prod

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateCol i (fun k => D (M k i))).det := by
  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def, map_zsmul, deriv_finset_prod, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Units.smul_def]
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)]
  · rw [Matrix.updateCol_self]
end PI.FJMX
