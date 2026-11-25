-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_mem_sq_of_gradAt_eq_zero_ba2ac002f700
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:47.345872+00:00
-- url     : https://prove2.me/submissions/4b2ab09c-a62d-48ce-a004-2021397c00d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_mul_of_eval_eq_zero_7e4ca727f22d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_X_sub_C_65f9f86f6e98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_expansion_8e7a532e1b86
import Theorems.Thm_UpperTheory_Reformulated_B_Qn12_exists_expansion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.TransverseSliceGeneral
theorem _root_.solution (q : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) (hp : eval q p = 0)
    (hg : gradAt q p = 0) : p ∈ RingHom.ker (eval q) ^ 2 := by
  obtain ⟨c, hc⟩ := exists_expansion q p
  rw [hp, map_zero, zero_add] at hc
  have hgrad : gradAt q p = ∑ i, eval q (c i) • (Pi.single i 1 : Fin n → ℂ) := by
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gradAt_mul_of_eval_eq_zero q _ _ (by simp), gradAt_X_sub_C]
  have hcj : ∀ j, eval q (c j) = 0 := by
    intro j
    have := congr_fun (hgrad.symm.trans hg) j
    simpa [Finset.sum_apply, Pi.single_apply] using this
  rw [hc, sq]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_mul (RingHom.mem_ker.2 (hcj i)) (by simp [RingHom.mem_ker])
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
