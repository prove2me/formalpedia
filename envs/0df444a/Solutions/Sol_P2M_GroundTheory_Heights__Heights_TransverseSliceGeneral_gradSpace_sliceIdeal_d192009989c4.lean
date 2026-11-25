-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradSpace_sliceIdeal_d192009989c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:43.837519+00:00
-- url     : https://prove2.me/submissions/67ee0350-f4cb-485b-8961-1cfe01e356cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_mul_of_eval_eq_zero_7e4ca727f22d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_linPoly_sub_044988d6fb10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385


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
theorem _root_.solution (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) :
    gradSpace (sliceIdeal W L q) q = gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    refine Submodule.add_mem_sup ⟨w, hw, rfl⟩ ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [gradAt_mul_of_eval_eq_zero q _ _ (by rw [map_sub, eval_linPoly, eval_C, sub_self]),
      gradAt_linPoly_sub]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Ideal.mem_sup_left hx, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩), gradAt_linPoly_sub q L i⟩
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
