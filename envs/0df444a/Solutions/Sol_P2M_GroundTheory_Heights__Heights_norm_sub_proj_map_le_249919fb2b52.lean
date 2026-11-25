-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_norm_sub_proj_map_le_249919fb2b52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:39:03.314991+00:00
-- url     : https://prove2.me/submissions/e3815f02-0872-4eb7-b515-2fd9f349333b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension

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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} [Fintype ι] (Y : Submodule ℂ V) [Y.HasOrthogonalProjection]
    (c : ι → V) (x : V) :
    ‖Y.starProjection x - (Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))).starProjection
        (Y.starProjection x)‖ ≤ ‖x - (Submodule.span ℂ (Set.range c)).starProjection x‖ := by
  set U := Submodule.span ℂ (Set.range c)
  set U' := Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem x)
  have hmem : Y.starProjection (U.starProjection x) ∈ U' := by
    rw [← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 : ‖Y.starProjection x - U'.starProjection (Y.starProjection x)‖ ≤
      ‖Y.starProjection x - Y.starProjection (U.starProjection x)‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (⟨_, hmem⟩ : U')
  refine h1.trans ?_
  rw [← map_sub]
  exact Y.norm_starProjection_apply_le _
end GroundTheory.Heights₂.Heights
