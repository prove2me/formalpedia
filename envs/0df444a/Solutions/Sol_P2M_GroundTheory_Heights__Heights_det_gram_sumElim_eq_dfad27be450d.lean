-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:43.668167+00:00
-- url     : https://prove2.me/submissions/898907af-3fbc-45e1-ab68-9bc85cc9f42f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_of_orthogonal_30fcb0026ad7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_sub_a3ffef1fbd7a

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) :
    det (gram ℂ (Sum.elim v u)) = det (gram ℂ v) *
      det (gram ℂ (fun j ↦ u j - (Submodule.span ℂ (Set.range v)).starProjection (u j))) := by
  set U := Submodule.span ℂ (Set.range v)
  have hmem : ∀ j, ∃ c : ι → ℂ, ∑ i, c i • v i = U.starProjection (u j) := fun j ↦
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem (u j))
  choose c hc using hmem
  have hu : (fun j ↦ u j - U.starProjection (u j)) = fun j ↦ u j - ∑ i, (of fun i j ↦ c j i) i j • v i := by
    funext j
    simp [hc]
  rw [← det_gram_sumElim_sub v u (of fun i j ↦ c j i), ← hu]
  refine det_gram_sumElim_of_orthogonal v _ fun i j ↦ ?_
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i))
    (U.sub_starProjection_mem_orthogonal (u j))
end GroundTheory.Heights₂.Heights
