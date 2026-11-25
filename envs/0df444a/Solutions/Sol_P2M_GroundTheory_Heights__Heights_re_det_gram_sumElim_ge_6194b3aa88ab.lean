-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_re_det_gram_sumElim_ge_6194b3aa88ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:45.689309+00:00
-- url     : https://prove2.me/submissions/013fec39-ce76-42b2-b240-c01a8b9d0ba4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_im_det_gram_c16ade0b03f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_re_nonneg_5b1b926b272e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_38a1cfc3754e

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
    (W : Submodule ℂ V) [W.HasOrthogonalProjection] (v : ι → V) (hv : ∀ i, v i ∈ W) (u : κ → V) :
    (det (gram ℂ v)).re * (det (gram ℂ fun j ↦ Wᗮ.starProjection (u j))).re ≤
      (det (gram ℂ (Sum.elim v u))).re := by
  set U := Submodule.span ℂ (Set.range v)
  have hUW : U ≤ W := Submodule.span_le.mpr (Set.range_subset_iff.mpr hv)
  rw [det_gram_sumElim_eq, Complex.mul_re, im_det_gram v, zero_mul, sub_zero]
  refine mul_le_mul_of_nonneg_left ?_ (det_gram_re_nonneg v)
  have hQ : (fun j ↦ Wᗮ.starProjection (u j)) =
      fun j ↦ Wᗮ.starProjection (u j - U.starProjection (u j)) := by
    funext j
    rw [map_sub, sub_eq_self.mpr]
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal W (hUW (U.starProjection_apply_mem (u j)))
  rw [hQ]
  exact re_det_gram_proj_le Wᗮ _
end GroundTheory.Heights₂.Heights
