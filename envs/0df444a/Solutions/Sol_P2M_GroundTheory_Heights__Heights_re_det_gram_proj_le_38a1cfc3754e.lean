-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_38a1cfc3754e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:31.455796+00:00
-- url     : https://prove2.me/submissions/67c62efe-e4aa-474d-95e7-263cd030e230

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_fin_76aed636b2ac

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Submodule ℂ V)
    [Y.HasOrthogonalProjection] (c : ι → V) :
    (det (gram ℂ fun i ↦ Y.starProjection (c i))).re ≤ (det (gram ℂ c)).re := by
  let e := (Fintype.equivFin ι).symm
  have h := re_det_gram_proj_le_fin Y (Fintype.card ι) (c ∘ e)
  rwa [det_gram_comp_equiv e c, show (fun i ↦ Y.starProjection ((c ∘ e) i)) =
    (fun i ↦ Y.starProjection (c i)) ∘ e from rfl, det_gram_comp_equiv] at h
end GroundTheory.Heights₂.Heights
