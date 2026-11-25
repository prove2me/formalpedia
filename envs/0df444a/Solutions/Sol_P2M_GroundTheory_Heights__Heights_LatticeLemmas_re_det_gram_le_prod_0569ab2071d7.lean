-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_0569ab2071d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:25.834798+00:00
-- url     : https://prove2.me/submissions/7f081665-9742-47c5-86db-4881f0f9c0d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_fin_5585265ad779
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → V) :
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  let e := (Fintype.equivFin ι).symm
  have h := re_det_gram_le_prod_fin (Fintype.card ι) (c ∘ e)
  rw [det_gram_comp_equiv e c] at h
  refine h.trans_eq ?_
  exact Fintype.prod_equiv e _ _ fun _ ↦ rfl
end GroundTheory.Heights₂.Heights.LatticeLemmas
