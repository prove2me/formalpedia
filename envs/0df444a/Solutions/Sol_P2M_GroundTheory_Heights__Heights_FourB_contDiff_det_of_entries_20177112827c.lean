-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_contDiff_det_of_entries_20177112827c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:31.454106+00:00
-- url     : https://prove2.me/submissions/a1a6f0c1-acf2-48eb-966d-be853e44fcd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Type*} [Fintype m] [DecidableEq m] {M : E → Matrix m m ℂ}
    (h : ∀ a b, ContDiff ℝ 2 fun x => M x a b) : ContDiff ℝ 2 fun x => (M x).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  exact (contDiff_prod fun a _ => h _ _).const_smul _
end GroundTheory.Heights₂.Heights.FourB
