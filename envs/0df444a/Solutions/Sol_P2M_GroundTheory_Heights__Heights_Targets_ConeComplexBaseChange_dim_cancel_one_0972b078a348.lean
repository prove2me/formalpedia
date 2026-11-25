-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_dim_cancel_one_0972b078a348
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:08.05247+00:00
-- url     : https://prove2.me/submissions/70986302-ee87-4163-b8ea-5ddbb6398bf5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeComplexBaseChange
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_withBot_enat_cancel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
theorem _root_.solution {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by
  refine ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel (h := 1) (N := N + 1) ?_ ?_
  · rw [add_comm]; exact_mod_cast h
  · push_cast; rw [add_comm]
end GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
