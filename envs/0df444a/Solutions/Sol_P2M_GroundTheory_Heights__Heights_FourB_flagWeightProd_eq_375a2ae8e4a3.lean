-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_flagWeightProd_eq_375a2ae8e4a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:42.414937+00:00
-- url     : https://prove2.me/submissions/3a21aea9-5cba-4d27-ba1f-01fdaac470e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
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
open ReciprocityTheory.AnForm
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (f N p : ℕ) (lam : Fin f → Fin N → ℝ) :
    flagWeightProd f N p lam = fun z => ∑ j : Fin f × Fin N, flagTerm f N p lam j z := by
  funext z
  simp only [flagWeightProd, flagWeight, flagTerm, Fintype.sum_prod_type]
end GroundTheory.Heights₂.Heights.FourB
