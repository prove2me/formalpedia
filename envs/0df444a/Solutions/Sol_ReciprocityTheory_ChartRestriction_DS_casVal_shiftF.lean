-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casVal_shiftF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:17.698319+00:00
-- url     : https://prove2.me/submissions/4eb1dfb7-e34f-46cd-ad87-c39408a1e688

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_casVal_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_casVal_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) :
    ((casVal lam + n : ℝ) : ℂ) + 2 * poleF dual lam s = ((casVal (shiftF dual lam s) : ℝ) : ℂ) := by
  cases dual
  · simp only [shiftF, poleF, cond_false, poleV, tset_casVal_add]; push_cast; ring
  · simp only [shiftF, poleF, cond_true, poleVd, tset_casVal_sub]; push_cast; ring
end ReciprocityTheory.ChartRestriction.DS
