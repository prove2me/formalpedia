-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CoeffIn.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:53.061849+00:00
-- url     : https://prove2.me/submissions/462aa40e-d04a-4605-939b-b04d9c7852b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace CoeffIn
theorem _root_.solution {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, CoeffIn R (f t)) : CoeffIn R (∏ t ∈ s, f t) := Finset.prod_induction f (ReciprocityTheory.ChartRestriction.L1.CoeffIn R)
    (fun a b ha hb => ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ha hb) (ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R) hf
end CoeffIn
end ReciprocityTheory.ChartRestriction.L1
