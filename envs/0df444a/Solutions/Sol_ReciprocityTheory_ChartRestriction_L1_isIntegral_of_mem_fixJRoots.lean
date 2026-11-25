-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.isIntegral_of_mem_fixJRoots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:54:24.204213+00:00
-- url     : https://prove2.me/submissions/0230d0f2-60cd-45ab-a0c6-affc59ddb37a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModChebOm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobCong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFixJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_fixJRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) {r : Ω}
    (hr : r ∈ fixJRoots (Ω := Ω) P) : IsIntegral ℤ r := by
  refine ⟨P, hP, ?_⟩
  rw [algebraMap_int_eq]
  exact (mem_fixJRoots hP r).1 hr
end ReciprocityTheory.ChartRestriction.L1
