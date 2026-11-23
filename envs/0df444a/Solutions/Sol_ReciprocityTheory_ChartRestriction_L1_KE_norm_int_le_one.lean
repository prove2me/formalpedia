-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.norm_int_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:51.81563+00:00
-- url     : https://prove2.me/submissions/6305be43-8657-46de-ac78-81c270f59c77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] (n : ℤ) :
    ‖algebraMap ℤ K n‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_intCast_le_one K n
end ReciprocityTheory.ChartRestriction.L1.KE
