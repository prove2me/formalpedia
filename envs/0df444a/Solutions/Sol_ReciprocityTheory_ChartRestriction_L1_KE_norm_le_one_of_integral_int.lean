-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.norm_le_one_of_integral_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:42.880526+00:00
-- url     : https://prove2.me/submissions/69370d99-36ad-472a-9d17-2d8e01bb03f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_le_one_of_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_int_le_one

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
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] (δ : K)
    (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral norm_int_le_one δ h
end ReciprocityTheory.ChartRestriction.L1.KE
