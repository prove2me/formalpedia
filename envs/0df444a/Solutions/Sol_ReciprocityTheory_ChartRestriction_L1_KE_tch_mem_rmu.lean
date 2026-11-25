-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.tch_mem_rmu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:57.830209+00:00
-- url     : https://prove2.me/submissions/f031c38b-b050-43ee-ad96-21edf9d2d100

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
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ Tch l) : x ∈ Rmu l := by
  rcases hx with rfl | hx
  · exact (Rmu l).zero_mem
  · exact Subring.subset_closure hx
end ReciprocityTheory.ChartRestriction.L1.KE
