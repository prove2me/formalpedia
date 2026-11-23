-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.psgn_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:56.696333+00:00
-- url     : https://prove2.me/submissions/3f450f4c-139c-4e88-9137-1e9bce1d48cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {p0 i : ℕ} (h : i ≤ p0) : psgn p0 i = 1 := by
  unfold psgn
  refine Finset.prod_eq_one fun a ha => ?_
  have hlt : a < p0 := lt_of_lt_of_le (Finset.mem_range.1 ha) h
  unfold sgn
  rw [if_pos hlt]
end ReciprocityTheory.ChartRestriction.G.FD
