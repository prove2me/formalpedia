-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.lminor_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:05.092933+00:00
-- url     : https://prove2.me/submissions/0335f309-bfd9-4474-a6be-4996b3195f86

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : lminor A (Fin.last n) = A.det := by
  rfl
end ReciprocityTheory.ChartRestriction.G.FD
