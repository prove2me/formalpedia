-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.locLen_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:28.850436+00:00
-- url     : https://prove2.me/submissions/a2219a6c-02a0-4bcd-a6fc-c14595f99eb3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {N : Type v} [AddCommGroup N] [Module A N] (p : PrimeSpectrum A)
    (hp : p ∉ support A N) : locLen N p = 0 := by
  unfold locLen
  have hs : Subsingleton (LocalizedModule p.asIdeal.primeCompl N) := by
    first
      | exact Module.notMem_support_iff.1 hp
      | exact Module.not_mem_support_iff.1 hp
  exact Module.length_eq_zero_iff.2 hs
end ReciprocityTheory.ChartRestriction.G.AI
