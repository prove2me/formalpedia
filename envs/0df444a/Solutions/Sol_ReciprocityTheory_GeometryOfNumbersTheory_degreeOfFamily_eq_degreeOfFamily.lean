-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily_eq_degreeOfFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:18:22.286502+00:00
-- url     : https://prove2.me/submissions/589ebde4-be80-4824-8749-26608f6762d1

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_length_eq_latticeRank
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_degreeOfFamily_eq_of_isFullRankFamily


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r r' : ℕ}
    {v : Fin r → V} {v' : Fin r' → V} (hv : IsFrame K E v) (hv' : IsFrame K E v') :
    degreeOfFamily h E v = degreeOfFamily h E v' := by
  obtain rfl : r = r' := hv.length_eq_latticeRank.trans hv'.length_eq_latticeRank.symm
  exact degreeOfFamily_eq_of_isFullRankFamily h hE hv hv'
end ReciprocityTheory.GeometryOfNumbersTheory
