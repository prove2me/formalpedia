-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isSectionOn_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:57.345898+00:00
-- url     : https://prove2.me/submissions/ac636ad2-171c-4846-b674-eceb0f41aba4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn P B 1 := by
  refine ⟨0, fun k => by simp [hB], ?_, ?_⟩
  · intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  · exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
end ReciprocityTheory.ChartRestriction.G.Geo
