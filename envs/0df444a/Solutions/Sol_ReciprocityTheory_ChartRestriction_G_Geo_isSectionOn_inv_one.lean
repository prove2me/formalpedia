-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isSectionOn_inv_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:43.06286+00:00
-- url     : https://prove2.me/submissions/9f6dd9ea-9e8d-49d2-9ad7-82669530c24e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA

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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι}
    (hB : B.a = 0) : IsSectionOn P B.inv 1 := by
  classical
  refine ⟨0, fun k => ?_, ?_, ?_⟩
  · simp [HermLine.inv, hB]
  · intro m hm k
    have hm0 : m = 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])
    subst hm0
    simp
  · intro h
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
end ReciprocityTheory.ChartRestriction.G.Geo
