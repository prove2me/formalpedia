-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.homog_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:53.464396+00:00
-- url     : https://prove2.me/submissions/4cf26041-b7a9-4530-9fd4-d9dac148ab9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {ι : Type*} [DecidableEq ι] (i₀ : ι) {N : ℕ} (G : MvPolynomial ι ℤ)
    (hN : G.totalDegree ≤ N) : (homog i₀ N G).IsHomogeneous N := by
  apply IsHomogeneous.sum
  intro m hm
  apply isHomogeneous_monomial
  have : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  have h := Finsupp.degree_single (R := ℕ) i₀ (N - m.degree)
  simp only [map_add, h]
  omega
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
