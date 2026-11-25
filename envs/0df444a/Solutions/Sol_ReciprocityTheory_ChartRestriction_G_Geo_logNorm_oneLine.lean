-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.logNorm_oneLine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:05.998808+00:00
-- url     : https://prove2.me/submissions/b9299e05-68bf-4046-8f9c-961571022374

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
theorem _root_.solution (z : (Σ k, ι k) → ℂ) : logNorm (oneLine (ι := ι)) 1 z = 1 := by
  simp [logNorm, oneLine, HermLine.ofWeight, Real.exp_neg]
end ReciprocityTheory.ChartRestriction.G.Geo
