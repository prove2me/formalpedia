-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.evQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:27:25.419105+00:00
-- url     : https://prove2.me/submissions/07980859-b732-4716-9d64-79d3b8c56782

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]


theorem solution (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P)
    (q : MvPolynomial (Σ k, ι k) ℚ) :
    evQ P z hz (Ideal.Quotient.mk _ q) = eval₂ (algebraMap ℚ ℂ) z q := by
  rfl
