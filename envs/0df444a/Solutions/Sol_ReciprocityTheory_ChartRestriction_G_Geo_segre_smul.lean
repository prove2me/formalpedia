-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.segre_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:42.030031+00:00
-- url     : https://prove2.me/submissions/e0de1781-8b77-4366-94a3-e4a0bb7532bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB

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
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (fun p => c p.1 * z p) = (∏ k, c k) • segre z := by
  funext i
  simp only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
end ReciprocityTheory.ChartRestriction.G.Geo
