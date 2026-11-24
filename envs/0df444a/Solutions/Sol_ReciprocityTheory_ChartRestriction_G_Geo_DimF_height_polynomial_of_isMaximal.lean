-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_polynomial_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:32.971738+00:00
-- url     : https://prove2.me/submissions/cc2af2fe-de91-4884-9a43-0e1675e44d67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {c : ℕ∞} (hR : ∀ m : Ideal R, m.IsMaximal → m.height = c)
    (M : Ideal (Polynomial R)) (hM : M.IsMaximal) : M.height = c + 1 := by
  haveI := hM
  have hp : (M.under R).IsMaximal := by
    rw [Ideal.under, Polynomial.algebraMap_eq]
    exact Polynomial.isMaximal_comap_C_of_isJacobsonRing M
  haveI : M.LiesOver (M.under R) := ⟨rfl⟩
  rw [Polynomial.height_eq_height_add_one (M.under R) M, hR _ hp]
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
