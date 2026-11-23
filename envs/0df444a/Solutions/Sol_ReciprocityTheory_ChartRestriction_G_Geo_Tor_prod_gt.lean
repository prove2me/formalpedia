-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:38.812804+00:00
-- url     : https://prove2.me/submissions/f0e7ecc5-5b3c-4f5e-aad6-b71930fe74fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφ D F b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  simp [DegPre.gtφ, DegPre.gtε] <;> rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
