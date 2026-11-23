-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.cPoint_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:52.551212+00:00
-- url     : https://prove2.me/submissions/31b875ba-6e1d-429c-9c0e-d9328daa527e

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
theorem _root_.solution (T : Over (Spec (CommRingCat.of R))) : cP D T 0 = 1 := by
  have h0 : D.c 0 = 1 := by
    have e := D.c_add 0 0
    rw [add_zero] at e
    have e' : D.c 0 * D.c 0 = D.c 0 * 1 := by
      rw [_root_.mul_one]
      exact e.symm
    exact _root_.mul_left_cancel e'
  unfold cP
  rw [h0]
  first
  | simp
  | (rw [Hom.one_def, Hom.one_def, ← Category.assoc]
     congr 1
     exact toUnit_unique _ _)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
