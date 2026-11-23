-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:38.928156+00:00
-- url     : https://prove2.me/submissions/49c70139-7317-4df7-92fb-0ebfa60bf2d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
theorem _root_.solution {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullSec s h) r z J = sval s (r ≫ h) z J := by

  have hm1 := hJ.mem (fun k => h ≫ φ k) r
  have hm2 := hJ.mem φ (r ≫ h)
  simp only [Category.assoc] at hm2
  unfold sval
  simp only [Category.assoc]
  exact (gs_res r z _ hm1 _).trans (gs_pull r h z _ hm2 _)
end ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
