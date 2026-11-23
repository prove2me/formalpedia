-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_powSec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:59.719905+00:00
-- url     : https://prove2.me/submissions/1206ac4b-b35b-4194-8b3c-1d0462726936

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
theorem _root_.solution {I : Type} [Fintype I] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : I → LB.Sec (LB.LinComb L φ ε))
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (powSec s) r z J = ∏ i, sval (s i) r z J := by

  have hm := hJ.mem (fun p : I × K => φ p.2) r
  unfold sval
  dsimp only [powSec]
  refine (gs_eq r z _ hm _).trans ?_
  erw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => (gs_eq r z _ hm _).symm.trans (gs_res r z _ hm _)
end ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
