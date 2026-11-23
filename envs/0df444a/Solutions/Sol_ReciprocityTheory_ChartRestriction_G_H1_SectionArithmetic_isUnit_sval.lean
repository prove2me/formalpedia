-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:17.339963+00:00
-- url     : https://prove2.me/submissions/0c2ee9ab-4ae2-4ac0-9f68-64f2294e2435

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
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (k : (LB.LinComb L φ ε).ι) (hk : r z ∈ Y.basicOpen (s.f k)) :
    IsUnit (sval s r z J) := by

  have hkU : r z ∈ LB.wchart L φ k := Y.basicOpen_le _ hk
  have hm := hJ.mem φ r
  unfold sval
  rw [sec_trans s r z hm hkU]
  refine (Units.isUnit _).mul ?_
  erw [gs_eq r z _ hkU]
  have hz : z ∈ Z.basicOpen ((r.app _).hom (s.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  exact (Z.mem_basicOpen _ z hkU).1 hz
end ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
