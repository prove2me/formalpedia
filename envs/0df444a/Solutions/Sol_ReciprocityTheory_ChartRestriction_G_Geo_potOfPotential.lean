-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.potOfPotential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:25.450946+00:00
-- url     : https://prove2.me/submissions/10aeec73-8b63-44e0-bcbb-e72ca9cb1632

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isPotential_potOf

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution : PotOfPotentialStatement := by
  intro K _ ι _ P J e R L hL
  exact isPotential_potOf R hL
end ReciprocityTheory.ChartRestriction.G.Geo
