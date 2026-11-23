-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationRestrictionInvariants.zeroDifferential_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:46.346518+00:00
-- url     : https://prove2.me/submissions/2baafa92-8120-4a8b-a6ec-8c562b97e1a2

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationRestrictionInvariants
theorem _root_.solution (M : TRep R G) (y : M.coch.X 0) (a : G) :
    (M.coch.d 0 y).1 (e1 a) = M.rho a (y.1 ![]) - y.1 ![] := by
  show ReciprocityTheory.Gal.dn M.rho 0 y.1 (e1 a) = _
  rw [LowDeg.dn_zero_apply]
end ReciprocityTheory.Coh.InflationRestrictionInvariants
