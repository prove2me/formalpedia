-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.cj_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:28.925204+00:00
-- url     : https://prove2.me/submissions/0d188c5b-1b02-42ba-81c7-b64c8d22c485

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution (N : Subgroup G) [N.Normal] (s : G) (n : N) : (cj N s n : G) = s⁻¹ * n * s := rfl
end ReciprocityTheory.Coh.InflationTransgression
