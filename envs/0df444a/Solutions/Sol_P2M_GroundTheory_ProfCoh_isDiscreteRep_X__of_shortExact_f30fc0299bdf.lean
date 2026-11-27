-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_isDiscreteRep_X__of_shortExact_f30fc0299bdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:33.771144+00:00
-- url     : https://prove2.me/submissions/b1fb4bf7-e86b-47c4-9dac-57f78872e84f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits Topology
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
omit [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {S : ShortComplex (Rep.{w} k G)} (hS : S.ShortExact)
    [IsDiscreteRep S.X₂] : IsDiscreteRep S.X₁ :=
  (isDiscreteRep k G).prop_X₁_of_shortExact hS ‹_›
end GroundTheory.ProfCoh
