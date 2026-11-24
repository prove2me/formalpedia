-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:39.169183+00:00
-- url     : https://prove2.me/submissions/9b8655e6-1168-488b-9eb6-5094214541a9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence

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
open CategoryTheory ShortComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (S : ShortComplex (Rep.{u} k G)) [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]
variable {S}
variable (hS : S.ShortExact)
include hS
namespace GroundTheory.ProfCoh
theorem _root_.solution (i : ℕ) :
    (ShortComplex.mk (cohomologyMap S.f i) (cohomologyMap S.g i)
      (cohomologyMap_f_comp_g i)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₂ i
end GroundTheory.ProfCoh
