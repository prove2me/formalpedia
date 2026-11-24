-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cohomology_exact__fb61531df879
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:59:51.246077+00:00
-- url     : https://prove2.me/submissions/35ce330c-3e4d-4f7b-a67e-b9299ca747f2

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
namespace GroundTheory.ProfCoh
theorem _root_.solution (i j : ℕ) (hij : i + 1 = j) :
    (ShortComplex.mk (δ hS i j hij) (cohomologyMap S.f j) (δ_comp hS i j hij)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₁ i j hij
end GroundTheory.ProfCoh
