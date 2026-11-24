-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cohomology_exact__5de6903b6f2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:37.615801+00:00
-- url     : https://prove2.me/submissions/289e3c8f-787e-415e-a054-18ac72f49fb1

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
    (ShortComplex.mk (cohomologyMap S.g i) (δ hS i j hij) (comp_δ hS i j hij)).Exact :=
  (cochainsShortComplex_shortExact hS).homology_exact₃ i j hij
end GroundTheory.ProfCoh
