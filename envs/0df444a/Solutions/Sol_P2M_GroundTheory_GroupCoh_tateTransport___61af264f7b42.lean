-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateTransport___61af264f7b42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:41.705573+00:00
-- url     : https://prove2.me/submissions/7fb8743a-d99d-468c-88d2-f2898b75ca35

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_TateTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology groupHomology
universe u
variable {k H K : Type u} [CommRing k] [Group H] [Group K]
variable [Fintype H] [Fintype K] (e : H ≃* K)
namespace GroundTheory.GroupCoh
theorem _root_.solution {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateTransport e (n + 1)).app X.X₁ =
      (tateTransport e n).app X.X₃ ≫
        TateCohomology.δ (shortExact_map_resFunctor_equiv e hX) n :=
  HomologicalComplex.HomologySequence.δ_naturality (tateTransportShortComplex e X)
    (TateCohomology.map_tateComplexFunctor_shortExact hX)
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_map_resFunctor_equiv e hX))
    n (n + 1) rfl
end GroundTheory.GroupCoh
