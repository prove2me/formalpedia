-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___map_g_apply_e86f9a071593
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:21.372195+00:00
-- url     : https://prove2.me/submissions/82031e61-b556-4200-a355-24ea8840df23

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)
include hX
namespace GroundTheory.GroupCoh
theorem _root_.solution (i j : ℕ) (hij : i + 1 = j) (x : groupCohomology X.X₂ i) :
    δ hX i j hij (map (MonoidHom.id H) X.g i x) = 0 := by
  have h := congr(($((map_cochainsFunctor_shortExact hX).comp_δ i j hij)).hom x)
  exact h
end GroundTheory.GroupCoh
