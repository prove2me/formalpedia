-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___comp_map_res_6a14414efe8b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.968807+00:00
-- url     : https://prove2.me/submissions/9d704ebd-7397-42f0-b16c-65126f287435

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Theorems.Thm_P2M_GroundTheory_GroupCoh___comp_map_002a70015e3d

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
open CategoryTheory groupCohomology Rep
universe u
variable {k G H : Type u} [CommRing k] [Group G] [Group H]
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  δ_comp_map f hX ((shortExact_res f).2 hX) (𝟙 _) i j hij
end GroundTheory.GroupCoh
