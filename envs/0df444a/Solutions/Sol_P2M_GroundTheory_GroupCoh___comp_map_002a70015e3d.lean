-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___comp_map_002a70015e3d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:09.988846+00:00
-- url     : https://prove2.me/submissions/c06c30bc-5384-43d6-9e2c-1d7d95e85647

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap

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
theorem _root_.solution (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f F)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hY) i j hij
end GroundTheory.GroupCoh
