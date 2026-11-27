-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_subrepCohomologyCocone___app_98e7da747dcd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:13:51.447492+00:00
-- url     : https://prove2.me/submissions/76baf803-b237-4acc-b230-f6b78cb3f164

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_FilteredHomology
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion

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
open CategoryTheory Limits
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep.{u} k G) {ι : Type u} [Preorder ι] (W : ι → Submodule k A) (hW : Monotone W)
  (hstable : ∀ i g, W i ≤ (W i).comap (A.ρ g))
variable [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A]
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) (i : ι) :
    (subrepCohomologyCocone A W hW hstable n).ι.app i =
      cohomologyMap (Rep.subtype A (W i) (hstable i)) n :=
  rfl
end GroundTheory.ProfCoh
