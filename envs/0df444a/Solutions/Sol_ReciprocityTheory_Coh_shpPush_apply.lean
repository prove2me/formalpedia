-- Prove2me | solution 1 for ReciprocityTheory.Coh.shpPush_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:12.019832+00:00
-- url     : https://prove2.me/submissions/ecc64a7f-a1bc-4ab9-ad17-1de054531569

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)
namespace ReciprocityTheory.Coh
theorem _root_.solution (n : ℕ) (F : hcoch C G n) (x) : (shpPush ev hφ n F).1 x = ev.u (F.1 x) := rfl
end ReciprocityTheory.Coh
