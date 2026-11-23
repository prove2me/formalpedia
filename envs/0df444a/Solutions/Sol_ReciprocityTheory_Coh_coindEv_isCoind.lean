-- Prove2me | solution 1 for ReciprocityTheory.Coh.coindEv_isCoind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:50.297582+00:00
-- url     : https://prove2.me/submissions/80382dc5-7fac-41af-9bc5-d51c8d48b18b

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
  (U : Subgroup G) (M : TRep R U)
variable {U M}
variable (U M)
variable [LocallyCompactSpace G]
namespace ReciprocityTheory.Coh
theorem _root_.solution : IsCoind U M (coindRep U M) (coindEv U M) := by
  unfold IsCoind
  refine ⟨rfl, fun f => f.1, Topology.IsEmbedding.subtypeVal, fun c g => ?_,
    fun f hf => ⟨⟨f, hf⟩, rfl⟩⟩
  show c.1 g = c.1 (1 * g)
  rw [one_mul]
end ReciprocityTheory.Coh
