-- Prove2me | solution 1 for ReciprocityTheory.Coh.lowLES_h0Equiv_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:13.518798+00:00
-- url     : https://prove2.me/submissions/720bff1f-59d3-4383-8549-e968579620b6

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal LowDeg
universe u
variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
namespace ReciprocityTheory.Coh
theorem _root_.solution {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (x : M.H 0) :
    cohomZeroEquivContinuous M' (P.hom.H 0 x) = P.h0 (cohomZeroEquivContinuous M x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x

  exact Subtype.ext (congrArg P.u (congrArg y.1.1 (Subsingleton.elim _ _)))
end ReciprocityTheory.Coh
