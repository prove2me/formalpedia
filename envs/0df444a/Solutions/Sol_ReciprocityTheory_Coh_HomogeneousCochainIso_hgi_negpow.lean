-- Prove2me | solution 1 for ReciprocityTheory.Coh.HomogeneousCochainIso.hgi_negpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:53:39.257034+00:00
-- url     : https://prove2.me/submissions/369577e8-3f6e-4c83-b82c-3c63bae6a37d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso

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
open ReciprocityTheory.Coh.HomogeneousCochainIso
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.HomogeneousCochainIso
theorem _root_.solution (V : Type u) [AddCommGroup V] [Module R V] (k : ℕ) (v : V) :
    (-1 : R) ^ k • v = (-1 : ℤ) ^ k • v := by
  rw [← Int.cast_smul_eq_zsmul R]; push_cast; rfl
end ReciprocityTheory.Coh.HomogeneousCochainIso
