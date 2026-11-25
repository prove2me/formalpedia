-- Prove2me | solution 1 for ReciprocityTheory.Coh.cupCoh_isCup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:46.2748+00:00
-- url     : https://prove2.me/submissions/57e726f8-017a-4fb8-af51-005bcaab4724

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ContractNthCastAddCastSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal
noncomputable section
universe u
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh
theorem _root_.solution {M N P : TRep R G} (b : Pairing M N P) : IsCup b (cupCoh b) := by
  intro p q x y hx hy
  exact ⟨cupCoch b p q x y, cupProduct_cocycle b p q x hx y hy, rfl, rfl⟩
end ReciprocityTheory.Coh
