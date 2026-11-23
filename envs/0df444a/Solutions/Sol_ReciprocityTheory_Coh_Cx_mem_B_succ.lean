-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.mem_B_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:30.901868+00:00
-- url     : https://prove2.me/submissions/06857c04-a659-4c7d-815a-483165098bd4

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
open ReciprocityTheory.Coh.Cx
variable {R : Type u} [CommRing R] {A B C : Cx R}
namespace ReciprocityTheory.Coh.Cx
theorem _root_.solution {n : ℕ} {x : A.X (n + 1)} : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by
  change x ∈ LinearMap.range (A.d n) ↔ _
  exact LinearMap.mem_range
end ReciprocityTheory.Coh.Cx
