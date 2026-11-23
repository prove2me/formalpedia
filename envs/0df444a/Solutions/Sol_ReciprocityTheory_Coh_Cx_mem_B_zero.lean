-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.mem_B_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:31.996254+00:00
-- url     : https://prove2.me/submissions/6fac1143-4d9c-431f-8369-46d60cc05afc

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
theorem _root_.solution {x : A.X 0} : x ∈ A.B 0 ↔ x = 0 := by
  change x ∈ (⊥ : Submodule R (A.X 0)) ↔ _
  exact Submodule.mem_bot R
end ReciprocityTheory.Coh.Cx
