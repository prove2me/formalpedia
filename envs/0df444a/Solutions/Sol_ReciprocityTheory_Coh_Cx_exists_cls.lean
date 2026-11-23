-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.exists_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:34.219122+00:00
-- url     : https://prove2.me/submissions/731b7412-d706-4f05-9840-8c3a5bef6ae8

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
theorem _root_.solution {n : ℕ} (c : A.H n) : ∃ x hx, c = A.cls n x hx := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z.1, z.2, rfl⟩
end ReciprocityTheory.Coh.Cx
