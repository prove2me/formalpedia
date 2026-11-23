-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.H_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:29.023948+00:00
-- url     : https://prove2.me/submissions/1b2e5da8-6393-4c90-b67b-411c1ef3f5e9

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
theorem _root_.solution {n : ℕ} {P : A.H n → Prop} (h : ∀ x hx, P (A.cls n x hx)) (c : A.H n) : P c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h z.1 z.2
end ReciprocityTheory.Coh.Cx
