-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.Hom.comp_H_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:27:38.025969+00:00
-- url     : https://prove2.me/submissions/e63faa7e-69b6-48db-95a8-0e4095838bb8

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_H

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
namespace Hom
theorem _root_.solution (ψ : Hom B C) (φ : Hom A B) (n : ℕ) (c : A.H n) :
    (ψ.comp φ).H n c = ψ.H n (φ.H n c) := by
  rw [Hom.comp_H]
  rfl
end Hom
end ReciprocityTheory.Coh.Cx
