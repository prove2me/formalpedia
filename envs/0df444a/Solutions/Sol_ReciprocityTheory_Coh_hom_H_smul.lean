-- Prove2me | solution 1 for ReciprocityTheory.Coh.hom_H_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:56:15.850716+00:00
-- url     : https://prove2.me/submissions/5948b8a2-2fcb-4a21-b8c7-39bdbb6963c4

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh
theorem _root_.solution {A : Cx R} (i : Hom A A) (t : R) (hi : ∀ n x, i.f n x = t • x) (n : ℕ)
    (x : A.H n) : i.H n x = t • x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    show Submodule.Quotient.mk (i.Z n z) = t • Submodule.Quotient.mk z
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hi n z.1)
end ReciprocityTheory.Coh
