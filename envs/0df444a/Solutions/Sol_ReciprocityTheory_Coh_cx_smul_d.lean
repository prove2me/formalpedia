-- Prove2me | solution 1 for ReciprocityTheory.Coh.cx_smul_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:07.637097+00:00
-- url     : https://prove2.me/submissions/b5ba16f3-6b28-438b-93a6-f428e266fc72

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LocaliseA

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
variable {R : Type u} [CommRing R] {A B : Cx R}
namespace ReciprocityTheory.Coh
theorem _root_.solution {n : ℕ} (t : R) (x : B.X n) : B.d n (t • x) = t • B.d n x := map_smul _ _ _
end ReciprocityTheory.Coh
