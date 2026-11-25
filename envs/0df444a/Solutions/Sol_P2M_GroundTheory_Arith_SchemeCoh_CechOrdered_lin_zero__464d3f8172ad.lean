-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_zero__464d3f8172ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:05.401195+00:00
-- url     : https://prove2.me/submissions/0706f18b-3b54-4970-a027-f3d04cd12512

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable {q r s : ℕ}
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
theorem _root_.solution (z : Chain ι q) : lin (fun _ => (0 : Chain ι r)) z = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', add_zero]
  | single t k => simp
end GroundTheory.Arith.SchemeCoh.CechOrdered
