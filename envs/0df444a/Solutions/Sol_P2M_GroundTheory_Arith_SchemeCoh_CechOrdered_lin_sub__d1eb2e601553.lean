-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_sub__d1eb2e601553
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:01.93513+00:00
-- url     : https://prove2.me/submissions/9cd74eb5-3b45-4082-934c-69b9f9abb135

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
theorem _root_.solution (B B' : (Fin (q + 1) → ι) → Chain ι r) (z : Chain ι q) :
    lin (fun t => B t - B' t) z = lin B z - lin B' z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add]; abel
  | single t k => simp [smul_sub]
end GroundTheory.Arith.SchemeCoh.CechOrdered
