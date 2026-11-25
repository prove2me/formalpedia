-- Prove2me | solution 1 for P2M_GlobalTheory_DI__Multi_one_eq_b408fba06786
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:30.516615+00:00
-- url     : https://prove2.me/submissions/d745562b-f990-4d39-b812-14aac857d325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorFormsSpanOfSetsMulSmulMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
namespace GlobalTheory.DI
theorem _root_.solution (u : Fin 1 → V) : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
end GlobalTheory.DI
