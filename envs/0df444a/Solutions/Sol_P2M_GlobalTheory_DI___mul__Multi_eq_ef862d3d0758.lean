-- Prove2me | solution 1 for P2M_GlobalTheory_DI___mul__Multi_eq_ef862d3d0758
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:51.064202+00:00
-- url     : https://prove2.me/submissions/0d59ff1e-9ae6-473b-9a6d-51059ecc5e02

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
theorem _root_.solution (u : V) {q : ℕ} (w : Fin q → V) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ιMulti K q w =
      ExteriorAlgebra.ιMulti K (q + 1) (Fin.cons u w) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl
end GlobalTheory.DI
