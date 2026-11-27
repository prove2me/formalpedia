-- Prove2me | solution 1 for P2M_GlobalTheory_T_idempotent_eq_of_basicOpen_eq__e96164f40167
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:27.756987+00:00
-- url     : https://prove2.me/submissions/7c9f1af0-e0f2-43b7-a29e-706b70cf9e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEqStatement
import Theorems.Thm_GlobalTheory_idempotent_eq_of_basicOpen_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' → X.basicOpen e = X.basicOpen e' → e = e' := by
  first | exact @GlobalTheory.idempotent_eq_of_basicOpen_eq | exact GlobalTheory.idempotent_eq_of_basicOpen_eq | (intros; apply GlobalTheory.idempotent_eq_of_basicOpen_eq <;> assumption)
end _root_.GlobalTheory.T
