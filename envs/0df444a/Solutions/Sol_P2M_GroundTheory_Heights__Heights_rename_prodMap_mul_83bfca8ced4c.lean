-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rename_prodMap_mul_83bfca8ced4c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:04.012094+00:00
-- url     : https://prove2.me/submissions/d27153c5-e678-4b1c-b345-e9298ace1518

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by
  rw [rename_rename]
  rfl
end GroundTheory.Heights₂.Heights
