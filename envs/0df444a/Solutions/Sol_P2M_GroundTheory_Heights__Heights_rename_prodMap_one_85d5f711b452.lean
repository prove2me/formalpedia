-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rename_prodMap_one_85d5f711b452
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:25.933424+00:00
-- url     : https://prove2.me/submissions/dea0ede9-a65c-4ef2-96c0-3fe4dad6b5fa

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
theorem _root_.solution (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by
  have : Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id := by
    funext ij
    rfl
  rw [this]
  exact rename_id_apply p
end GroundTheory.Heights₂.Heights
