-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__of_mulVec_eq_ac3453965221
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:43.595018+00:00
-- url     : https://prove2.me/submissions/0f98bcd3-b341-44d8-ac5e-2aeb742763db

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (γ : Matrix (Fin N) (Fin N) E) (v : Fin N → Fin N → E) :
    Matrix.of (fun j => γ.mulVec (v j)) = Matrix.of v * γ.transpose := by
  ext i k
  change (∑ l, γ k l * v i l) = ∑ l, v i l * γ k l
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _
end Formalism.BasicNotions.Examples₂
