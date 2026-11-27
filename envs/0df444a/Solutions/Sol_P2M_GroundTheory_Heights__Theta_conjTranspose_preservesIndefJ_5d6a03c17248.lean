-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_conjTranspose_preservesIndefJ_5d6a03c17248
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:27.360646+00:00
-- url     : https://prove2.me/submissions/f4306533-ebe2-463a-860e-8390f3f738b7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {p q : ℕ}
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {g : 𝔐} (hg : gᴴ * J * g = J) : gᴴᴴ * J * gᴴ = J := by
  rw [conjTranspose_conjTranspose]
  exact mul_indefJ_mul_conjTranspose hg
end GroundTheory.Heights₂.Theta
