-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_cartanHomeomorph_apply_2cea746d6a8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:11:51.400931+00:00
-- url     : https://prove2.me/submissions/f77b867f-6812-4644-ac1d-499742a76309

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
local notation "G" => indefiniteUnitaryGroup p q
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (ks : maxCompact G × cartanPos p q) :
    ((cartanHomeomorph ks : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) =
      (((ks.1 : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) * ks.2.1 := rfl
end GroundTheory.Heights₂.Theta
