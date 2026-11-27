-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isMaximalCompact_maxCompact_361840dcefd4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:43.539289+00:00
-- url     : https://prove2.me/submissions/10f66c56-ab59-4f17-9a2a-95ee6c8e229e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_eq_maxCompact_of_isCompact_2b5a34383dd9

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
theorem _root_.solution :
    IsCompact ((maxCompact G : Subgroup G) : Set G) ∧
      ∀ L : Subgroup G, IsCompact (L : Set G) → maxCompact G ≤ L → L = maxCompact G :=
  ⟨isCompact_maxCompact_indefiniteUnitary, fun _ hL hK => eq_maxCompact_of_isCompact hL hK⟩
end GroundTheory.Heights₂.Theta
