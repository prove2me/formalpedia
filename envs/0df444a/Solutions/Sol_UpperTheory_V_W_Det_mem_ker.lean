-- Prove2me | solution 1 for UpperTheory.V.W.Det.mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:11.695426+00:00
-- url     : https://prove2.me/submissions/ae39178e-6918-4a03-ada7-952c9b1efc86

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.W
open UpperTheory.V.W.Det
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
namespace UpperTheory.V.W.Det
theorem _root_.solution {x : E} : x ∈ D.ker ↔ ∀ (S : Type) [CommRing S] [Algebra A S] (y u v : S ⊗[A] E),
    D.D S (y + u * (1 ⊗ₜ x) * v) = D.D S y := TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _
end UpperTheory.V.W.Det
