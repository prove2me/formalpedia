-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_le_powerSubgroup__e59580feb9f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:13:55.561998+00:00
-- url     : https://prove2.me/submissions/5ffa9ce8-9f78-4aef-9a45-1bfb95709a47

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PowInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
namespace GroundTheory.Variant₂.N1
theorem _root_.solution (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    U ≤ mulZPowers U s hU := fun u hu => ⟨0, u, hu, by simp⟩
end GroundTheory.Variant₂.N1
