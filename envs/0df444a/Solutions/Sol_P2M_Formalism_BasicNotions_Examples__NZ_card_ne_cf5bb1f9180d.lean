-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_card_ne_cf5bb1f9180d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:00.90113+00:00
-- url     : https://prove2.me/submissions/02375ab2-095b-4972-9e46-a1a266aa22b8

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
variable {K Γ}
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution [CharZero K] : (Nat.card Γ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
end Formalism.BasicNotions.Examples₂.NZ
