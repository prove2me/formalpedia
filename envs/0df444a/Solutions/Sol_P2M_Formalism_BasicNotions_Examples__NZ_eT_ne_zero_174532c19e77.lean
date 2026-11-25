-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_eT_ne_zero_174532c19e77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:32.67993+00:00
-- url     : https://prove2.me/submissions/a0b224f4-229e-4ff2-a100-8ea8c070164b

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_card_ne_cf5bb1f9180d

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
theorem _root_.solution [CharZero K] : eT K Γ ≠ 0 := fun h =>
  inv_ne_zero (card_ne (K := K) (Γ := Γ)) (congrArg (fun x => x.coeff 1) h)
end Formalism.BasicNotions.Examples₂.NZ
