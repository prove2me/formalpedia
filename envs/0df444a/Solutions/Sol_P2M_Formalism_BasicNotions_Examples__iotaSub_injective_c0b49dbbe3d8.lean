-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__iotaSub_injective_c0b49dbbe3d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:41.255161+00:00
-- url     : https://prove2.me/submissions/ede38e4e-e190-4719-9f08-0baae14b01b8

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_UnitsPowSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Cardinal
variable (g l : ℕ) [Fact g.Prime] [Fact l.Prime]
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : Function.Injective (iotaSub g l) := by
  intro x y h
  have h1 := (MonoidHom.ofInjective (teichU_injective l)).symm.injective h
  have h2 : teichU g x.1 = teichU g y.1 := congrArg Subtype.val h1
  exact Subtype.ext (teichU_injective g h2)
end Formalism.BasicNotions.Examples₂
