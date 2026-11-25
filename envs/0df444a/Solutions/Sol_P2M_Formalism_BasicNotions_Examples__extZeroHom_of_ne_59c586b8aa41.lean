-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__extZeroHom_of_ne_59c586b8aa41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:40.507255+00:00
-- url     : https://prove2.me/submissions/5a810c2a-12ce-4a84-af00-eb191591bd1a

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
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution {K L : Type*} [Field K] [Field L] (χ : Kˣ →* Lˣ) {x : K} (h : x ≠ 0) :
    extZeroHom χ x = (χ (Units.mk0 x h) : L) := by
  simp [extZeroHom, h]
end Formalism.BasicNotions.Examples₂
