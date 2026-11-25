-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__mem_primeToSub_e38917aa181c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:42.078502+00:00
-- url     : https://prove2.me/submissions/e298c0a1-b296-44ac-90f6-e2f4dba4df71

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
omit [Fact l.Prime]
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (x : (AlgebraicClosure (ZMod g))ˣ) :
    x ∈ primeToSub g l ↔ (orderOf x).Coprime l := Iff.rfl
end Formalism.BasicNotions.Examples₂
