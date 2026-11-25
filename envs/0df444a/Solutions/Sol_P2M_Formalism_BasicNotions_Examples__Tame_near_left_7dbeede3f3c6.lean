-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_near_left_7dbeede3f3c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:22.356256+00:00
-- url     : https://prove2.me/submissions/b097c1ad-7e53-498b-8a3a-815da2f5d707

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable [IsAlgClosure E Ω]
attribute [instance] Test.grp Test.fin
omit [NumberField E] [IsAlgClosure E Ω]
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution {s t : Test E Ω} {σ : G E Ω} (h : Near A (s.prod t).φ σ) : Near A s.φ σ :=
  fun y hy hf => h y hy fun κ hκ => hf κ (congrArg Prod.fst hκ)
end Formalism.BasicNotions.Examples₂.Tame
