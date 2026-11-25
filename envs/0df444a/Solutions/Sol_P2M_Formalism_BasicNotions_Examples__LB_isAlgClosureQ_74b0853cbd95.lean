-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_isAlgClosureQ_74b0853cbd95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:34.98577+00:00
-- url     : https://prove2.me/submissions/7a7ca60f-f071-4296-a328-0ba853b76753

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]
omit hl
variable (E Ω)
include E
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution : IsAlgClosure ℚ Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ E Ω⟩
end Formalism.BasicNotions.Examples₂.LB
