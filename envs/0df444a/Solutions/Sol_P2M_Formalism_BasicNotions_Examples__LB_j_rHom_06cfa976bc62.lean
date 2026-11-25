-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:04:44.352703+00:00
-- url     : https://prove2.me/submissions/49f9d608-e69a-4cd5-81d2-a98c66ab32d7

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
variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (σ : ↥(KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j ((rHom hj σ : G E Ω) x) = (σ : GQ l) (j x) := j_resE j σ.1 σ.2 x
end Formalism.BasicNotions.Examples₂.LB
