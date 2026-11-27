-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_norm_aut_906809479f72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:49:31.796857+00:00
-- url     : https://prove2.me/submissions/1eaf7ab7-9906-4caa-950a-2e4a00a88a50

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB

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
  (j : Ω →+* PadicAlgCl l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (σ : GQ l) (x : PadicAlgCl l) : ‖σ x‖ = ‖x‖ := by
  have h1 : ∀ y : PadicAlgCl l, ‖y‖ = spectralNorm ℚ_[l] (PadicAlgCl l) y := fun y => rfl
  rw [h1, h1, ← spectralNorm_eq_of_equiv]
end Formalism.BasicNotions.Examples₂.LB
