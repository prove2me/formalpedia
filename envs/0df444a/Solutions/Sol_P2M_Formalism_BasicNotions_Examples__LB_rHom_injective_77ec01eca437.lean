-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_rHom_injective_77ec01eca437
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:55.720821+00:00
-- url     : https://prove2.me/submissions/c0250a5a-0cc2-40f9-80c9-718d119eea56

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_continuous_aut_604fb98ffbcf
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_denseRange_emb_e16ca7438e57


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
theorem _root_.solution : Function.Injective (rHom (E := E) hj) := by
  intro σ τ h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hd := denseRange_emb l j
  have heq : ((σ : GQ l) : PadicAlgCl l → PadicAlgCl l) = (τ : GQ l) :=
    hd.equalizer (continuous_aut _) (continuous_aut _) (funext fun x => by
      simp only [Function.comp_apply]
      rw [← j_rHom hj σ x, ← j_rHom hj τ x, h])
  exact Subtype.ext (AlgEquiv.ext (congrFun heq))
end Formalism.BasicNotions.Examples₂.LB
