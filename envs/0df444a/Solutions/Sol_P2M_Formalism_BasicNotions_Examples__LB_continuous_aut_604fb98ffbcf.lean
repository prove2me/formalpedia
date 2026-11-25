-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_continuous_aut_604fb98ffbcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:13.724751+00:00
-- url     : https://prove2.me/submissions/56433e31-425c-4eff-9c41-dfafd27854bb

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
theorem _root_.solution (σ : GQ l) : Continuous σ := by
  have hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖ := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    first
      | (simp only [spectralNorm, minpoly.algEquiv_eq]; done)
      | exact (spectralNorm.aut_isom σ y).symm
      | (unfold spectralNorm; rw [minpoly.algEquiv_eq])
      | (unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)
  exact (AddMonoidHomClass.isometry_of_norm σ hiso).continuous
end Formalism.BasicNotions.Examples₂.LB
