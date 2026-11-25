-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_mk_85d17fedfeb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:23.996259+00:00
-- url     : https://prove2.me/submissions/ce587b68-f75c-410f-8b48-8c0dc90e39d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (m : M₁.laurent) :
    quotProj M₁ M₂ c (Submodule.Quotient.mk m) =
      quotIota M₁ M₂ c ⟨(m : LaurentSpace x E) c, m.2 c⟩ := rfl
end GroundTheory.Heights₂.Heights.Kleiman
