-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_quotInl_baf1d4324949
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:04.655451+00:00
-- url     : https://prove2.me/submissions/3350bf18-d0ac-4378-8a9c-ce5ca747cc1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
theorem _root_.solution (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotPr F₁ F₂ F₃ h32 I (quotInl F₁ F₂ F₃ h21 I m) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  show (Submodule.Quotient.mk (⟨(y : E), h21 I y.2⟩ : F₁.sub I) : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact y.2
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
