-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_exists_quotInl_e9e32e11d485
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:43.021509+00:00
-- url     : https://prove2.me/submissions/0d8ffa8e-2a7b-4e8f-a86e-0c35a2d125f7

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
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I)
    (hm : quotPr F₁ F₂ F₃ h32 I m = 0) : ∃ y, quotInl F₁ F₂ F₃ h21 I y = m := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h' : (Submodule.Quotient.mk z : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0 := hm
  rw [Submodule.Quotient.mk_eq_zero] at h'
  exact ⟨Submodule.Quotient.mk ⟨z, h'⟩, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
