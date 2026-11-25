-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_quotMul_res_b337987bbe92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:12:14.747472+00:00
-- url     : https://prove2.me/submissions/a6754226-bdc3-4d6b-b73d-b35ad33d3ca6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
theorem _root_.solution (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω) (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ G₁ I) :
    quotMul F₁ G₁ F₂ G₂ s hF hG J (SubSystem.quotRes F₁ G₁ I J h m) =
      SubSystem.quotRes F₂ G₂ I J h (quotMul F₁ G₁ F₂ G₂ s hF hG I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
