-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_finrank_quotH_le_b9556f2e26a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:31.125813+00:00
-- url     : https://prove2.me/submissions/597a1274-d666-47d2-83d8-c33c998732c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_cechH0Map_injective_562dc05f7cb3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_quotMul_res_b337987bbe92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_quotMul_injective_339defbd4c78

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
theorem _root_.solution (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω)
    (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I)
    (hinj : ∀ I : Chart x, ∀ y ∈ F₁.sub I, s * y ∈ G₂.sub I → y ∈ G₁.sub I)
    [Module.Finite k (SubSystem.quotH F₂ G₂ 0)] :
    Module.finrank k (SubSystem.quotH F₁ G₁ 0) ≤ Module.finrank k (SubSystem.quotH F₂ G₂ 0) :=
  LinearMap.finrank_le_finrank_of_injective
    (cechH0Map_injective (quotMul F₁ G₁ F₂ G₂ s hF hG) (quotMul_res F₁ G₁ F₂ G₂ s hF hG)
      fun I => quotMul_injective F₁ G₁ F₂ G₂ s hF hG I.1 (hinj I.1))
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
