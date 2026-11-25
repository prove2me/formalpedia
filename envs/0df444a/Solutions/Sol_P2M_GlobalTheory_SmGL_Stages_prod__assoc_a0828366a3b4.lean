-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_Stages_prod__assoc_a0828366a3b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:02.982662+00:00
-- url     : https://prove2.me/submissions/6f617b66-32e6-49cf-8691-baffff94944d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_P2M_GlobalTheory_SmGL_Stages_ind__assoc_9f771f8b94ce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r s t : ℕ) (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃), IsSmooth π₁ → IsSmooth π₂ → IsSmooth π₃ → Nonempty ((prod₂ (prod₂ π₁ π₂) π₃).Equiv (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ (prod₂ π₂ π₃)))) := by
  intro k _ _ _ _ r s t V₁ V₂ V₃ _ _ _ _ _ _ π₁ π₂ π₃ _ _ _
  exact ind₂_assoc (stdSum rfl) (stdSum rfl) (stdSum (Nat.add_assoc r s t).symm) (stdSum rfl)
    (fun i => Fin.ext (by simp)) (fun i => Fin.ext (by simp)) (fun i => Fin.ext (by simp [add_assoc]))
    π₁ π₂ π₃
end GlobalTheory.SmGL.Stages
