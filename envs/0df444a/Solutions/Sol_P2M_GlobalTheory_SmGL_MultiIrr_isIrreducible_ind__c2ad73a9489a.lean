-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:18:16.558924+00:00
-- url     : https://prove2.me/submissions/5d4b2355-0f70-42c3-a848-2328f5b591d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_linearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_continuous_relabel
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (e : a ⊕ b ≃ n)
    {π₁ : Representation ℂ (GL a k) V} {π₂ : Representation ℂ (GL b k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ e (extTensor π₁ π₂)).IsIrreducible := by
  let ea := (Fintype.equivFin a).symm
  let eb := (Fintype.equivFin b).symm
  have := H k _ _ V W (π₁.comp (relabel k ea).toMonoidHom) (π₂.comp (relabel k eb).toMonoidHom)
    (isSmooth_comp s₁ _ (continuous_relabel ea))
    ((isIrreducible_iff_of_linearEquiv _ (relabel k ea).surjective (.refl ℂ V) fun _ _ => rfl).2 i₁)
    (UnitInd.isUnitarisable_comp u₁ _) (isSmooth_comp s₂ _ (continuous_relabel eb))
    ((isIrreducible_iff_of_linearEquiv _ (relabel k eb).surjective (.refl ℂ W) fun _ _ => rfl).2 i₂)
    (UnitInd.isUnitarisable_comp u₂ _)
  exact (isIrreducible_ind₂_iff _ e ea eb (.refl ℂ _) fun _ _ => rfl).1 this
end GlobalTheory.SmGL.MultiIrr
