-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind_Lower_fadf1cb588da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:32:01.920192+00:00
-- url     : https://prove2.me/submissions/4b9e448e-5f66-4813-8c76-14c40695b64e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_equiv
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_SwapBlocks_lower_equiv_upper_swap


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
    (ind₂Lower e (extTensor π₁ π₂)).IsIrreducible := by
  obtain ⟨E⟩ := (SwapBlocks.lower_equiv_upper_swap k a b n e _).1 (extTensor π₁ π₂)
  refine (isIrreducible_iff_of_equiv E).2 ((isIrreducible_ind₂_iff _ _ (.refl b) (.refl a)
    (TensorProduct.comm ℂ W V) fun g x => ?_).1
      (isIrreducible_ind₂ H ((Equiv.sumComm b a).trans e) s₂ i₂ u₂ s₁ i₁ u₁))
  show _ = extTensor π₁ π₂ (g.2, g.1) _
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w => simp
end GlobalTheory.SmGL.MultiIrr
