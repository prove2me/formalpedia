-- Prove2me | solution 1 for P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_ind__stdSum_ee64510dd378
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:51:18.442588+00:00
-- url     : https://prove2.me/submissions/fa667130-04d2-45e7-b608-6eee7a1ad5a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.BernsteinUnitaryProductIrreducible
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.Published.BernsteinUnitaryProductIrreducible
theorem _root_.solution (H : BernsteinUnitaryProductIrreducible) {r t N : ℕ} (h : r + t = N)
    {π₁ : Representation ℂ (GL (Fin r) k) V} {π₂ : Representation ℂ (GL (Fin t) k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ (stdSum h) (extTensor π₁ π₂)).IsIrreducible := by
  subst h
  exact H k r t V W π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂
end GlobalTheory.Published.BernsteinUnitaryProductIrreducible
