-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_isSmooth_jac__a0d7e6d45b7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:16.487929+00:00
-- url     : https://prove2.me/submissions/6ff7cf09-222c-4f5f-a6a7-9b69f3676826

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_jac
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviTwo
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
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {k}
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SmGL
theorem _root_.solution (e : a ⊕ b ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jac₂ e π) :=
  isSmooth_comp (isSmooth_jac _ hπ) _ (continuous_leviTwo k)
end GlobalTheory.SmGL
