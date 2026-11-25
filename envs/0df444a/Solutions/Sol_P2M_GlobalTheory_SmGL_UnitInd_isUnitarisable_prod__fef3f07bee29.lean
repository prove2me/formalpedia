-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_UnitInd_isUnitarisable_prod__fef3f07bee29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:36.467044+00:00
-- url     : https://prove2.me/submissions/4cd95249-cc96-436c-84cf-411ef5cb9d62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_comp
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_extTensor
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_parInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution {r t : ℕ} {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : IsUnitarisable π₁) (h₂ : IsUnitarisable π₂) :
    IsUnitarisable (prod₂ π₁ π₂) :=
  isUnitarisable_parInd _ (isUnitarisable_comp (isUnitarisable_extTensor h₁ h₂) _)
end GlobalTheory.SmGL.UnitInd
