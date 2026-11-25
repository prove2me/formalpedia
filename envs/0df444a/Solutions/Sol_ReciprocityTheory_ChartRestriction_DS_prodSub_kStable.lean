-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.prodSub_kStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:31.033709+00:00
-- url     : https://prove2.me/submissions/27abf7eb-b758-4867-8e59-066bbd3c01b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_prodSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {E₁ : Fin n → Fin n → Module.End ℂ M₁}
    {E₂ : Fin n → Fin n → Module.End ℂ M₂} {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂}
    (h₁ : IsKStableSub ε E₁ V₁) (h₂ : IsKStableSub ε E₂ V₂) :
    IsKStableSub ε (prodE E₁ E₂) (prodSub V₁ V₂) := fun a b hab v hv =>
  mem_prodSub.2 ⟨h₁ a b hab _ (mem_prodSub.1 hv).1, h₂ a b hab _ (mem_prodSub.1 hv).2⟩
end ReciprocityTheory.ChartRestriction.DS
