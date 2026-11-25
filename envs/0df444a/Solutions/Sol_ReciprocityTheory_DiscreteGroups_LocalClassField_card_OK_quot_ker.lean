-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.card_OK_quot_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:06:22.828231+00:00
-- url     : https://prove2.me/submissions/8d5a35c5-db9f-4d0a-b9b9-3066790d2583

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_resK_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : Nat.card (OK p K ⧸ RingHom.ker (resMap p K)) = qK p K := by
  rw [Nat.card_congr (RingHom.quotientKerEquivRange (resMap p K)).toEquiv, qK]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_resK_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨toObar p K x, (x : K).2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨⟨x, hx⟩, x.2⟩, rfl⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
