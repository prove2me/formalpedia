-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.span_singleton_OK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:54.883857+00:00
-- url     : https://prove2.me/submissions/6a345ee2-26db-4778-8865-bf4b855b5132

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_span_singleton_OK

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
theorem _root_.solution {a b : OK p K} (h : ‖((a : K) : PadicAlgCl p)‖ = ‖((b : K) : PadicAlgCl p)‖) :
    Ideal.span {a} = Ideal.span {b} :=
  le_antisymm ((Ideal.span_singleton_le_iff_mem _).2 ((mem_span_singleton_OK p K a b).2 h.le))
    ((Ideal.span_singleton_le_iff_mem _).2 ((mem_span_singleton_OK p K b a).2 h.ge))
end ReciprocityTheory.DiscreteGroups.LocalClassField
