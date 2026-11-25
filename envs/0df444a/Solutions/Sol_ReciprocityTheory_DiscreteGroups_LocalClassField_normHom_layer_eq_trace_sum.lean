-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_layer_eq_trace_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:26.589932+00:00
-- url     : https://prove2.me/submissions/a5ffbd64-c321-4908-90ff-c8e5febd0b3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution [(subG p K L).Normal] [Fintype (GalLK p K L)] (y : (layer p K L).V) :
    normHom p K L y.1 = (∑ g, (layer p K L).rho g y).1 := by
  refine (normHom_apply (K := K) (L := L) (y.1 : KbarMult p)).trans ?_
  have h1 : (∑ g, (layer p K L).rho g y).1 = ∑ g, ((layer p K L).rho g y).1 :=
    map_sum (Submodule.subtype _) _ _
  refine Eq.trans ?_ h1.symm
  refine Finset.sum_congr rfl fun g _ => ?_
  conv_rhs => rw [← QuotientGroup.out_eq' g]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
