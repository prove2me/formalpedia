-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.layer_val_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:40.560991+00:00
-- url     : https://prove2.me/submissions/4e238e51-e7df-40d9-993b-4f60d1edd490

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_multOf_iff_fixed

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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution [(subG p K L).Normal] (h : K ≤ L) (x : (layer p K L).V) : x.1 ∈ multOf p L :=
  (mem_multOf_iff_fixed h x.1).2 fun σ hσ => x.2 ⟨σ, hσ⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
