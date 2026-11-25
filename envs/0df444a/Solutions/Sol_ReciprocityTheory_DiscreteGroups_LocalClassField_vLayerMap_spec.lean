-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:41.233918+00:00
-- url     : https://prove2.me/submissions/202952d1-0f34-48a0-87cf-6660f01dcf97

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_layer_val_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vOn_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) [(subG p K L).Normal] (x : (layer p K L).V) :
    (vLayerMap p K L x : ℝ) = eK p L * vbar p x.1 := by
  have hex : ∃ f : (layer p K L).V →+ ℤ, ∀ x, (f x : ℝ) = eK p L * vbar p x.1 :=
    ⟨(vOn p L).comp
      { toFun := fun x => ⟨x.1, layer_val_mem h x⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }, fun x => vOn_spec p L _⟩
  unfold vLayerMap
  rw [dif_pos hex]
  exact hex.choose_spec x
end ReciprocityTheory.DiscreteGroups.LocalClassField
